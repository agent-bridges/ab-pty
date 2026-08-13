package main

// The daemon's side of the relay: it dials out, so a machine with no public
// address is reachable without anybody opening a port or holding a shell on it.
//
// Shape of the thing, and why it is this shape:
//
//   - ONE control connection, kept open, carrying nothing but keepalives and
//     "a client wants you" notifications;
//   - ONE FRESH TCP CONNECTION PER STREAM. No multiplexing, no framing, no flow
//     control. When the relay says OPEN, the daemon dials a new socket, says
//     which ticket it is answering, and hands the raw socket to relay.go's
//     synthetic listener — which serves it with the daemon's real mux and real
//     TLS. Every stream is therefore an ordinary net.Conn all the way down, and
//     a stalled terminal cannot block anybody else's session because there is
//     no shared window to exhaust.
//
// The second choice is the load-bearing one. This protocol has to be
// re-implemented in Kotlin for Android by somebody who will not have this file
// in front of them, and "open a socket, write one line, read one line, start
// TLS" is a page of code with no state machine in it. See docs/RELAY.md.
//
// Security note that must survive future edits: this file never terminates TLS
// and never inspects payload. It obtains byte streams and gives them to
// relayLn.Deliver. Everything about authentication — mandatory client
// certificates, the fingerprint allow-list, the refusal to treat a relay
// connection as loopback — lives in relay.go and mtls.go and applies to these
// streams because they arrive through the same listener. Do not add a shortcut
// that serves a relay stream directly.

import (
	"crypto/tls"
	"database/sql"
	"fmt"
	"log"
	"math/rand"
	"net"
	"os"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"time"
)

const (
	relayAddrEnv  = "AB_PTY_RELAY_ADDR"
	relayLabelEnv = "AB_PTY_RELAY_LABEL"
	relayPinEnv   = "AB_PTY_RELAY_PIN"

	// Wire protocol v1. Kept in lockstep with ab-relay/protocol.go — the two
	// modules are deployed separately, so the strings are duplicated rather
	// than shared, and the version in the magic is what catches a mismatch.
	relayProtoMagic = "AB-RELAY/1"
	relayRoleCtl    = "CONTROL"
	relayRoleData   = "DATA"
	relayMsgOpen    = "OPEN"
	relayMsgPing    = "PING"
	relayMsgPong    = "PONG"
	relayMsgBye     = "BYE"
	relayMaxLine    = 512

	relayDialTimeout   = 20 * time.Second
	relayBackoffBase   = time.Second
	relayBackoffMax    = 60 * time.Second
	relayConfigPoll    = 3 * time.Second
	relayDefaultKeepIv = 30 * time.Second

	// How many streams this daemon will have open through the relay at
	// once. The relay is UNTRUSTED (docs/RELAY.md): OPEN is a line of text
	// from a machine that may have been taken over, and every OPEN costs a
	// goroutine and a fresh outbound socket. Without a ceiling here a
	// compromised VPS empties this daemon's file-descriptor table and its
	// ephemeral port range without holding a single credential for any
	// session — the relay would be controlling the daemon, which is exactly
	// what the threat model says it must not be able to do.
	//
	// The default matches ab-relay's own -max-streams default, so a
	// well-behaved relay never reaches it: the relay refuses the client
	// before the daemon has to. Raise both together if a machine really
	// needs more concurrent streams.
	relayDefaultMaxStreams = 32
	relayMaxStreamsEnv     = "AB_PTY_RELAY_MAX_STREAMS"

	// A relay that keeps asking for streams the daemon has already refused
	// is either broken or hostile, and there is no useful difference: in
	// both cases the right answer is to hang up and come back on the
	// backoff schedule, which costs the relay far more than it costs us.
	relayOpenFloodWindow = time.Minute
	relayOpenFloodBurst  = 128
)

// relayMaxStreams is the concurrency ceiling for relay-initiated streams.
func relayMaxStreams() int {
	if v := strings.TrimSpace(os.Getenv(relayMaxStreamsEnv)); v != "" {
		if n, err := strconv.Atoi(v); err == nil && n > 0 {
			return n
		}
	}
	return relayDefaultMaxStreams
}

// --- persisted state -------------------------------------------------------

// RelayConfig is the single row of relay_config, plus the fields the manager
// writes back so `ab-pty relay status` can answer without the daemon.
type RelayConfig struct {
	Enabled     bool   `json:"enabled"`
	Address     string `json:"address"`
	Label       string `json:"label"`
	Pin         string `json:"relay_fingerprint,omitempty"`
	LastSuccess string `json:"last_success,omitempty"`
	LastError   string `json:"last_error,omitempty"`
	State       string `json:"state"`
}

// initRelayTable is called from initDB. The table is created in every mode so
// that `ab-pty relay status` answers on an untouched install, exactly like
// tls_clients.
func initRelayTable() {
	if _, err := db.Exec(`
		CREATE TABLE IF NOT EXISTS relay_config (
			id           INTEGER PRIMARY KEY CHECK (id = 1),
			enabled      INTEGER NOT NULL DEFAULT 0,
			address      TEXT    NOT NULL DEFAULT '',
			label        TEXT    NOT NULL DEFAULT '',
			pin          TEXT    NOT NULL DEFAULT '',
			last_success DATETIME,
			last_error   TEXT    NOT NULL DEFAULT '',
			state        TEXT    NOT NULL DEFAULT 'disconnected',
			updated_at   DATETIME DEFAULT CURRENT_TIMESTAMP
		)
	`); err != nil {
		log.Fatal(err)
	}
}

func loadRelayConfig() RelayConfig {
	var c RelayConfig
	if db == nil {
		return c
	}
	var enabled int
	var lastSuccess sql.NullString
	err := db.QueryRow(`SELECT enabled, address, label, pin, COALESCE(last_success,''), last_error, state
	                    FROM relay_config WHERE id = 1`).
		Scan(&enabled, &c.Address, &c.Label, &c.Pin, &lastSuccess, &c.LastError, &c.State)
	if err != nil {
		return c
	}
	c.Enabled = enabled != 0
	c.LastSuccess = lastSuccess.String

	// The environment wins over the database so that a container or a unit
	// file can pin the relay without anyone shelling in to run a command.
	if addr := strings.TrimSpace(os.Getenv(relayAddrEnv)); addr != "" {
		c.Address = addr
		c.Enabled = true
	}
	if l := strings.TrimSpace(os.Getenv(relayLabelEnv)); l != "" {
		c.Label = l
	}
	if p := strings.TrimSpace(os.Getenv(relayPinEnv)); p != "" {
		c.Pin = p
	}
	if c.Address == "" {
		c.Enabled = false
	}
	return c
}

func saveRelayConfig(enabled bool, address, label, pin string) error {
	e := 0
	if enabled {
		e = 1
	}
	_, err := db.Exec(`
		INSERT INTO relay_config (id, enabled, address, label, pin, updated_at)
		VALUES (1, ?, ?, ?, ?, CURRENT_TIMESTAMP)
		ON CONFLICT(id) DO UPDATE SET
			enabled = excluded.enabled,
			address = excluded.address,
			label   = excluded.label,
			pin     = excluded.pin,
			updated_at = CURRENT_TIMESTAMP`,
		e, address, label, pin)
	return err
}

func setRelayState(state, lastErr string, success bool) {
	if db == nil {
		return
	}
	if success {
		_, _ = db.Exec(`UPDATE relay_config SET state = ?, last_error = ?, last_success = CURRENT_TIMESTAMP WHERE id = 1`, state, lastErr)
		return
	}
	_, _ = db.Exec(`UPDATE relay_config SET state = ?, last_error = ? WHERE id = 1`, state, lastErr)
}

// relayConfiguredEnabled reports whether the persisted configuration (or the
// environment) asks for the relay. Read after initDB, because the answer lives
// in SQLite.
func relayConfiguredEnabled() bool {
	c := loadRelayConfig()
	return c.Enabled && c.Address != ""
}

// --- backoff ---------------------------------------------------------------

// relayBackoff returns how long to wait before reconnect attempt n (0-based).
//
// The jitter is not a nicety. Every daemon that was attached to a relay
// notices the same restart within a second of every other one, so a
// deterministic backoff makes all of them retry in lockstep forever: the relay
// comes up, takes N simultaneous handshakes, and the ones it sheds retry
// together again. Spreading each wait over [w/2, w) turns a thundering herd
// into an arrival process. rnd is the caller's random in [0,1) so the schedule
// is testable.
func relayBackoff(attempt int, rnd float64) time.Duration {
	w := relayBackoffBase
	for i := 0; i < attempt && w < relayBackoffMax; i++ {
		w *= 2
	}
	if w > relayBackoffMax {
		w = relayBackoffMax
	}
	half := w / 2
	return half + time.Duration(rnd*float64(half))
}

// --- manager ---------------------------------------------------------------

// relayManager keeps at most one control session alive and follows changes to
// the persisted configuration, so `ab-pty relay connect` and
// `ab-pty relay disconnect` take effect without restarting the daemon.
type relayManager struct {
	ln *relayListener

	mu     sync.Mutex
	cur    RelayConfig
	cancel chan struct{}

	// inFlight counts streams opened on the relay's orders and not yet
	// finished. It lives on the manager rather than on one control session
	// on purpose: a hostile relay that gets hung up on reconnects, and the
	// sockets from the previous session are still ours to pay for until
	// they time out, so the ceiling has to span sessions.
	inFlight atomic.Int64
}

// acquireStream takes one of the stream slots, or reports that they are all
// taken. A compare-and-swap, not a read followed by an increment: OPEN lines
// arrive as fast as the relay can write them, and a check that is not part of
// the same atomic step is not a limit.
func (m *relayManager) acquireStream(max int) bool {
	for {
		cur := m.inFlight.Load()
		if int(cur) >= max {
			return false
		}
		if m.inFlight.CompareAndSwap(cur, cur+1) {
			return true
		}
	}
}

func (m *relayManager) releaseStream() { m.inFlight.Add(-1) }

// streamsInFlight is for tests and diagnostics.
func (m *relayManager) streamsInFlight() int { return int(m.inFlight.Load()) }

var relayMgr *relayManager

func startRelayManager(ln *relayListener) {
	m := &relayManager{ln: ln}
	relayMgr = m
	go m.loop()
}

func (m *relayManager) loop() {
	for {
		cfg := loadRelayConfig()
		m.mu.Lock()
		changed := cfg.Address != m.cur.Address || cfg.Enabled != m.cur.Enabled ||
			cfg.Label != m.cur.Label || cfg.Pin != m.cur.Pin
		if changed {
			if m.cancel != nil {
				close(m.cancel)
				m.cancel = nil
			}
			m.cur = cfg
			if cfg.Enabled && cfg.Address != "" {
				stop := make(chan struct{})
				m.cancel = stop
				go m.session(cfg, stop)
			} else {
				setRelayState("disconnected", "", false)
				log.Printf("relay: disabled")
			}
		}
		m.mu.Unlock()
		time.Sleep(relayConfigPoll)
	}
}

// session is the reconnect loop for one configuration.
func (m *relayManager) session(cfg RelayConfig, stop <-chan struct{}) {
	rnd := rand.New(rand.NewSource(time.Now().UnixNano() ^ int64(os.Getpid())))
	attempt := 0
	for {
		select {
		case <-stop:
			return
		default:
		}

		err := m.connectOnce(cfg, stop)
		select {
		case <-stop:
			return
		default:
		}
		if err != nil {
			setRelayState("reconnecting", err.Error(), false)
			log.Printf("relay: %v", err)
		} else {
			setRelayState("reconnecting", "control connection closed", false)
			log.Printf("relay: control connection to %s closed", cfg.Address)
			attempt = 0 // a session that actually worked starts over
		}
		d := relayBackoff(attempt, rnd.Float64())
		attempt++
		log.Printf("relay: reconnecting to %s in %s", cfg.Address, d.Truncate(10*time.Millisecond))
		select {
		case <-stop:
			return
		case <-time.After(d):
		}
	}
}

// connectOnce runs one control session to completion. Returns nil if the
// session was established and then ended, an error if it never got that far.
func (m *relayManager) connectOnce(cfg RelayConfig, stop <-chan struct{}) error {
	// The daemon authenticates to the relay with its OWN SERVER certificate,
	// presented as a client certificate. That is what makes the identity the
	// relay proves equal to the identity a phone pins from /info's
	// tls_server_fingerprint: one keypair, one identity, nothing to keep in
	// sync.
	cert, err := tls.LoadX509KeyPair(tlsCertPath(), tlsKeyPath())
	if err != nil {
		return fmt.Errorf("loading the daemon keypair for the relay (%s): %w — run `ab-pty tls init`", tlsCertPath(), err)
	}

	tlsCfg := &tls.Config{
		Certificates: []tls.Certificate{cert},
		MinVersion:   tls.VersionTLS12,
		// The relay's own certificate is not a trust anchor for anything:
		// the payload riding through it is a second, independent TLS
		// session terminated inside this daemon, so a relay that lies
		// about its identity still cannot read or forge a byte. Verifying
		// it is offered as an option (a pin) purely to deny an on-path
		// attacker the metadata.
		InsecureSkipVerify: true,
	}
	if pin := strings.TrimSpace(cfg.Pin); pin != "" {
		want, perr := normalizeFingerprint(pin)
		if perr != nil {
			return fmt.Errorf("relay pin: %w", perr)
		}
		tlsCfg.VerifyConnection = func(cs tls.ConnectionState) error {
			if len(cs.PeerCertificates) == 0 {
				return fmt.Errorf("relay presented no certificate")
			}
			got := certFingerprint(cs.PeerCertificates[0].Raw)
			if got != want {
				return fmt.Errorf("relay certificate %s does not match the pin %s", got, want)
			}
			return nil
		}
	}

	d := &net.Dialer{Timeout: relayDialTimeout}
	conn, err := tls.DialWithDialer(d, "tcp", cfg.Address, tlsCfg)
	if err != nil {
		return fmt.Errorf("dialing relay %s: %w", cfg.Address, err)
	}
	defer conn.Close()

	label := cfg.Label
	if label == "" {
		label, _ = os.Hostname()
	}
	_ = conn.SetDeadline(time.Now().Add(relayDialTimeout))
	if _, err := fmt.Fprintf(conn, "%s %s label=%s version=%s\n", relayProtoMagic, relayRoleCtl, sanitizeToken(label), Version); err != nil {
		return fmt.Errorf("greeting relay %s: %w", cfg.Address, err)
	}
	line, err := relayReadLine(conn, relayMaxLine)
	if err != nil {
		return fmt.Errorf("reading relay greeting from %s: %w", cfg.Address, err)
	}
	fields := strings.Fields(line)
	if len(fields) < 2 || fields[0] != relayProtoMagic || strings.ToUpper(fields[1]) != "OK" {
		return fmt.Errorf("relay %s refused the control connection: %s", cfg.Address, line)
	}
	keepalive := relayDefaultKeepIv
	name := ""
	for _, f := range fields[2:] {
		k, v, ok := strings.Cut(f, "=")
		if !ok {
			continue
		}
		switch k {
		case "keepalive":
			if n, e := strconv.Atoi(v); e == nil && n > 0 {
				keepalive = time.Duration(n) * time.Second
			}
		case "name":
			name = v
		}
	}
	_ = conn.SetDeadline(time.Time{})
	setRelayState("connected", "", true)
	log.Printf("relay: connected to %s as %q (keepalive %s)", cfg.Address, name, keepalive)
	defer setRelayState("disconnected", "", false)

	// A dead control channel is indistinguishable from an idle one until
	// something is written, and NAT boxes forget mappings in minutes. The
	// relay pings; three missed pings and we tear down and reconnect rather
	// than sit on a socket that no longer goes anywhere.
	readTimeout := 3 * keepalive

	done := make(chan struct{})
	defer close(done)
	go func() {
		select {
		case <-stop:
			_ = conn.Close()
		case <-done:
		}
	}()

	maxStreams := relayMaxStreams()
	dropped := 0
	windowStart := time.Now()

	for {
		_ = conn.SetReadDeadline(time.Now().Add(readTimeout))
		line, err := relayReadLine(conn, relayMaxLine)
		if err != nil {
			return nil // established, then ended: a normal reconnect
		}
		verb, arg := relaySplit(line)
		switch verb {
		case relayMsgOpen:
			// Refuse rather than queue. A dropped OPEN costs the
			// client on the other end one `timeout` error and a
			// retry; a queued one costs this machine a socket it
			// did not agree to spend, and the queue is written by
			// the untrusted side.
			if !m.acquireStream(maxStreams) {
				now := time.Now()
				if now.Sub(windowStart) > relayOpenFloodWindow {
					windowStart, dropped = now, 0
				}
				dropped++
				if dropped == 1 || dropped%32 == 0 {
					log.Printf("relay: %s asked for a stream past the limit of %d (%d refused); dropping the request",
						cfg.Address, maxStreams, dropped)
				}
				if dropped >= relayOpenFloodBurst {
					return fmt.Errorf("relay %s pushed %d stream requests past the limit of %d in %s: hanging up",
						cfg.Address, dropped, maxStreams, time.Since(windowStart).Truncate(time.Millisecond))
				}
				continue
			}
			go func(ticket string) {
				defer m.releaseStream()
				m.openStream(cfg, ticket)
			}(arg)
		case relayMsgPing:
			_ = conn.SetWriteDeadline(time.Now().Add(10 * time.Second))
			if _, err := fmt.Fprintf(conn, "%s %s\n", relayMsgPong, arg); err != nil {
				return nil
			}
			_ = conn.SetWriteDeadline(time.Time{})
		case relayMsgPong:
		case relayMsgBye:
			log.Printf("relay: %s said BYE: %s", cfg.Address, arg)
			return nil
		}
	}
}

// openStream answers an OPEN by dialling a fresh connection to the relay and
// handing it, raw, to the synthetic listener.
//
// The stream is deliberately NOT wrapped in TLS here: relay.go's listener is
// already behind tls.NewListener with a required-client-certificate config, so
// the handshake that happens on this socket is between the remote client and
// this daemon, and the relay in the middle sees ciphertext only.
func (m *relayManager) openStream(cfg RelayConfig, ticket string) {
	if m.ln == nil {
		return
	}
	conn, err := net.DialTimeout("tcp", cfg.Address, relayDialTimeout)
	if err != nil {
		log.Printf("relay: opening a stream to %s: %v", cfg.Address, err)
		return
	}
	_ = conn.SetDeadline(time.Now().Add(relayDialTimeout))
	if _, err := fmt.Fprintf(conn, "%s %s %s\n", relayProtoMagic, relayRoleData, ticket); err != nil {
		conn.Close()
		return
	}
	line, err := relayReadLine(conn, relayMaxLine)
	if err != nil {
		conn.Close()
		return
	}
	fields := strings.Fields(line)
	if len(fields) < 2 || fields[0] != relayProtoMagic || strings.ToUpper(fields[1]) != "OK" {
		log.Printf("relay: stream refused: %s", line)
		conn.Close()
		return
	}
	_ = conn.SetDeadline(time.Time{})
	if err := m.ln.Deliver(conn); err != nil {
		conn.Close()
	}
}

// --- small wire helpers ----------------------------------------------------

// relayReadLine reads a \n-terminated line one byte at a time.
//
// One byte at a time is not an oversight. The very next bytes on this socket
// belong to a TLS handshake that this code must not touch; a bufio.Reader would
// pull them into a buffer that is then dropped on the floor, and the resulting
// hang is extremely hard to see. Reimplementations in other languages have to
// do the same — it is called out in docs/RELAY.md.
func relayReadLine(c net.Conn, max int) (string, error) {
	buf := make([]byte, 0, 64)
	one := make([]byte, 1)
	for {
		n, err := c.Read(one)
		if n == 1 {
			if one[0] == '\n' {
				return strings.TrimRight(string(buf), "\r"), nil
			}
			buf = append(buf, one[0])
			if len(buf) > max {
				return "", fmt.Errorf("relay line exceeds %d bytes", max)
			}
			continue
		}
		if err != nil {
			return "", err
		}
	}
}

func relaySplit(line string) (verb, arg string) {
	f := strings.Fields(line)
	if len(f) == 0 {
		return "", ""
	}
	if len(f) == 1 {
		return strings.ToUpper(f[0]), ""
	}
	return strings.ToUpper(f[0]), f[1]
}

// sanitizeToken keeps a value safe to put in a space-separated key=value line.
func sanitizeToken(s string) string {
	s = strings.TrimSpace(s)
	var b strings.Builder
	for _, r := range s {
		if r <= ' ' || r == '=' || r > '~' {
			b.WriteByte('-')
			continue
		}
		b.WriteRune(r)
	}
	out := b.String()
	if len(out) > 64 {
		out = out[:64]
	}
	if out == "" {
		out = "ab-pty"
	}
	return out
}

// --- subcommands -----------------------------------------------------------

const relayUsage = `ab-pty relay — reach this daemon through a relay, from anywhere

  ab-pty relay connect <host:port> [-label NAME] [-pin SHA256]
        Dial out to a relay and stay connected. Takes effect immediately: a
        running daemon picks the change up within a few seconds, and a stopped
        one starts connected. The relay must already know this daemon's
        certificate fingerprint:

            ab-pty tls fingerprint          # on this machine
            ab-relay agent add <name> <fp>  # on the relay

  ab-pty relay status
        Show the configured relay, this daemon's identifier and the last
        success / last error recorded by the connection loop.

  ab-pty relay disconnect
        Stop using the relay. The LAN listener is unaffected.

  ab-pty relay id
        Print this daemon's relay identifier: the SHA-256 of its server
        certificate. Same value as /info's tls_server_fingerprint, and the same
        value a client pins — a relay cannot join a client to the wrong machine
        without the client's TLS handshake failing.

Environment (overrides the stored configuration; for containers and unit files):
  AB_PTY_RELAY_ENABLED=1     serve the relay listener
  AB_PTY_RELAY_ADDR          relay address host:port
  AB_PTY_RELAY_LABEL         label reported to the relay
  AB_PTY_RELAY_PIN           expected SHA-256 of the relay's own certificate
  AB_PTY_RELAY_MAX_STREAMS   concurrent streams the relay may ask for (default 32).
                             The relay is untrusted: past this the daemon drops
                             OPEN requests, and a relay that keeps pushing has
                             its control channel hung up on.
`

func runRelay(args []string) {
	if len(args) == 0 || args[0] == "-h" || args[0] == "--help" || args[0] == "help" {
		fmt.Print(relayUsage)
		return
	}
	initDB()
	switch args[0] {
	case "connect":
		runRelayConnect(args[1:])
	case "status":
		runRelayStatus()
	case "disconnect":
		cur := loadRelayConfig()
		if err := saveRelayConfig(false, cur.Address, cur.Label, cur.Pin); err != nil {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
			os.Exit(1)
		}
		setRelayState("disconnected", "", false)
		fmt.Println("Relay disabled. A running daemon drops the connection within a few seconds.")
	case "id":
		fp, err := serverCertFingerprintFromDisk()
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error: %v — run `ab-pty tls init` first\n", err)
			os.Exit(1)
		}
		fmt.Println(fp)
	default:
		fmt.Fprintf(os.Stderr, "unknown relay subcommand: %s\n\n", args[0])
		fmt.Print(relayUsage)
		os.Exit(2)
	}
}

func runRelayConnect(args []string) {
	label, pin := "", ""
	var addr string
	for i := 0; i < len(args); i++ {
		switch args[i] {
		case "-label", "--label":
			if i+1 < len(args) {
				i++
				label = args[i]
			}
		case "-pin", "--pin":
			if i+1 < len(args) {
				i++
				pin = args[i]
			}
		default:
			if addr == "" {
				addr = args[i]
			}
		}
	}
	if addr == "" {
		fmt.Fprintln(os.Stderr, "usage: ab-pty relay connect <host:port> [-label NAME] [-pin SHA256]")
		os.Exit(2)
	}
	if _, _, err := net.SplitHostPort(addr); err != nil {
		fmt.Fprintf(os.Stderr, "Error: %q is not host:port\n", addr)
		os.Exit(2)
	}
	if pin != "" {
		norm, err := normalizeFingerprint(pin)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
			os.Exit(1)
		}
		pin = norm
	}
	if err := saveRelayConfig(true, addr, label, pin); err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}
	fp, ferr := serverCertFingerprintFromDisk()
	fmt.Printf("Relay set to %s\n", addr)
	if ferr == nil {
		fmt.Printf("This daemon's relay id: %s\n", fp)
		fmt.Printf("Register it on the relay: ab-relay agent add <name> %s\n", fp)
	} else {
		fmt.Printf("WARNING: no server certificate yet (%v) — run `ab-pty tls init`\n", ferr)
	}
	if !relayEnabled() {
		fmt.Printf("Start the daemon with %s=1 for the relay listener to exist.\n", relayEnabledEnv)
	}
}

func runRelayStatus() {
	c := loadRelayConfig()
	fp, ferr := serverCertFingerprintFromDisk()
	fmt.Printf("enabled:      %v\n", c.Enabled)
	fmt.Printf("address:      %s\n", orDash(c.Address))
	fmt.Printf("label:        %s\n", orDash(c.Label))
	if c.Pin != "" {
		fmt.Printf("relay pin:    %s\n", prettyFingerprint(c.Pin))
	}
	fmt.Printf("state:        %s\n", orDash(c.State))
	fmt.Printf("last success: %s\n", orDash(c.LastSuccess))
	fmt.Printf("last error:   %s\n", orDash(c.LastError))
	if ferr == nil {
		fmt.Printf("relay id:     %s\n", fp)
	} else {
		fmt.Printf("relay id:     unavailable (%v)\n", ferr)
	}
	fmt.Printf("listener:     %s=%v\n", relayEnabledEnv, relayEnabled())
}

func orDash(s string) string {
	if strings.TrimSpace(s) == "" {
		return "-"
	}
	return s
}
