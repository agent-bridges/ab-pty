package main

// The daemon's side of the relay: it dials out, so a machine with no public
// address is reachable without anybody opening a port or holding a shell on it.
//
// Shape of the thing, and why it is this shape:
//
//   - ONE control connection PER CONFIGURED RELAY, kept open, carrying nothing
//     but keepalives and
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

	// Bounds on the keepalive the relay announces. The value decides how
	// long this daemon will sit on a channel that has stopped carrying
	// anything (the read timeout is three times it), so an unbounded value
	// from an untrusted peer means "never notice you are cut off, never
	// reconnect" — a one-line way for a relay to strand a machine.
	relayMinKeepIv = time.Second
	relayMaxKeepIv = 5 * time.Minute
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

// clampRelayKeepalive turns the relay's announced keepalive into one this
// daemon is willing to live with. Anything outside the bounds is clamped
// rather than refused: the relay's owner may legitimately want a different
// period, they just do not get to choose "infinite".
func clampRelayKeepalive(seconds int) time.Duration {
	if seconds <= 0 {
		return relayDefaultKeepIv
	}
	d := time.Duration(seconds) * time.Second
	if seconds > int(relayMaxKeepIv/time.Second) || d <= 0 { // d <= 0 catches overflow
		return relayMaxKeepIv
	}
	if d < relayMinKeepIv {
		return relayMinKeepIv
	}
	return d
}

// --- persisted state -------------------------------------------------------

// RelayConfig is one named relay route, plus the fields the manager writes back
// so `ab-pty relay status` can answer without the daemon.
type RelayConfig struct {
	Name        string `json:"name"`
	Enabled     bool   `json:"enabled"`
	Address     string `json:"address"`
	Label       string `json:"label"`
	Pin         string `json:"relay_fingerprint,omitempty"`
	LastSuccess string `json:"last_success,omitempty"`
	LastError   string `json:"last_error,omitempty"`
	State       string `json:"state"`
	runID       uint64
}

// initRelayTable is called from initDB. It also performs the one-way migration
// from the original singleton relay_config table. The old row becomes the
// named route "default", preserving the existing address, label, pin and
// connection diagnostics.
func initRelayTable() {
	tx, err := db.Begin()
	if err != nil {
		log.Fatal(err)
	}
	rollback := func(err error) {
		_ = tx.Rollback()
		log.Fatal(err)
	}
	if _, err := tx.Exec(`
		CREATE TABLE IF NOT EXISTS relay_configs (
			name         TEXT PRIMARY KEY,
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
		rollback(err)
	}
	if _, err := tx.Exec(`
		CREATE TABLE IF NOT EXISTS relay_environment_state (
			address      TEXT PRIMARY KEY,
			last_success DATETIME,
			last_error   TEXT NOT NULL DEFAULT '',
			state        TEXT NOT NULL DEFAULT 'disconnected'
		)
	`); err != nil {
		rollback(err)
	}

	var legacyExists int
	if err := tx.QueryRow(`SELECT COUNT(*) FROM sqlite_master WHERE type='table' AND name='relay_config'`).Scan(&legacyExists); err != nil {
		rollback(err)
	}

	type storedAddress struct{ name, address, normalized string }
	rows, err := tx.Query(`SELECT name, address FROM relay_configs ORDER BY name`)
	if err != nil {
		rollback(err)
	}
	var stored []storedAddress
	needsCanonicalization := legacyExists != 0
	for rows.Next() {
		var item storedAddress
		if err := rows.Scan(&item.name, &item.address); err != nil {
			_ = rows.Close()
			rollback(err)
		}
		item.normalized, err = normalizeRelayAddress(item.address)
		if err != nil {
			// Retain an invalid legacy value so status can explain it and the
			// reconnect loop can report the dial error; new CLI writes cannot
			// create one.
			item.normalized = strings.TrimSpace(item.address)
		}
		if item.normalized != item.address {
			needsCanonicalization = true
		}
		stored = append(stored, item)
	}
	if err := rows.Close(); err != nil {
		rollback(err)
	}
	if needsCanonicalization {
		// Drop/recreate only while actually canonicalising. Doing this on every
		// CLI invocation needlessly takes a write lock from the running daemon.
		if _, err := tx.Exec(`DROP INDEX IF EXISTS relay_configs_address_idx`); err != nil {
			rollback(err)
		}
	}

	if legacyExists != 0 {
		var c RelayConfig
		var enabled int
		var lastSuccess sql.NullString
		var updatedAt sql.NullString
		err := tx.QueryRow(`SELECT enabled, address, label, pin, last_success, last_error, state, updated_at
		                    FROM relay_config WHERE id = 1`).
			Scan(&enabled, &c.Address, &c.Label, &c.Pin, &lastSuccess, &c.LastError, &c.State, &updatedAt)
		if err != nil && err != sql.ErrNoRows {
			rollback(err)
		}
		if err == nil {
			if normalized, nerr := normalizeRelayAddress(c.Address); nerr == nil {
				c.Address = normalized
			} else {
				c.Address = strings.TrimSpace(c.Address)
			}
			if _, err := tx.Exec(`
				INSERT OR IGNORE INTO relay_configs
					(name, enabled, address, label, pin, last_success, last_error, state, updated_at)
				VALUES ('default', ?, ?, ?, ?, ?, ?, ?, ?)
			`, enabled, c.Address, c.Label, c.Pin, lastSuccess, c.LastError, c.State, updatedAt); err != nil {
				rollback(err)
			}
		}
		if _, err := tx.Exec(`DROP TABLE relay_config`); err != nil {
			rollback(err)
		}
	}
	for _, item := range stored {
		if item.normalized == item.address {
			continue
		}
		if _, err := tx.Exec(`UPDATE relay_configs SET address = ? WHERE name = ?`, item.normalized, item.name); err != nil {
			rollback(err)
		}
	}
	if _, err := tx.Exec(`CREATE UNIQUE INDEX IF NOT EXISTS relay_configs_address_idx ON relay_configs(address)`); err != nil {
		rollback(fmt.Errorf("relay routes contain duplicate canonical addresses: %w", err))
	}
	if err := tx.Commit(); err != nil {
		log.Fatal(err)
	}
}

func loadRelayConfigs() []RelayConfig {
	if db == nil {
		return nil
	}

	// The singular environment configuration retains its old declarative
	// semantics: when present it replaces the stored routes. Multi-relay units
	// should persist routes with `relay connect -name ...` instead.
	if addr := strings.TrimSpace(os.Getenv(relayAddrEnv)); addr != "" {
		if normalized, err := normalizeRelayAddress(addr); err == nil {
			addr = normalized
		}
		c := RelayConfig{
			Name:    "environment",
			Enabled: true,
			Address: addr,
			Label:   strings.TrimSpace(os.Getenv(relayLabelEnv)),
			Pin:     strings.TrimSpace(os.Getenv(relayPinEnv)),
			State:   "configured",
		}
		var lastSuccess sql.NullString
		if err := db.QueryRow(`SELECT COALESCE(last_success,''), last_error, state
		                       FROM relay_environment_state WHERE address = ?`, addr).
			Scan(&lastSuccess, &c.LastError, &c.State); err == nil {
			c.LastSuccess = lastSuccess.String
		} else if err != sql.ErrNoRows {
			log.Printf("relay: reading environment state: %v", err)
		}
		return []RelayConfig{c}
	}

	rows, err := db.Query(`SELECT name, enabled, address, label, pin, COALESCE(last_success,''), last_error, state
	                       FROM relay_configs ORDER BY name`)
	if err != nil {
		log.Printf("relay: reading relay_configs: %v", err)
		return nil
	}
	defer rows.Close()
	var configs []RelayConfig
	for rows.Next() {
		var c RelayConfig
		var enabled int
		var lastSuccess sql.NullString
		if err := rows.Scan(&c.Name, &enabled, &c.Address, &c.Label, &c.Pin, &lastSuccess, &c.LastError, &c.State); err != nil {
			log.Printf("relay: reading relay_configs row: %v", err)
			continue
		}
		c.Enabled = enabled != 0 && c.Address != ""
		c.LastSuccess = lastSuccess.String
		configs = append(configs, c)
	}
	return configs
}

func saveRelayConfig(c RelayConfig) error {
	e := 0
	if c.Enabled {
		e = 1
	}
	_, err := db.Exec(`
		INSERT INTO relay_configs (name, enabled, address, label, pin, updated_at)
		VALUES (?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
		ON CONFLICT(name) DO UPDATE SET
			enabled = excluded.enabled,
			address = excluded.address,
			label   = excluded.label,
			pin     = excluded.pin,
			updated_at = CURRENT_TIMESTAMP`,
		c.Name, e, c.Address, c.Label, c.Pin)
	return err
}

func renameRelayConfig(oldName, newName string) error {
	_, err := db.Exec(`UPDATE relay_configs SET name = ?, updated_at = CURRENT_TIMESTAMP WHERE name = ?`, newName, oldName)
	return err
}

// saveRelayConfigReplacing performs an operator-facing rename and its config
// update as one transaction. The polling manager can therefore see either the
// old complete route or the new complete route, never a half-renamed one.
func saveRelayConfigReplacing(c RelayConfig, oldName string) error {
	tx, err := db.Begin()
	if err != nil {
		return err
	}
	if oldName != "" && oldName != c.Name {
		if _, err := tx.Exec(`UPDATE relay_configs SET name = ? WHERE name = ?`, c.Name, oldName); err != nil {
			_ = tx.Rollback()
			return err
		}
	}
	e := 0
	if c.Enabled {
		e = 1
	}
	if _, err := tx.Exec(`
		INSERT INTO relay_configs (name, enabled, address, label, pin, updated_at)
		VALUES (?, ?, ?, ?, ?, CURRENT_TIMESTAMP)
		ON CONFLICT(name) DO UPDATE SET
			enabled = excluded.enabled,
			address = excluded.address,
			label   = excluded.label,
			pin     = excluded.pin,
			updated_at = CURRENT_TIMESTAMP`,
		c.Name, e, c.Address, c.Label, c.Pin); err != nil {
		_ = tx.Rollback()
		return err
	}
	return tx.Commit()
}

func saveValidatedRelayConfig(c RelayConfig, oldName string) error {
	if strings.TrimSpace(c.Pin) != "" {
		normalized, err := normalizeFingerprint(c.Pin)
		if err != nil {
			return err
		}
		c.Pin = normalized
	}
	return saveRelayConfigReplacing(c, oldName)
}

func setRelayState(name, address, state, lastErr string, success bool) {
	if db == nil {
		return
	}
	if name == "environment" {
		if success {
			_, _ = db.Exec(`
				INSERT INTO relay_environment_state (address, state, last_error, last_success)
				VALUES (?, ?, ?, CURRENT_TIMESTAMP)
				ON CONFLICT(address) DO UPDATE SET state=excluded.state, last_error=excluded.last_error,
					last_success=CURRENT_TIMESTAMP`, address, state, lastErr)
			return
		}
		_, _ = db.Exec(`
			INSERT INTO relay_environment_state (address, state, last_error)
			VALUES (?, ?, ?)
			ON CONFLICT(address) DO UPDATE SET state=excluded.state, last_error=excluded.last_error`,
			address, state, lastErr)
		return
	}
	if success {
		_, _ = db.Exec(`UPDATE relay_configs SET state = ?, last_error = ?, last_success = CURRENT_TIMESTAMP WHERE name = ?`, state, lastErr, name)
		return
	}
	_, _ = db.Exec(`UPDATE relay_configs SET state = ?, last_error = ? WHERE name = ?`, state, lastErr, name)
}

// relayConfiguredEnabled reports whether the persisted configuration (or the
// environment) asks for the relay. Read after initDB, because the answer lives
// in SQLite.
func relayConfiguredEnabled() bool {
	for _, c := range loadRelayConfigs() {
		if c.Enabled && c.Address != "" {
			return true
		}
	}
	return false
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

// relayManager keeps one independent control session alive for every enabled
// relay route. Adding, changing or disabling one route does not disturb any of
// the others.
type relayManager struct {
	ln *relayListener

	mu      sync.Mutex
	runs    map[string]*relayRun
	nextRun uint64
	stop    chan struct{}
	done    chan struct{}
	stopOne sync.Once
	wg      sync.WaitGroup

	// inFlight counts streams opened on the relay's orders and not yet
	// finished. It lives on the manager rather than on one control session
	// on purpose: a hostile relay that gets hung up on reconnects, and the
	// sockets from the previous session are still ours to pay for until
	// they time out, so the ceiling has to span sessions.
	inFlight atomic.Int64

	// keepAliveNs is the interval last agreed with the relay, after
	// clamping. Exported through this field only so tests can see what the
	// daemon actually accepted.
	keepAliveNs atomic.Int64
}

type relayRun struct {
	cfg    RelayConfig
	cancel chan struct{}
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

func (m *relayManager) keepalive() time.Duration { return time.Duration(m.keepAliveNs.Load()) }

var relayMgr *relayManager

func startRelayManager(ln *relayListener) {
	m := &relayManager{
		ln:   ln,
		runs: make(map[string]*relayRun),
		stop: make(chan struct{}),
		done: make(chan struct{}),
	}
	relayMgr = m
	go func() {
		m.loop(m.stop)
		m.wg.Wait()
		close(m.done)
	}()
}

func stopRelayManager() {
	if relayMgr == nil || relayMgr.stop == nil {
		return
	}
	relayMgr.stopOne.Do(func() { close(relayMgr.stop) })
	<-relayMgr.done
}

func sameRelayConfig(a, b RelayConfig) bool {
	return a.Name == b.Name && a.Enabled == b.Enabled && a.Address == b.Address &&
		a.Label == b.Label && a.Pin == b.Pin
}

func (m *relayManager) loop(stop <-chan struct{}) {
	for {
		configs := loadRelayConfigs()
		desired := make(map[string]RelayConfig, len(configs))
		for _, cfg := range configs {
			if cfg.Enabled && cfg.Address != "" {
				desired[cfg.Name] = cfg
			}
		}

		m.mu.Lock()
		if m.runs == nil {
			m.runs = make(map[string]*relayRun)
		}
		for name, run := range m.runs {
			cfg, exists := desired[name]
			if !exists || !sameRelayConfig(cfg, run.cfg) {
				close(run.cancel)
				delete(m.runs, name)
			}
		}
		for name, cfg := range desired {
			if _, exists := m.runs[name]; exists {
				continue
			}
			cancel := make(chan struct{})
			m.nextRun++
			cfg.runID = m.nextRun
			m.runs[name] = &relayRun{cfg: cfg, cancel: cancel}
			m.wg.Add(1)
			go func(cfg RelayConfig, cancel chan struct{}) {
				defer m.wg.Done()
				m.session(cfg, cancel)
			}(cfg, cancel)
		}
		m.mu.Unlock()

		select {
		case <-stop:
			m.mu.Lock()
			for name, run := range m.runs {
				close(run.cancel)
				setRelayState(run.cfg.Name, run.cfg.Address, "disconnected", "", false)
				delete(m.runs, name)
			}
			m.mu.Unlock()
			return
		case <-time.After(relayConfigPoll):
		}
	}
}

// setState ignores a write from a canceled generation. Without this guard, a
// slow old connection can report "disconnected" after its replacement has
// already reported "connected" for the same named route.
func (m *relayManager) setState(cfg RelayConfig, state, lastErr string, success bool) {
	if cfg.runID != 0 {
		m.mu.Lock()
		run := m.runs[cfg.Name]
		current := run != nil && run.cfg.runID == cfg.runID
		m.mu.Unlock()
		if !current {
			return
		}
	}
	setRelayState(cfg.Name, cfg.Address, state, lastErr, success)
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
			m.setState(cfg, "reconnecting", err.Error(), false)
			log.Printf("relay %q: %v", cfg.Name, err)
		} else {
			m.setState(cfg, "reconnecting", "control connection closed", false)
			log.Printf("relay %q: control connection to %s closed", cfg.Name, cfg.Address)
			attempt = 0 // a session that actually worked starts over
		}
		d := relayBackoff(attempt, rnd.Float64())
		attempt++
		log.Printf("relay %q: reconnecting to %s in %s", cfg.Name, cfg.Address, d.Truncate(10*time.Millisecond))
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
				keepalive = clampRelayKeepalive(n)
			}
		case "name":
			name = v
		}
	}
	_ = conn.SetDeadline(time.Time{})
	m.keepAliveNs.Store(int64(keepalive))
	m.setState(cfg, "connected", "", true)
	log.Printf("relay %q: connected to %s as %q (keepalive %s)", cfg.Name, cfg.Address, name, keepalive)
	defer m.setState(cfg, "disconnected", "", false)

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

  ab-pty relay connect <host:port> [-name ROUTE] [-label NAME] [-pin SHA256]
        Add or update a relay route and stay connected to it. Repeat with
        different route names (for example "home" and "remote") to keep this
        same daemon online on several relays concurrently. The relay must
        already know this daemon's certificate fingerprint:

            ab-pty tls fingerprint          # on this machine
            ab-relay agent add <name> <fp>  # on the relay

  ab-pty relay status [ROUTE]
        Show every configured relay route (or one named route), this daemon's
        identifier and each connection loop's last success / last error.

  ab-pty relay disconnect [ROUTE|host:port|--all]
        Disable one route. With no argument (or --all), disable every route.
        The LAN listener is unaffected.

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
		runRelayStatus(args[1:])
	case "disconnect":
		runRelayDisconnect(args[1:])
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

func normalizeRelayAddress(addr string) (string, error) {
	host, port, err := net.SplitHostPort(strings.TrimSpace(addr))
	if err != nil || host == "" || port == "" {
		return "", fmt.Errorf("%q is not host:port", addr)
	}
	host = strings.ToLower(strings.TrimSuffix(host, "."))
	if ip := net.ParseIP(host); ip != nil {
		host = ip.String()
	}
	return net.JoinHostPort(host, port), nil
}

func validateRelayName(name string) error {
	if name == "" {
		return fmt.Errorf("relay route name cannot be empty")
	}
	if len(name) > 64 {
		return fmt.Errorf("relay route name is longer than 64 bytes")
	}
	if strings.ContainsAny(name, "\r\n\t") {
		return fmt.Errorf("relay route name cannot contain control characters")
	}
	return nil
}

func relaySelectorMatches(c RelayConfig, selector string) bool {
	if c.Name == selector || c.Address == selector {
		return true
	}
	normalized, err := normalizeRelayAddress(selector)
	return err == nil && c.Address == normalized
}

func runRelayConnect(args []string) {
	label, pin, routeName := "", "", ""
	explicitRouteName := false
	var addr string
	for i := 0; i < len(args); i++ {
		switch args[i] {
		case "-name", "--name":
			if i+1 >= len(args) {
				fmt.Fprintln(os.Stderr, "Error: -name requires a value")
				os.Exit(2)
			}
			i++
			routeName = strings.TrimSpace(args[i])
			explicitRouteName = true
		case "-label", "--label":
			if i+1 >= len(args) {
				fmt.Fprintln(os.Stderr, "Error: -label requires a value")
				os.Exit(2)
			}
			i++
			label = args[i]
		case "-pin", "--pin":
			if i+1 >= len(args) {
				fmt.Fprintln(os.Stderr, "Error: -pin requires a value")
				os.Exit(2)
			}
			i++
			pin = args[i]
		default:
			if addr == "" {
				addr = args[i]
			} else {
				fmt.Fprintf(os.Stderr, "Error: unexpected argument %q\n", args[i])
				os.Exit(2)
			}
		}
	}
	if addr == "" {
		fmt.Fprintln(os.Stderr, "usage: ab-pty relay connect <host:port> [-name ROUTE] [-label NAME] [-pin SHA256]")
		os.Exit(2)
	}
	var err error
	addr, err = normalizeRelayAddress(addr)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(2)
	}
	configs := loadRelayConfigs()
	if strings.TrimSpace(os.Getenv(relayAddrEnv)) != "" {
		fmt.Fprintf(os.Stderr, "Error: %s is set; stored relay routes are suppressed by the environment configuration\n", relayAddrEnv)
		os.Exit(1)
	}
	if routeName == "" {
		for _, c := range configs {
			if c.Address == addr {
				routeName = c.Name
				break
			}
		}
		if routeName == "" {
			routeName = addr
		}
	}
	if err := validateRelayName(routeName); err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(2)
	}
	renameFrom := ""
	for _, c := range configs {
		if c.Address != addr || c.Name == routeName {
			continue
		}
		if !explicitRouteName {
			fmt.Fprintf(os.Stderr, "Error: relay address %s is already configured as route %q\n", addr, c.Name)
			os.Exit(1)
		}
		for _, other := range configs {
			if other.Name == routeName {
				fmt.Fprintf(os.Stderr, "Error: relay route %q already points to %s\n", routeName, other.Address)
				os.Exit(1)
			}
		}
		renameFrom = c.Name
	}
	if err := saveValidatedRelayConfig(
		RelayConfig{Name: routeName, Enabled: true, Address: addr, Label: label, Pin: pin}, renameFrom); err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}
	fp, ferr := serverCertFingerprintFromDisk()
	fmt.Printf("Relay route %q set to %s\n", routeName, addr)
	if ferr == nil {
		fmt.Printf("This daemon's relay id: %s\n", fp)
		fmt.Printf("Register it on the relay: ab-relay agent add <name> %s\n", fp)
	} else {
		fmt.Printf("WARNING: no server certificate yet (%v) — run `ab-pty tls init`\n", ferr)
	}
}

func runRelayStatus(args []string) {
	if len(args) > 1 {
		fmt.Fprintln(os.Stderr, "usage: ab-pty relay status [ROUTE]")
		os.Exit(2)
	}
	configs := loadRelayConfigs()
	if len(args) == 1 {
		selected := configs[:0]
		for _, c := range configs {
			if relaySelectorMatches(c, args[0]) {
				selected = append(selected, c)
			}
		}
		configs = selected
		if len(configs) == 0 {
			fmt.Fprintf(os.Stderr, "Error: relay route %q not found\n", args[0])
			os.Exit(1)
		}
	}
	fp, ferr := serverCertFingerprintFromDisk()
	enabled := false
	for _, c := range configs {
		enabled = enabled || c.Enabled
	}
	// Keep the first line parseable for scripts written for the singleton
	// status output. It now means "at least one route is enabled".
	fmt.Printf("enabled:      %v\n", enabled)
	for i, c := range configs {
		if i > 0 {
			fmt.Println()
		}
		fmt.Printf("route:        %s\n", c.Name)
		fmt.Printf("  enabled:      %v\n", c.Enabled)
		fmt.Printf("  address:      %s\n", orDash(c.Address))
		fmt.Printf("  label:        %s\n", orDash(c.Label))
		if c.Pin != "" {
			fmt.Printf("  relay pin:    %s\n", prettyFingerprint(c.Pin))
		}
		fmt.Printf("  state:        %s\n", orDash(c.State))
		fmt.Printf("  last success: %s\n", orDash(c.LastSuccess))
		fmt.Printf("  last error:   %s\n", orDash(c.LastError))
	}
	if ferr == nil {
		fmt.Printf("relay id:     %s\n", fp)
	} else {
		fmt.Printf("relay id:     unavailable (%v)\n", ferr)
	}
	fmt.Printf("listener:     configured=%v (%s=%v)\n", relayConfiguredEnabled(), relayEnabledEnv, relayEnabled())
}

func runRelayDisconnect(args []string) {
	if len(args) > 1 {
		fmt.Fprintln(os.Stderr, "usage: ab-pty relay disconnect [ROUTE|host:port|--all]")
		os.Exit(2)
	}
	if strings.TrimSpace(os.Getenv(relayAddrEnv)) != "" {
		fmt.Fprintf(os.Stderr, "Error: relay is configured by %s; remove it from the environment to disconnect\n", relayAddrEnv)
		os.Exit(1)
	}
	selector := "--all"
	if len(args) == 1 {
		selector = args[0]
	}
	configs := loadRelayConfigs()
	changed := 0
	for _, c := range configs {
		if selector != "--all" && !relaySelectorMatches(c, selector) {
			continue
		}
		if c.Enabled {
			c.Enabled = false
			if err := saveRelayConfig(c); err != nil {
				fmt.Fprintf(os.Stderr, "Error: %v\n", err)
				os.Exit(1)
			}
		}
		setRelayState(c.Name, c.Address, "disconnected", "", false)
		changed++
	}
	if changed == 0 && selector != "--all" {
		fmt.Fprintf(os.Stderr, "Error: relay route %q not found\n", selector)
		os.Exit(1)
	}
	if selector == "--all" {
		fmt.Printf("Disabled %d relay route(s). A running daemon drops the connections within a few seconds.\n", changed)
	} else {
		fmt.Printf("Relay route %q disabled. A running daemon drops the connection within a few seconds.\n", selector)
	}
}

func orDash(s string) string {
	if strings.TrimSpace(s) == "" {
		return "-"
	}
	return s
}
