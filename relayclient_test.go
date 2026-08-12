package main

import (
	"context"
	"crypto/tls"
	"encoding/json"
	"fmt"
	"io"
	"net"
	"net/http"
	"path/filepath"
	"strings"
	"sync"
	"testing"
	"time"
)

// A fake relay, written from the protocol description rather than by calling
// into ab-relay: these tests exist to catch the two sides drifting apart, and
// sharing an implementation would defeat that. It is also, deliberately, the
// smallest thing that speaks the protocol — roughly what the Kotlin client will
// be.
type fakeRelay struct {
	t    *testing.T
	ln   net.Listener
	cfg  *tls.Config
	addr string

	mu       sync.Mutex
	ctl      net.Conn
	agentFP  string
	pending  map[string]chan net.Conn
	connects int
	closed   bool
}

func newFakeRelay(t *testing.T) *fakeRelay {
	t.Helper()
	dir := t.TempDir()
	crt := filepath.Join(dir, "relay.crt")
	key := filepath.Join(dir, "relay.key")
	if err := generateSelfSignedCert(crt, key, []string{"127.0.0.1"}, 1); err != nil {
		t.Fatalf("relay cert: %v", err)
	}
	pair, err := tls.LoadX509KeyPair(crt, key)
	if err != nil {
		t.Fatal(err)
	}
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	r := &fakeRelay{
		t:   t,
		ln:  ln,
		cfg: &tls.Config{Certificates: []tls.Certificate{pair}, ClientAuth: tls.RequireAnyClientCert, MinVersion: tls.VersionTLS12},
		// The relay never verifies a chain — agents are self-signed and
		// pinned by fingerprint, exactly like the daemon's own clients.
		addr:    ln.Addr().String(),
		pending: map[string]chan net.Conn{},
	}
	r.cfg.InsecureSkipVerify = true
	go r.accept()
	t.Cleanup(r.stop)
	return r
}

// listenAgain rebinds the same port after a stop, which is how the reconnect
// test plays "the relay was restarted".
func (r *fakeRelay) listenAgain() {
	ln, err := net.Listen("tcp", r.addr)
	if err != nil {
		r.t.Fatalf("rebinding %s: %v", r.addr, err)
	}
	r.mu.Lock()
	r.ln = ln
	r.closed = false
	r.mu.Unlock()
	go r.accept()
}

func (r *fakeRelay) stop() {
	r.mu.Lock()
	if r.closed {
		r.mu.Unlock()
		return
	}
	r.closed = true
	ln, ctl := r.ln, r.ctl
	r.ctl = nil
	r.mu.Unlock()
	_ = ln.Close()
	if ctl != nil {
		_ = ctl.Close()
	}
}

func (r *fakeRelay) accept() {
	for {
		c, err := r.ln.Accept()
		if err != nil {
			return
		}
		go r.handle(c)
	}
}

func (r *fakeRelay) handle(c net.Conn) {
	one := make([]byte, 1)
	if _, err := io.ReadFull(c, one); err != nil {
		c.Close()
		return
	}
	if one[0] == 0x16 {
		pc := &replayConn{Conn: c, r: io.MultiReader(strings.NewReader("\x16"), c)}
		tc := tls.Server(pc, r.cfg)
		if err := tc.Handshake(); err != nil {
			c.Close()
			return
		}
		r.control(tc)
		return
	}
	// Plaintext: a DATA answer.
	line, err := readRelayLine(io.MultiReader(strings.NewReader(string(one)), c))
	if err != nil {
		c.Close()
		return
	}
	f := strings.Fields(line)
	if len(f) < 3 || f[0] != relayProtoMagic || strings.ToUpper(f[1]) != relayRoleData {
		c.Close()
		return
	}
	r.mu.Lock()
	ch := r.pending[f[2]]
	delete(r.pending, f[2])
	r.mu.Unlock()
	if ch == nil {
		c.Close()
		return
	}
	if _, err := fmt.Fprintf(c, "%s OK\n", relayProtoMagic); err != nil {
		c.Close()
		return
	}
	ch <- c
}

func (r *fakeRelay) control(c net.Conn) {
	st := c.(*tls.Conn).ConnectionState()
	if len(st.PeerCertificates) == 0 {
		c.Close()
		return
	}
	fp := certFingerprint(st.PeerCertificates[0].Raw)

	line, err := readRelayLine(c)
	if err != nil {
		c.Close()
		return
	}
	f := strings.Fields(line)
	if len(f) < 2 || f[0] != relayProtoMagic || strings.ToUpper(f[1]) != relayRoleCtl {
		c.Close()
		return
	}
	if _, err := fmt.Fprintf(c, "%s OK id=%s name=test keepalive=1\n", relayProtoMagic, fp); err != nil {
		c.Close()
		return
	}
	r.mu.Lock()
	r.ctl = c
	r.agentFP = fp
	r.connects++
	r.mu.Unlock()

	for {
		line, err := readRelayLine(c)
		if err != nil {
			return
		}
		if verb, arg := relaySplit(line); verb == relayMsgPong {
			_ = arg
		}
	}
}

// open asks the daemon for a stream and returns the client end of it — the
// point at which the caller starts its own TLS handshake against the daemon.
func (r *fakeRelay) open() (net.Conn, error) {
	r.mu.Lock()
	ctl := r.ctl
	r.mu.Unlock()
	if ctl == nil {
		return nil, fmt.Errorf("no agent connected")
	}
	ticket := fmt.Sprintf("t%d", time.Now().UnixNano())
	ch := make(chan net.Conn, 1)
	r.mu.Lock()
	r.pending[ticket] = ch
	r.mu.Unlock()
	if _, err := fmt.Fprintf(ctl, "%s %s\n", relayMsgOpen, ticket); err != nil {
		return nil, err
	}
	select {
	case c := <-ch:
		return c, nil
	case <-time.After(10 * time.Second):
		return nil, fmt.Errorf("the daemon did not answer OPEN")
	}
}

func (r *fakeRelay) waitAgent(d time.Duration) bool {
	deadline := time.Now().Add(d)
	for time.Now().Before(deadline) {
		r.mu.Lock()
		got := r.ctl != nil
		r.mu.Unlock()
		if got {
			return true
		}
		time.Sleep(20 * time.Millisecond)
	}
	return false
}

func (r *fakeRelay) connectCount() int {
	r.mu.Lock()
	defer r.mu.Unlock()
	return r.connects
}

type replayConn struct {
	net.Conn
	r io.Reader
}

func (p *replayConn) Read(b []byte) (int, error) { return p.r.Read(b) }

func readRelayLine(r io.Reader) (string, error) {
	buf := make([]byte, 0, 64)
	one := make([]byte, 1)
	for {
		n, err := r.Read(one)
		if n == 1 {
			if one[0] == '\n' {
				return strings.TrimRight(string(buf), "\r"), nil
			}
			buf = append(buf, one[0])
			if len(buf) > relayMaxLine {
				return "", fmt.Errorf("line too long")
			}
			continue
		}
		if err != nil {
			return "", err
		}
	}
}

// --- harness ---------------------------------------------------------------

// relayClientStand runs the daemon's real mux behind the real synthetic
// listener, with the real relay client dialling a fake relay. Nothing between
// the HTTP handler and the socket is stubbed.
type relayClientStand struct {
	relay *fakeRelay
	stop  chan struct{}
}

func newRelayClientStand(t *testing.T) *relayClientStand {
	t.Helper()
	initTestDB()
	initTLSClientsTable()
	initRelayTable()
	if _, err := db.Exec(`DELETE FROM tls_clients`); err != nil {
		t.Fatal(err)
	}

	dir := t.TempDir()
	crt := filepath.Join(dir, "server.crt")
	key := filepath.Join(dir, "server.key")
	if err := generateSelfSignedCert(crt, key, []string{"localhost"}, 1); err != nil {
		t.Fatal(err)
	}
	t.Setenv(tlsCertEnv, crt)
	t.Setenv(tlsKeyEnv, key)
	t.Setenv(tlsModeEnv, "off")

	srv := &http.Server{Handler: buildMux()}
	ln, err := serveRelay(srv)
	if err != nil {
		t.Fatal(err)
	}
	relay := newFakeRelay(t)

	m := &relayManager{ln: ln}
	stop := make(chan struct{})
	go m.session(RelayConfig{Enabled: true, Address: relay.addr, Label: "test"}, stop)
	t.Cleanup(func() {
		close(stop)
		ln.Close()
		srv.Close()
	})
	if !relay.waitAgent(10 * time.Second) {
		t.Fatal("the daemon never registered with the relay")
	}
	return &relayClientStand{relay: relay, stop: stop}
}

// dialViaRelay is the transport a phone would have: every HTTP connection is a
// fresh relay stream, and the TLS on top of it is end to end. Nothing here
// terminates TLS, which is the property the relay's trust model rests on.
func dialViaRelay(r *fakeRelay) func(context.Context, string, string) (net.Conn, error) {
	return func(_ context.Context, _, _ string) (net.Conn, error) {
		return r.open()
	}
}

// --- tests -----------------------------------------------------------------

// The whole point, in one test: an HTTP request made by a client that has never
// heard of this machine's address arrives at the daemon's own mux, over TLS the
// relay cannot read, and is authorised by the certificate allow-list.
func TestRelayClientCarriesHTTP(t *testing.T) {
	s := newRelayClientStand(t)
	cert, fp := newClientCert(t)
	if err := addAuthorizedClient("test-phone", fp); err != nil {
		t.Fatal(err)
	}

	client := &http.Client{
		Timeout: 15 * time.Second,
		Transport: &http.Transport{
			DialContext: dialViaRelay(s.relay),
			TLSClientConfig: &tls.Config{
				InsecureSkipVerify: true,
				Certificates:       []tls.Certificate{cert},
			},
		},
	}
	resp, err := client.Get("https://relay/info")
	if err != nil {
		t.Fatalf("GET /info through the relay: %v", err)
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		t.Fatalf("status %s", resp.Status)
	}
	body, _ := io.ReadAll(resp.Body)
	var env map[string]interface{}
	if err := json.Unmarshal(body, &env); err != nil {
		t.Fatalf("decoding /info: %v (%s)", err, body)
	}
	data, _ := env["data"].(map[string]interface{})
	if data == nil {
		data = env
	}
	if data["tls_client_authorized"] != true {
		t.Fatalf("tls_client_authorized = %v", data["tls_client_authorized"])
	}
	// The identifier a client pins is the identifier the relay proved. If
	// these ever diverge, a relay could point a phone at the wrong machine
	// and the phone would not notice.
	fpOnDisk, err := serverCertFingerprintFromDisk()
	if err != nil {
		t.Fatal(err)
	}
	s.relay.mu.Lock()
	agentFP := s.relay.agentFP
	s.relay.mu.Unlock()
	if agentFP != fpOnDisk {
		t.Fatalf("the relay knows this daemon as %s but its certificate is %s", agentFP, fpOnDisk)
	}
	if data["tls_server_fingerprint"] != fpOnDisk {
		t.Fatalf("/info reports %v, certificate is %s", data["tls_server_fingerprint"], fpOnDisk)
	}
}

// Negative controls on the live relay path, not on a net.Pipe: the relay
// carries connections from an untrusted network, and everything that guards
// them has to hold when the bytes actually come off a socket.
func TestRelayClientRejectsUnauthorizedClients(t *testing.T) {
	// As hostile as the configuration can be made: the network listener is
	// plain HTTP and the loopback exemption is on.
	t.Setenv(tlsAllowLoopbackEnv, "1")
	s := newRelayClientStand(t)

	noCert := &http.Client{
		Timeout:   10 * time.Second,
		Transport: &http.Transport{DialContext: dialViaRelay(s.relay), TLSClientConfig: &tls.Config{InsecureSkipVerify: true}},
	}
	if resp, err := noCert.Get("https://relay/info"); err == nil {
		resp.Body.Close()
		t.Fatalf("a client with no certificate reached /info (status %s)", resp.Status)
	}

	stranger, _ := newClientCert(t) // never added to the allow-list
	unknown := &http.Client{
		Timeout: 10 * time.Second,
		Transport: &http.Transport{DialContext: dialViaRelay(s.relay),
			TLSClientConfig: &tls.Config{InsecureSkipVerify: true, Certificates: []tls.Certificate{stranger}}},
	}
	if resp, err := unknown.Get("https://relay/info"); err == nil {
		resp.Body.Close()
		t.Fatalf("an unauthorized certificate reached /info (status %s)", resp.Status)
	}

	// Positive control on the same path, so the two refusals above are
	// about identity and not about broken plumbing.
	cert, fp := newClientCert(t)
	if err := addAuthorizedClient("test-phone", fp); err != nil {
		t.Fatal(err)
	}
	good := &http.Client{
		Timeout: 10 * time.Second,
		Transport: &http.Transport{DialContext: dialViaRelay(s.relay),
			TLSClientConfig: &tls.Config{InsecureSkipVerify: true, Certificates: []tls.Certificate{cert}}},
	}
	resp, err := good.Get("https://relay/info")
	if err != nil {
		t.Fatalf("an authorized client was refused on the same path: %v", err)
	}
	resp.Body.Close()

	// /api/hook is loopback-only and mutates state without any
	// authentication of its own. A relay stream must never look local.
	resp, err = good.Post("https://relay/api/hook", "application/json", strings.NewReader("{}"))
	if err != nil {
		t.Fatalf("POST /api/hook: %v", err)
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusForbidden {
		t.Fatalf("/api/hook through the relay returned %s, want 403", resp.Status)
	}

	// Revocation bites the next connection, with no restart.
	if n, err := revokeAuthorizedClient("test-phone"); err != nil || n != 1 {
		t.Fatalf("revoke: n=%d err=%v", n, err)
	}
	good.CloseIdleConnections()
	if resp, err := good.Get("https://relay/info"); err == nil {
		resp.Body.Close()
		t.Fatal("a revoked client still reached /info through the relay")
	}
}

// The reconnect loop: kill the relay, bring it back, and the daemon must find
// its way home unaided.
func TestRelayClientReconnects(t *testing.T) {
	s := newRelayClientStand(t)
	if got := s.relay.connectCount(); got != 1 {
		t.Fatalf("connect count before the outage = %d", got)
	}

	s.relay.stop()
	time.Sleep(200 * time.Millisecond)
	s.relay.listenAgain()

	deadline := time.Now().Add(20 * time.Second)
	for time.Now().Before(deadline) {
		if s.relay.connectCount() >= 2 && s.relay.waitAgent(time.Second) {
			break
		}
		time.Sleep(100 * time.Millisecond)
	}
	if s.relay.connectCount() < 2 {
		t.Fatal("the daemon did not reconnect after the relay came back")
	}

	// And the path works again, which is the part that actually matters.
	cert, fp := newClientCert(t)
	if err := addAuthorizedClient("test-phone", fp); err != nil {
		t.Fatal(err)
	}
	client := &http.Client{
		Timeout: 15 * time.Second,
		Transport: &http.Transport{DialContext: dialViaRelay(s.relay),
			TLSClientConfig: &tls.Config{InsecureSkipVerify: true, Certificates: []tls.Certificate{cert}}},
	}
	resp, err := client.Get("https://relay/health")
	if err != nil {
		t.Fatalf("after the reconnect: %v", err)
	}
	resp.Body.Close()
}

// The backoff schedule. Two properties, both load-bearing:
//   - it grows, so a relay that is down for an hour is not hammered;
//   - it is spread out, so N daemons that noticed the same outage do not all
//     retry in the same millisecond forever.
func TestRelayBackoff(t *testing.T) {
	// Growth, measured at the low end of each window so the jitter cannot
	// make the assertion flaky.
	prev := time.Duration(0)
	for a := 0; a < 8; a++ {
		d := relayBackoff(a, 0)
		if a > 0 && d < prev {
			t.Fatalf("attempt %d waits %s, less than attempt %d's %s", a, d, a-1, prev)
		}
		prev = d
	}
	if got := relayBackoff(30, 0.999); got > relayBackoffMax {
		t.Fatalf("backoff is unbounded: %s", got)
	}
	if got := relayBackoff(0, 0); got < relayBackoffBase/2 {
		t.Fatalf("the first retry is immediate: %s", got)
	}

	// Spread: a hundred daemons hitting the same attempt number must not
	// land on the same instant. With a [w/2, w) window the values have to
	// cover a good part of the range.
	seen := map[time.Duration]bool{}
	var min, max time.Duration
	for i := 0; i < 100; i++ {
		d := relayBackoff(3, float64(i)/100.0)
		seen[d] = true
		if min == 0 || d < min {
			min = d
		}
		if d > max {
			max = d
		}
	}
	if len(seen) < 50 {
		t.Fatalf("only %d distinct delays across 100 daemons — the herd stays synchronised", len(seen))
	}
	w := relayBackoff(3, 0) * 2 // the window's low edge is w/2
	if max-min < w/4 {
		t.Fatalf("delays span only %s of a %s window", max-min, w)
	}
}

// The configuration round-trips through SQLite, which is what makes
// `ab-pty relay connect` take effect on a running daemon and survive a restart.
func TestRelayConfigRoundTrip(t *testing.T) {
	initTestDB()
	initRelayTable()
	if _, err := db.Exec(`DELETE FROM relay_config`); err != nil {
		t.Fatal(err)
	}
	if relayConfiguredEnabled() {
		t.Fatal("a fresh install has the relay on")
	}
	if err := saveRelayConfig(true, "relay.example:9500", "homebox", ""); err != nil {
		t.Fatal(err)
	}
	c := loadRelayConfig()
	if !c.Enabled || c.Address != "relay.example:9500" || c.Label != "homebox" {
		t.Fatalf("round trip: %+v", c)
	}
	if !relayConfiguredEnabled() {
		t.Fatal("relayConfiguredEnabled disagrees with the stored row")
	}

	setRelayState("connected", "", true)
	if c := loadRelayConfig(); c.State != "connected" || c.LastSuccess == "" {
		t.Fatalf("state not recorded: %+v", c)
	}

	if err := saveRelayConfig(false, c.Address, c.Label, ""); err != nil {
		t.Fatal(err)
	}
	if relayConfiguredEnabled() {
		t.Fatal("disconnect did not stick")
	}

	// The environment overrides the row, for containers and unit files.
	t.Setenv(relayAddrEnv, "env.example:9999")
	if c := loadRelayConfig(); !c.Enabled || c.Address != "env.example:9999" {
		t.Fatalf("environment override ignored: %+v", c)
	}
}

// Turning the relay on must be incompatible with the loopback exemption
// whichever way it was turned on — the environment or the stored row.
func TestRelayFromDatabaseStillRefusesLoopbackExemption(t *testing.T) {
	t.Setenv(relayEnabledEnv, "0")
	t.Setenv(tlsAllowLoopbackEnv, "1")
	if err := validateRelayConfig(); err != nil {
		t.Fatalf("the exemption alone must stay allowed: %v", err)
	}
	if err := validateRelayActive(true); err == nil {
		t.Fatal("a database-configured relay escapes the loopback check")
	}
}
