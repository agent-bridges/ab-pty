package main

import (
	"context"
	"crypto/tls"
	"crypto/x509"
	"encoding/json"
	"io"
	"net"
	"net/http"
	"path/filepath"
	"strings"
	"testing"
	"time"
)

// relayTestServer stands up the daemon's real mux behind the synthetic relay
// listener, with a freshly generated server keypair, and returns an
// http.Client that reaches it only through that listener.
type relayTestServer struct {
	ln      *relayListener
	srv     *http.Server
	certDir string
}

func newRelayTestServer(t *testing.T) *relayTestServer {
	t.Helper()
	initTestDB()
	initTLSClientsTable()
	if _, err := db.Exec(`DELETE FROM tls_clients`); err != nil {
		t.Fatalf("clearing tls_clients: %v", err)
	}

	dir := t.TempDir()
	certPath := filepath.Join(dir, "server.crt")
	keyPath := filepath.Join(dir, "server.key")
	if err := generateSelfSignedCert(certPath, keyPath, []string{"localhost"}, 1); err != nil {
		t.Fatalf("generating server cert: %v", err)
	}
	t.Setenv(tlsCertEnv, certPath)
	t.Setenv(tlsKeyEnv, keyPath)

	srv := &http.Server{Handler: buildMux()}
	ln, err := serveRelay(srv)
	if err != nil {
		t.Fatalf("serveRelay: %v", err)
	}
	t.Cleanup(func() {
		ln.Close()
		srv.Close()
	})
	return &relayTestServer{ln: ln, srv: srv, certDir: dir}
}

// client returns an http.Client whose every connection is a net.Pipe handed
// to the relay listener — no sockets, no ports, exactly the shape a tunnelled
// ssh channel will have in phase 1.
func (rt *relayTestServer) client(certs []tls.Certificate) *http.Client {
	return &http.Client{
		Timeout: 10 * time.Second,
		Transport: &http.Transport{
			DialContext: func(_ context.Context, _, _ string) (net.Conn, error) {
				local, remote := net.Pipe()
				if err := rt.ln.Deliver(remote); err != nil {
					return nil, err
				}
				return local, nil
			},
			TLSClientConfig: &tls.Config{
				// The daemon's certificate is self-signed; the client
				// identity is what this test is about.
				InsecureSkipVerify: true,
				Certificates:       certs,
			},
		},
	}
}

// newClientCert mints a self-signed client certificate and returns it with its
// SHA-256 fingerprint — the same identity shape the Android app uses.
func newClientCert(t *testing.T) (tls.Certificate, string) {
	t.Helper()
	dir := t.TempDir()
	certPath := filepath.Join(dir, "client.crt")
	keyPath := filepath.Join(dir, "client.key")
	if err := generateSelfSignedCert(certPath, keyPath, []string{"test-client"}, 1); err != nil {
		t.Fatalf("generating client cert: %v", err)
	}
	pair, err := tls.LoadX509KeyPair(certPath, keyPath)
	if err != nil {
		t.Fatalf("loading client keypair: %v", err)
	}
	der := pair.Certificate[0]
	if _, err := x509.ParseCertificate(der); err != nil {
		t.Fatalf("parsing client cert: %v", err)
	}
	return pair, certFingerprint(der)
}

// The relay path must demand a known client certificate even when the daemon
// itself is configured wide open. AB_PTY_TLS_MODE=off means plain HTTP on the
// network listener; on the relay it must mean nothing at all.
func TestRelayRequiresClientCertRegardlessOfMode(t *testing.T) {
	t.Setenv(tlsModeEnv, "off")
	t.Setenv(tlsAllowLoopbackEnv, "1")
	rt := newRelayTestServer(t)

	resp, err := rt.client(nil).Get("https://relay/info")
	if err == nil {
		resp.Body.Close()
		t.Fatalf("a client with no certificate reached /info through the relay (status %s)", resp.Status)
	}
	// The failure must be the handshake, not the application.
	if !isHandshakeRejection(err) {
		t.Fatalf("expected a TLS handshake rejection, got: %v", err)
	}

	// Positive control on the very same listener: the refusal above is about
	// the missing certificate and not about the plumbing.
	cert, fp := newClientCert(t)
	if err := addAuthorizedClient("test-phone", fp); err != nil {
		t.Fatalf("authorizing client: %v", err)
	}
	resp, err = rt.client([]tls.Certificate{cert}).Get("https://relay/info")
	if err != nil {
		t.Fatalf("authorized client rejected on the same listener: %v", err)
	}
	resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		t.Fatalf("expected 200 for the authorized client, got %s", resp.Status)
	}
}

// An unknown certificate is no better than none: the allow-list is the
// identity, not the mere possession of a key.
func TestRelayRejectsUnknownClientCert(t *testing.T) {
	t.Setenv(tlsModeEnv, "off")
	rt := newRelayTestServer(t)

	cert, _ := newClientCert(t) // deliberately not added to the allow-list
	resp, err := rt.client([]tls.Certificate{cert}).Get("https://relay/info")
	if err == nil {
		resp.Body.Close()
		t.Fatalf("an unauthorized certificate reached /info through the relay (status %s)", resp.Status)
	}
}

// The positive control: an enrolled client gets through, and /info reports it
// as authorized. Without this the two rejection tests above would also pass
// against a listener that is simply broken.
func TestRelayAcceptsAuthorizedClient(t *testing.T) {
	t.Setenv(tlsModeEnv, "off")
	rt := newRelayTestServer(t)

	cert, fp := newClientCert(t)
	if err := addAuthorizedClient("test-phone", fp); err != nil {
		t.Fatalf("authorizing client: %v", err)
	}

	resp, err := rt.client([]tls.Certificate{cert}).Get("https://relay/info")
	if err != nil {
		t.Fatalf("authorized client rejected: %v", err)
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusOK {
		t.Fatalf("expected 200, got %s", resp.Status)
	}
	body, _ := io.ReadAll(resp.Body)
	var info map[string]interface{}
	if err := json.Unmarshal(body, &info); err != nil {
		t.Fatalf("decoding /info: %v (%s)", err, body)
	}
	data, _ := info["data"].(map[string]interface{})
	if data == nil {
		data = info
	}
	if data["tls_client_authorized"] != true {
		t.Fatalf("expected tls_client_authorized=true, got %v", data["tls_client_authorized"])
	}
	if data["tls_client_name"] != "test-phone" {
		t.Fatalf("expected tls_client_name=test-phone, got %v", data["tls_client_name"])
	}
}

// /api/hook mutates the claude-session→pty mapping and carries no
// authentication of its own; it is loopback-only. A relay connection must
// never look like loopback — not because a case was added for it, but because
// its address does not parse as an IP at all.
func TestRelayCannotReachHookEvenWithLoopbackExemption(t *testing.T) {
	t.Setenv(tlsModeEnv, "required")
	// The exemption is set as hostile as possible: if it applied to relay
	// connections, this is where it would show.
	t.Setenv(tlsAllowLoopbackEnv, "1")
	rt := newRelayTestServer(t)

	cert, fp := newClientCert(t)
	if err := addAuthorizedClient("test-phone", fp); err != nil {
		t.Fatalf("authorizing client: %v", err)
	}
	client := rt.client([]tls.Certificate{cert})

	// Sanity: this same client can reach a normal endpoint, so a 403 below
	// is about the hook and not about the connection.
	if resp, err := client.Get("https://relay/health"); err != nil {
		t.Fatalf("authorized client rejected on /health: %v", err)
	} else {
		resp.Body.Close()
	}

	resp, err := client.Post("https://relay/api/hook", "application/json", nil)
	if err != nil {
		t.Fatalf("posting to /api/hook: %v", err)
	}
	defer resp.Body.Close()
	if resp.StatusCode != http.StatusForbidden {
		t.Fatalf("expected 403 on /api/hook through the relay, got %s", resp.Status)
	}
}

// The address itself, checked directly against the two predicates that decide
// who is trusted.
func TestRelayAddrIsNotLoopback(t *testing.T) {
	ln := newRelayListener()
	defer ln.Close()

	local, remote := net.Pipe()
	defer local.Close()
	if err := ln.Deliver(remote); err != nil {
		t.Fatalf("deliver: %v", err)
	}
	conn, err := ln.Accept()
	if err != nil {
		t.Fatalf("accept: %v", err)
	}
	addr := conn.RemoteAddr().String()

	if net.ParseIP(addr) != nil {
		t.Fatalf("relay address %q parses as an IP — loopback checks would apply to it", addr)
	}
	if isLoopbackAddr(addr) {
		t.Fatalf("relay address %q passes isLoopbackAddr", addr)
	}
	if host, _, err := net.SplitHostPort(addr); err == nil {
		t.Fatalf("relay address %q splits into host %q — it must not look like host:port", addr, host)
	}
}

// isHandshakeRejection distinguishes "the TLS handshake was refused" from any
// other transport failure, so the rejection tests cannot pass for the wrong
// reason (a broken pipe, a timeout, a nil listener).
func isHandshakeRejection(err error) bool {
	s := strings.ToLower(err.Error())
	// "closed pipe" belongs here: over net.Pipe the server aborts the
	// handshake by closing, and the client can see the close before it sees
	// the alert. Either way the connection died during the handshake, which
	// is the property under test — the daemon logs the precise reason
	// ("tls: client didn't provide a certificate").
	for _, want := range []string{"certificate", "handshake", "tls:", "remote error", "closed pipe"} {
		if strings.Contains(s, want) {
			return true
		}
	}
	return false
}
