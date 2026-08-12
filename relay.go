package main

import (
	"crypto/tls"
	"fmt"
	"log"
	"net"
	"net/http"
	"os"
	"strings"
	"sync"
	"sync/atomic"
)

// Relay scaffolding — phase 0 of docs/RELAY.md.
//
// The plan is that the daemon dials out to a VPS over ssh and serves the
// resulting reverse-forwarded channels itself, so that a machine with no
// public IP is reachable without anyone holding a shell on it. The load
// bearing idea is that the tunnelled byte stream is handed to *the same*
// http.Server and *the same* tls.Config as the ordinary listener, so nothing
// about authentication is re-implemented for the outside path and the VPS
// never sees plaintext: TLS terminates inside the daemon, past the relay.
//
// This file is that seam and nothing more. There is no ssh here yet: the
// listener takes connections from a channel, and whatever produces them —
// net.Pipe in tests today, an ssh channel in phase 1 — is somebody else's
// problem. The point of building it now is to find out here, cheaply, whether
// the idea actually holds.
//
// Two invariants are enforced at this seam, each of them one line, and the
// trust model collapses without either:
//
//   - the relay listener is ALWAYS mode=required and ALWAYS without the
//     loopback exemption, whatever AB_PTY_TLS_MODE and
//     AB_PTY_TLS_ALLOW_LOOPBACK say. An internet-reachable plain-HTTP daemon
//     must not be a state this program can reach;
//   - a relay connection's RemoteAddr is deliberately NOT parseable as an IP.
//     Everything loopback-gated in the daemon — the AB_PTY_TLS_ALLOW_LOOPBACK
//     exemption in the TLS handshake, requireLoopback in front of /api/hook —
//     decides by parsing RemoteAddr, so an address of the form "relay/7"
//     fails those checks by construction rather than by remembering to add a
//     special case. This mine has been stepped on before (commit d45bcf3).

const (
	relayEnabledEnv     = "AB_PTY_RELAY_ENABLED"
	relayNetwork        = "relay"
	relayAcceptBacklog  = 16
	relayListenerAddrID = "relay/listener"
)

// relayEnabled reports whether the daemon should serve the relay path. Phase 0
// has no tunnel to attach to it, so this only decides whether the synthetic
// listener is created; it is here now so the safety check below exists and is
// tested from the start.
func relayEnabled() bool {
	v := strings.ToLower(strings.TrimSpace(os.Getenv(relayEnabledEnv)))
	return v == "1" || v == "true" || v == "yes"
}

// --- synthetic address / connection ---------------------------------------

// relayAddr is a net.Addr that is intentionally not an IP. See the header
// comment: this is what makes loopback checks reject relay traffic without
// anyone having to remember them.
type relayAddr string

func (a relayAddr) Network() string { return relayNetwork }
func (a relayAddr) String() string  { return string(a) }

// relayConn is a tunnelled connection wearing a synthetic remote address.
type relayConn struct {
	net.Conn
	remote relayAddr
}

func (c *relayConn) RemoteAddr() net.Addr { return c.remote }

// --- synthetic listener ----------------------------------------------------

// relayListener is a net.Listener whose Accept() returns connections handed to
// it by Deliver, rather than ones it accepted from a socket. That is the whole
// trick: http.Server cannot tell the difference, so the relay path gets the
// daemon's real route table and real TLS configuration for free.
type relayListener struct {
	incoming chan net.Conn
	closed   chan struct{}
	once     sync.Once
	seq      atomic.Uint64
}

func newRelayListener() *relayListener {
	return &relayListener{
		incoming: make(chan net.Conn, relayAcceptBacklog),
		closed:   make(chan struct{}),
	}
}

func (l *relayListener) Accept() (net.Conn, error) {
	select {
	case c := <-l.incoming:
		return c, nil
	case <-l.closed:
		return nil, net.ErrClosed
	}
}

func (l *relayListener) Close() error {
	l.once.Do(func() { close(l.closed) })
	return nil
}

func (l *relayListener) Addr() net.Addr { return relayAddr(relayListenerAddrID) }

// Deliver hands a tunnelled stream to the HTTP server. It blocks until the
// server accepts it or the listener closes; the caller is the tunnel reader,
// which has nothing better to do meanwhile.
func (l *relayListener) Deliver(conn net.Conn) error {
	wrapped := &relayConn{
		Conn:   conn,
		remote: relayAddr(fmt.Sprintf("%s/%d", relayNetwork, l.seq.Add(1))),
	}
	select {
	case l.incoming <- wrapped:
		return nil
	case <-l.closed:
		conn.Close()
		return net.ErrClosed
	}
}

// --- serving ---------------------------------------------------------------

// relayTLSConfig is the relay's TLS configuration: client certificate
// mandatory, loopback exemption off, no matter how the daemon is configured
// for its own network listener.
func relayTLSConfig() (*tls.Config, error) {
	return buildTLSConfigWithLoopback(TLSModeRequired, false)
}

// serveRelay starts srv on a fresh synthetic listener and returns it, so the
// tunnel (phase 1) has somewhere to deliver connections. Serving happens in a
// goroutine; the listener is the handle the caller keeps.
func serveRelay(srv *http.Server) (*relayListener, error) {
	cfg, err := relayTLSConfig()
	if err != nil {
		return nil, fmt.Errorf("relay TLS: %w", err)
	}
	ln := newRelayListener()
	go func() {
		err := srv.Serve(tls.NewListener(ln, cfg))
		if err != nil && err != http.ErrServerClosed && err != net.ErrClosed {
			log.Printf("relay listener stopped: %v", err)
		}
	}()
	log.Printf("relay listener ready: mode=required, client certificate mandatory, loopback exemption off")
	return ln, nil
}

// relayLn is the live relay listener, set at startup when the relay is
// enabled. Phase 1's ssh reader delivers channels to it.
var relayLn *relayListener
