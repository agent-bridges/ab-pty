package main

// Mutual TLS for the ab-pty daemon.
//
// Why this exists: the daemon binds 0.0.0.0 and its only authentication is a
// bearer JWT. Anything that can reach the port can at least probe it, and a
// leaked JWT is game over. Historically TLS was bolted on with an external
// nginx terminator (see ../CLAUDE.md, "HTTPS PTY setup"). This is the native
// replacement — no nginx, no new Go dependencies, stdlib crypto/tls only.
//
// Trust model: clients (the Android app) generate their OWN self-signed
// certificate and never talk to a CA. So the daemon does NOT verify a chain —
// it pins the SHA-256 fingerprint of the leaf certificate against an
// allow-list in its SQLite DB, exactly like ssh authorized_keys. That is why
// tls.RequireAndVerifyClientCert is unusable here (it would reject every
// self-signed peer before our code ever runs) and we use
// RequireAnyClientCert + a custom VerifyPeerCertificate instead.
//
// Compatibility contract: AB_PTY_TLS_MODE defaults to "off", which is
// byte-for-byte the previous behaviour (plain HTTP, no certificate files
// touched, no DB writes beyond the table creation). Every new behaviour is
// opt-in.

import (
	"crypto/rand"
	"crypto/rsa"
	"crypto/sha256"
	"crypto/tls"
	"crypto/x509"
	"crypto/x509/pkix"
	"encoding/hex"
	"encoding/pem"
	"flag"
	"fmt"
	"log"
	"math/big"
	"net"
	"net/http"
	"os"
	"path/filepath"
	"strings"
	"sync"
	"time"
)

// --- configuration --------------------------------------------------------

const (
	// AB_PTY_TLS_MODE: off | optional | required. Default "off".
	tlsModeEnv = "AB_PTY_TLS_MODE"
	// AB_PTY_TLS_CERT / AB_PTY_TLS_KEY pin the server keypair to exact
	// paths, mirroring how AB_PTY_JWT_SECRET_PATH pins the JWT secret.
	tlsCertEnv = "AB_PTY_TLS_CERT"
	tlsKeyEnv  = "AB_PTY_TLS_KEY"
	// AB_PTY_TLS_ALLOW_LOOPBACK=1 downgrades "required" to "optional" for
	// connections originating on 127.0.0.1/::1. Off by default: "required"
	// means required. See tlsAllowLoopback below for the trade-off.
	tlsAllowLoopbackEnv = "AB_PTY_TLS_ALLOW_LOOPBACK"
)

const (
	TLSModeOff      = "off"
	TLSModeOptional = "optional"
	TLSModeRequired = "required"
)

// tlsMode returns the normalised, validated mode. Anything unrecognised is a
// fatal misconfiguration rather than a silent downgrade to "off" — silently
// serving plain HTTP when the operator asked for TLS is the one failure mode
// that must never happen.
func tlsMode() string {
	raw := strings.ToLower(strings.TrimSpace(os.Getenv(tlsModeEnv)))
	switch raw {
	case "", TLSModeOff:
		return TLSModeOff
	case TLSModeOptional, TLSModeRequired:
		return raw
	default:
		log.Fatalf("invalid %s=%q (want off|optional|required)", tlsModeEnv, raw)
		return TLSModeOff
	}
}

// tlsAllowLoopback: when set, a connection from 127.0.0.1/::1 may skip the
// client certificate even in "required" mode. This exists because the daemon's
// own in-session CLI (`ab sessions ...`), the /api/hook endpoint used by Claude
// Code hooks, and scripts/dev-daemon.sh all talk to the daemon over loopback
// with no certificate of their own. It is NOT an auth bypass: those callers
// still need a JWT or an in-session token. Default off.
func tlsAllowLoopback() bool {
	v := strings.ToLower(strings.TrimSpace(os.Getenv(tlsAllowLoopbackEnv)))
	return v == "1" || v == "true" || v == "yes"
}

// tlsDefaultDir puts the keypair next to the JWT secret, under a tls/
// subdirectory. When AB_PTY_JWT_SECRET_PATH is set (non-canonical installs,
// e.g. the dev stand under $HOME) the certificates follow it, so an install
// that has no /opt access does not end up with half its state in /opt.
func tlsDefaultDir() string {
	if p := strings.TrimSpace(os.Getenv(jwtSecretPathEnv)); p != "" {
		return filepath.Join(filepath.Dir(p), "tls")
	}
	return filepath.Join(filepath.Dir(jwtSecretFileCanonical), "tls")
}

func tlsCertPath() string {
	if p := strings.TrimSpace(os.Getenv(tlsCertEnv)); p != "" {
		return p
	}
	return filepath.Join(tlsDefaultDir(), "server.crt")
}

func tlsKeyPath() string {
	if p := strings.TrimSpace(os.Getenv(tlsKeyEnv)); p != "" {
		return p
	}
	return filepath.Join(tlsDefaultDir(), "server.key")
}

// --- fingerprints ---------------------------------------------------------

// certFingerprint is the SHA-256 over the DER encoding of the certificate —
// the same bytes `openssl x509 -fingerprint -sha256` reports, and the same
// value Android's X509Certificate.getEncoded() hashes to. Returned lowercase
// hex with no separators.
func certFingerprint(der []byte) string {
	sum := sha256.Sum256(der)
	return hex.EncodeToString(sum[:])
}

// normalizeFingerprint accepts the shapes humans actually paste: with or
// without colons, spaces, a leading "sha256:" or "SHA256 Fingerprint=" label,
// upper or lower case. Returns lowercase 64-hex or an error.
func normalizeFingerprint(s string) (string, error) {
	t := strings.TrimSpace(s)
	if i := strings.LastIndex(t, "="); i >= 0 {
		t = t[i+1:] // "SHA256 Fingerprint=AA:BB:..."
	}
	t = strings.TrimPrefix(strings.ToLower(strings.TrimSpace(t)), "sha256:")
	var b strings.Builder
	for _, r := range t {
		switch {
		case r >= '0' && r <= '9', r >= 'a' && r <= 'f':
			b.WriteRune(r)
		case r >= 'A' && r <= 'F':
			b.WriteRune(r + ('a' - 'A'))
		case r == ':' || r == ' ' || r == '-' || r == '\t' || r == '\n' || r == '\r':
			// separator, drop
		default:
			return "", fmt.Errorf("not a hex SHA-256 fingerprint: %q", s)
		}
	}
	out := b.String()
	if len(out) != 64 {
		return "", fmt.Errorf("fingerprint must be 64 hex chars (SHA-256), got %d in %q", len(out), s)
	}
	return out, nil
}

// prettyFingerprint renders colon-separated uppercase for display, matching
// what openssl and Android's UI show.
func prettyFingerprint(fp string) string {
	up := strings.ToUpper(fp)
	parts := make([]string, 0, len(up)/2)
	for i := 0; i+1 < len(up); i += 2 {
		parts = append(parts, up[i:i+2])
	}
	return strings.Join(parts, ":")
}

// --- authorized client store ----------------------------------------------

// AuthorizedClient is one row of the allow-list.
type AuthorizedClient struct {
	Name        string `json:"name"`
	Fingerprint string `json:"fingerprint"`
	AddedAt     string `json:"added_at"`
	LastSeen    string `json:"last_seen,omitempty"`
}

// initTLSClientsTable is called from initDB. Creating the table in "off" mode
// too keeps `ab-pty client list` answering on an untouched install.
func initTLSClientsTable() {
	if _, err := db.Exec(`
		CREATE TABLE IF NOT EXISTS tls_clients (
			fingerprint TEXT PRIMARY KEY,
			name        TEXT NOT NULL,
			added_at    DATETIME DEFAULT CURRENT_TIMESTAMP,
			last_seen   DATETIME
		)
	`); err != nil {
		log.Fatal(err)
	}
	if _, err := db.Exec(`CREATE INDEX IF NOT EXISTS idx_tls_clients_name ON tls_clients(name)`); err != nil {
		log.Fatal(err)
	}
}

func addAuthorizedClient(name, fingerprint string) error {
	fp, err := normalizeFingerprint(fingerprint)
	if err != nil {
		return err
	}
	name = strings.TrimSpace(name)
	if name == "" {
		return fmt.Errorf("client name must not be empty")
	}
	_, err = db.Exec(
		`INSERT INTO tls_clients (fingerprint, name, added_at) VALUES (?, ?, CURRENT_TIMESTAMP)
		 ON CONFLICT(fingerprint) DO UPDATE SET name = excluded.name`,
		fp, name)
	return err
}

func listAuthorizedClients() ([]AuthorizedClient, error) {
	rows, err := db.Query(`SELECT name, fingerprint, COALESCE(added_at,''), COALESCE(last_seen,'')
	                       FROM tls_clients ORDER BY added_at`)
	if err != nil {
		return nil, err
	}
	defer rows.Close()
	out := []AuthorizedClient{}
	for rows.Next() {
		var c AuthorizedClient
		if err := rows.Scan(&c.Name, &c.Fingerprint, &c.AddedAt, &c.LastSeen); err != nil {
			return nil, err
		}
		out = append(out, c)
	}
	return out, rows.Err()
}

// revokeAuthorizedClient removes by name, or — if nothing matched — by
// fingerprint, so an operator who only has the fingerprint on hand is not
// stuck. Returns how many rows went away.
func revokeAuthorizedClient(nameOrFingerprint string) (int64, error) {
	res, err := db.Exec(`DELETE FROM tls_clients WHERE name = ?`, strings.TrimSpace(nameOrFingerprint))
	if err != nil {
		return 0, err
	}
	n, _ := res.RowsAffected()
	if n > 0 {
		return n, nil
	}
	if fp, ferr := normalizeFingerprint(nameOrFingerprint); ferr == nil {
		res, err = db.Exec(`DELETE FROM tls_clients WHERE fingerprint = ?`, fp)
		if err != nil {
			return 0, err
		}
		n, _ = res.RowsAffected()
	}
	return n, nil
}

// lookupAuthorizedClient reads straight through to SQLite on every handshake —
// no cache — so `ab-pty client revoke` takes effect on the very next
// connection without restarting the daemon. Handshakes are rare compared to
// the cost of a primary-key lookup.
func lookupAuthorizedClient(fp string) (string, bool) {
	if db == nil {
		return "", false
	}
	var name string
	err := db.QueryRow(`SELECT name FROM tls_clients WHERE fingerprint = ?`, fp).Scan(&name)
	if err != nil {
		return "", false
	}
	return name, true
}

// touchAuthorizedClient records a successful handshake. Fired off the
// handshake goroutine: a SQLite write blocked behind another writer must never
// stall a TLS accept. Serialised through a single-slot channel so a burst of
// reconnects cannot spawn unbounded goroutines.
var touchQueue = make(chan string, 64)
var touchOnce sync.Once

func touchAuthorizedClient(fp string) {
	touchOnce.Do(func() {
		go func() {
			for f := range touchQueue {
				if db == nil {
					continue
				}
				if _, err := db.Exec(`UPDATE tls_clients SET last_seen = CURRENT_TIMESTAMP WHERE fingerprint = ?`, f); err != nil {
					log.Printf("tls: recording last_seen for %s: %v", f[:16], err)
				}
			}
		}()
	})
	select {
	case touchQueue <- fp:
	default: // queue full — last_seen is telemetry, never worth blocking on
	}
}

// --- server certificate ---------------------------------------------------

// tlsServerFingerprint is the SHA-256 of the certificate this daemon presents.
// Published in /info (it is not a secret — every client sees it on the wire)
// so the Android app can show the user what it is about to trust.
var tlsServerFingerprint string

// generateSelfSignedCert writes a fresh keypair. hosts are extra SAN entries
// on top of the auto-discovered set.
//
// SANs matter more than usual here: clients reach this daemon by raw IP
// (http://192.168.1.7:8421 in the LAN stand, 127.0.0.1 through a reverse-ssh
// tunnel from the Mac emulator). A certificate with only a CN would be
// rejected by Go, Android and curl alike, so every address the daemon might be
// dialled on goes into SAN — all local interface IPs, localhost, 127.0.0.1,
// ::1 and the hostname.
func generateSelfSignedCert(certPath, keyPath string, hosts []string, days int) error {
	key, err := rsa.GenerateKey(rand.Reader, 2048)
	if err != nil {
		return fmt.Errorf("generating key: %w", err)
	}

	hostname, _ := os.Hostname()
	dnsNames := map[string]bool{"localhost": true}
	if hostname != "" {
		dnsNames[hostname] = true
	}
	ipSet := map[string]net.IP{
		"127.0.0.1": net.ParseIP("127.0.0.1"),
		"::1":       net.ParseIP("::1"),
	}
	if addrs, err := net.InterfaceAddrs(); err == nil {
		for _, a := range addrs {
			if ipnet, ok := a.(*net.IPNet); ok && !ipnet.IP.IsLinkLocalUnicast() {
				ipSet[ipnet.IP.String()] = ipnet.IP
			}
		}
	}
	for _, h := range hosts {
		h = strings.TrimSpace(h)
		if h == "" {
			continue
		}
		if ip := net.ParseIP(h); ip != nil {
			ipSet[ip.String()] = ip
		} else {
			dnsNames[h] = true
		}
	}

	dns := make([]string, 0, len(dnsNames))
	for d := range dnsNames {
		dns = append(dns, d)
	}
	ips := make([]net.IP, 0, len(ipSet))
	for _, ip := range ipSet {
		ips = append(ips, ip)
	}

	serial, err := rand.Int(rand.Reader, new(big.Int).Lsh(big.NewInt(1), 128))
	if err != nil {
		return fmt.Errorf("generating serial: %w", err)
	}
	cn := hostname
	if cn == "" {
		cn = "ab-pty"
	}
	tmpl := x509.Certificate{
		SerialNumber:          serial,
		Subject:               pkix.Name{CommonName: cn, Organization: []string{"ab-pty"}},
		NotBefore:             time.Now().Add(-1 * time.Hour),
		NotAfter:              time.Now().AddDate(0, 0, days),
		KeyUsage:              x509.KeyUsageKeyEncipherment | x509.KeyUsageDigitalSignature | x509.KeyUsageCertSign,
		ExtKeyUsage:           []x509.ExtKeyUsage{x509.ExtKeyUsageServerAuth},
		BasicConstraintsValid: true,
		IsCA:                  true,
		DNSNames:              dns,
		IPAddresses:           ips,
	}

	der, err := x509.CreateCertificate(rand.Reader, &tmpl, &tmpl, &key.PublicKey, key)
	if err != nil {
		return fmt.Errorf("creating certificate: %w", err)
	}

	if err := os.MkdirAll(filepath.Dir(certPath), 0755); err != nil {
		return err
	}
	if err := os.MkdirAll(filepath.Dir(keyPath), 0755); err != nil {
		return err
	}
	certOut, err := os.OpenFile(certPath, os.O_WRONLY|os.O_CREATE|os.O_TRUNC, 0644)
	if err != nil {
		return err
	}
	if err := pem.Encode(certOut, &pem.Block{Type: "CERTIFICATE", Bytes: der}); err != nil {
		certOut.Close()
		return err
	}
	if err := certOut.Close(); err != nil {
		return err
	}
	// 0600: the private key must not be world-readable even though the
	// daemon usually runs as root.
	keyOut, err := os.OpenFile(keyPath, os.O_WRONLY|os.O_CREATE|os.O_TRUNC, 0600)
	if err != nil {
		return err
	}
	if err := pem.Encode(keyOut, &pem.Block{Type: "RSA PRIVATE KEY", Bytes: x509.MarshalPKCS1PrivateKey(key)}); err != nil {
		keyOut.Close()
		return err
	}
	if err := keyOut.Close(); err != nil {
		return err
	}

	fmt.Printf("Server certificate: %s\n", certPath)
	fmt.Printf("Server key:         %s\n", keyPath)
	fmt.Printf("Valid until:        %s\n", tmpl.NotAfter.Format(time.RFC3339))
	fmt.Printf("SAN DNS:            %s\n", strings.Join(dns, ", "))
	ipStrs := make([]string, 0, len(ips))
	for _, ip := range ips {
		ipStrs = append(ipStrs, ip.String())
	}
	fmt.Printf("SAN IP:             %s\n", strings.Join(ipStrs, ", "))
	fmt.Printf("SHA-256:            %s\n", prettyFingerprint(certFingerprint(der)))
	return nil
}

// --- TLS config -----------------------------------------------------------

// buildTLSConfig loads the keypair and wires the fingerprint check.
//
// GetConfigForClient exists purely so the verify callback can name the peer's
// address in log lines — VerifyPeerCertificate gets raw DER and nothing else,
// and "rejected an unknown certificate" without a source address is useless
// when three devices are on the LAN.
func buildTLSConfig(mode string) (*tls.Config, error) {
	return buildTLSConfigWithLoopback(mode, tlsAllowLoopback())
}

// buildTLSConfigWithLoopback takes the loopback exemption as an argument
// instead of reading the environment, because not every listener gets to have
// an opinion about it: the relay listener is built with required + no
// exemption unconditionally (see relay.go), whatever AB_PTY_TLS_MODE and
// AB_PTY_TLS_ALLOW_LOOPBACK say.
func buildTLSConfigWithLoopback(mode string, allowLoopback bool) (*tls.Config, error) {
	certPath, keyPath := tlsCertPath(), tlsKeyPath()
	cert, err := tls.LoadX509KeyPair(certPath, keyPath)
	if err != nil {
		return nil, fmt.Errorf("loading TLS keypair (%s / %s): %w — run `ab-pty tls init`", certPath, keyPath, err)
	}
	if len(cert.Certificate) > 0 {
		tlsServerFingerprint = certFingerprint(cert.Certificate[0])
	}

	base := &tls.Config{
		Certificates: []tls.Certificate{cert},
		MinVersion:   tls.VersionTLS12,
	}

	base.GetConfigForClient = func(chi *tls.ClientHelloInfo) (*tls.Config, error) {
		peer := ""
		if chi.Conn != nil && chi.Conn.RemoteAddr() != nil {
			peer = chi.Conn.RemoteAddr().String()
		}
		effective := mode
		if mode == TLSModeRequired && allowLoopback && isLoopbackAddr(peer) {
			effective = TLSModeOptional
		}
		c := base.Clone()
		switch effective {
		case TLSModeOptional:
			// RequestClientCert: ask, but a client with nothing to show
			// still completes the handshake. This is the enrolment mode —
			// the app connects before it owns a key so the operator can
			// read its fingerprint and register it.
			c.ClientAuth = tls.RequestClientCert
		case TLSModeRequired:
			// RequireAnyClientCert, deliberately NOT
			// RequireAndVerifyClientCert: our clients are self-signed and
			// have no chain, so the stdlib chain check would reject them
			// all before VerifyPeerCertificate ever runs.
			c.ClientAuth = tls.RequireAnyClientCert
		}
		c.VerifyPeerCertificate = makePeerVerifier(effective, peer)
		return c, nil
	}

	return base, nil
}

func isLoopbackAddr(addr string) bool {
	host, _, err := net.SplitHostPort(addr)
	if err != nil {
		host = addr
	}
	ip := net.ParseIP(strings.Trim(host, "[]"))
	return ip != nil && ip.IsLoopback()
}

// makePeerVerifier returns the fingerprint allow-list check. Every rejection
// logs the fingerprint that was offered and the reason — without that, the
// only symptom on the client is a bare "connection reset" and debugging turns
// into guesswork.
func makePeerVerifier(mode string, peer string) func([][]byte, [][]*x509.Certificate) error {
	return func(rawCerts [][]byte, _ [][]*x509.Certificate) error {
		if len(rawCerts) == 0 {
			if mode == TLSModeRequired {
				log.Printf("tls: REJECT %s — no client certificate offered (mode=required)", peer)
				return fmt.Errorf("client certificate required")
			}
			return nil
		}
		fp := certFingerprint(rawCerts[0])
		subject := ""
		if c, err := x509.ParseCertificate(rawCerts[0]); err == nil {
			subject = c.Subject.CommonName
		}
		name, ok := lookupAuthorizedClient(fp)
		if ok {
			touchAuthorizedClient(fp)
			log.Printf("tls: accept %s — client %q (sha256 %s)", peer, name, prettyFingerprint(fp))
			return nil
		}
		if mode == TLSModeRequired {
			log.Printf("tls: REJECT %s — client certificate not in allow-list (CN=%q sha256 %s). "+
				"Authorize it with: ab-pty client add <name> %s",
				peer, subject, prettyFingerprint(fp), fp)
			return fmt.Errorf("client certificate %s is not authorized", fp)
		}
		log.Printf("tls: accept %s (mode=optional) — UNKNOWN client certificate (CN=%q sha256 %s). "+
			"To authorize: ab-pty client add <name> %s", peer, subject, prettyFingerprint(fp), fp)
		return nil
	}
}

// tlsPeerName returns the allow-listed name for the certificate on this
// request, if any. Used by /info so the app can tell "my cert is registered"
// from "my cert is being tolerated because the daemon is in optional mode".
func tlsPeerName(r *http.Request) string {
	if r.TLS == nil || len(r.TLS.PeerCertificates) == 0 {
		return ""
	}
	name, _ := lookupAuthorizedClient(certFingerprint(r.TLS.PeerCertificates[0].Raw))
	return name
}

// --- subcommands ----------------------------------------------------------

const tlsUsage = `ab-pty tls — native TLS / mutual-TLS for the daemon

  ab-pty tls init [-force] [-host H,H] [-days N] [-cert PATH] [-key PATH]
        Generate the self-signed server keypair. SANs automatically include
        localhost, 127.0.0.1, ::1, the hostname and every local interface IP;
        -host adds more (IPs or DNS names, comma-separated or repeated).
        Refuses to overwrite an existing pair unless -force is given.

  ab-pty tls status
        Show the configured mode, certificate paths and server fingerprint.

  ab-pty tls fingerprint
        Print the server certificate's SHA-256 fingerprint (hex, no colons).

Client allow-list (see also the top-level aliases: ab-pty client add|list|revoke):

  ab-pty tls client add <name> <sha256-fingerprint>
  ab-pty tls client list
  ab-pty tls client revoke <name|fingerprint>

Environment:
  AB_PTY_TLS_MODE            off (default) | optional | required
  AB_PTY_TLS_CERT            server certificate path
  AB_PTY_TLS_KEY             server key path
  AB_PTY_TLS_ALLOW_LOOPBACK  1 = exempt 127.0.0.1/::1 from "required"
  AB_PTY_DATABASE            SQLite DB holding the client allow-list
`

func runTLS(args []string) {
	if len(args) == 0 || args[0] == "-h" || args[0] == "--help" || args[0] == "help" {
		fmt.Print(tlsUsage)
		return
	}
	switch args[0] {
	case "init":
		runTLSInit(args[1:])
	case "status":
		runTLSStatus()
	case "fingerprint":
		runTLSFingerprint()
	case "client":
		runTLSClient(args[1:])
	default:
		fmt.Fprintf(os.Stderr, "unknown tls subcommand: %s\n\n", args[0])
		fmt.Print(tlsUsage)
		os.Exit(2)
	}
}

type stringList []string

func (s *stringList) String() string { return strings.Join(*s, ",") }
func (s *stringList) Set(v string) error {
	for _, part := range strings.Split(v, ",") {
		if p := strings.TrimSpace(part); p != "" {
			*s = append(*s, p)
		}
	}
	return nil
}

func runTLSInit(args []string) {
	var (
		force    bool
		days     int
		hosts    stringList
		certPath string
		keyPath  string
	)
	fs := flag.NewFlagSet("tls init", flag.ExitOnError)
	fs.BoolVar(&force, "force", false, "Overwrite an existing keypair")
	fs.IntVar(&days, "days", 3650, "Validity in days")
	fs.Var(&hosts, "host", "Extra SAN entry (IP or DNS name); repeatable or comma-separated")
	fs.StringVar(&certPath, "cert", "", "Certificate output path (default: $AB_PTY_TLS_CERT)")
	fs.StringVar(&keyPath, "key", "", "Key output path (default: $AB_PTY_TLS_KEY)")
	fs.Parse(args)

	if certPath == "" {
		certPath = tlsCertPath()
	}
	if keyPath == "" {
		keyPath = tlsKeyPath()
	}

	// Never silently clobber: overwriting the key invalidates nothing on the
	// daemon side but every pinned client would suddenly see a stranger.
	if !force {
		for _, p := range []string{certPath, keyPath} {
			if _, err := os.Stat(p); err == nil {
				fmt.Fprintf(os.Stderr,
					"%s already exists — refusing to overwrite. Re-run with -force if that is really what you want.\n", p)
				os.Exit(1)
			}
		}
	}

	if err := generateSelfSignedCert(certPath, keyPath, hosts, days); err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}
	fmt.Printf("\nEnable it with: %s=optional (enrolment) or %s=required (locked down)\n", tlsModeEnv, tlsModeEnv)
}

func runTLSStatus() {
	certPath, keyPath := tlsCertPath(), tlsKeyPath()
	fmt.Printf("mode:        %s (%s)\n", tlsMode(), tlsModeEnv)
	fmt.Printf("certificate: %s%s\n", certPath, existsSuffix(certPath))
	fmt.Printf("key:         %s%s\n", keyPath, existsSuffix(keyPath))
	if fp, err := serverCertFingerprintFromDisk(); err == nil {
		fmt.Printf("sha256:      %s\n", prettyFingerprint(fp))
	}
	fmt.Printf("loopback exempt in required mode: %v (%s)\n", tlsAllowLoopback(), tlsAllowLoopbackEnv)
}

func existsSuffix(p string) string {
	if _, err := os.Stat(p); err == nil {
		return " (present)"
	}
	return " (missing)"
}

func serverCertFingerprintFromDisk() (string, error) {
	data, err := os.ReadFile(tlsCertPath())
	if err != nil {
		return "", err
	}
	block, _ := pem.Decode(data)
	if block == nil {
		return "", fmt.Errorf("%s is not PEM", tlsCertPath())
	}
	return certFingerprint(block.Bytes), nil
}

func runTLSFingerprint() {
	fp, err := serverCertFingerprintFromDisk()
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v — run `ab-pty tls init` first\n", err)
		os.Exit(1)
	}
	fmt.Println(fp)
}

// runTLSClient implements add/list/revoke. It opens the daemon's DB directly
// rather than going through the HTTP API: it has to work when the daemon is
// stopped (initial enrolment) and when the daemon is in required mode and
// would refuse the CLI's own certificate-less connection.
func runTLSClient(args []string) {
	if len(args) == 0 {
		fmt.Fprintln(os.Stderr, "usage: ab-pty client <add|list|revoke> ...")
		os.Exit(2)
	}
	initDB()
	switch args[0] {
	case "add":
		if len(args) < 3 {
			fmt.Fprintln(os.Stderr, "usage: ab-pty client add <name> <sha256-fingerprint>")
			os.Exit(2)
		}
		if err := addAuthorizedClient(args[1], args[2]); err != nil {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
			os.Exit(1)
		}
		fp, _ := normalizeFingerprint(args[2])
		fmt.Printf("Authorized client %q: %s\n", args[1], prettyFingerprint(fp))
	case "list":
		clients, err := listAuthorizedClients()
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
			os.Exit(1)
		}
		if len(clients) == 0 {
			fmt.Println("No authorized clients. Add one: ab-pty client add <name> <sha256-fingerprint>")
			return
		}
		fmt.Printf("%-20s %-24s %-24s %s\n", "NAME", "ADDED", "LAST SEEN", "SHA-256")
		for _, c := range clients {
			seen := c.LastSeen
			if seen == "" {
				seen = "never"
			}
			fmt.Printf("%-20s %-24s %-24s %s\n", c.Name, c.AddedAt, seen, prettyFingerprint(c.Fingerprint))
		}
	case "revoke":
		if len(args) < 2 {
			fmt.Fprintln(os.Stderr, "usage: ab-pty client revoke <name|fingerprint>")
			os.Exit(2)
		}
		n, err := revokeAuthorizedClient(args[1])
		if err != nil {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
			os.Exit(1)
		}
		if n == 0 {
			fmt.Fprintf(os.Stderr, "No authorized client matched %q\n", args[1])
			os.Exit(1)
		}
		fmt.Printf("Revoked %d client certificate(s) matching %q — effective immediately, no restart needed.\n", n, args[1])
	default:
		fmt.Fprintf(os.Stderr, "unknown client subcommand: %s\n", args[0])
		os.Exit(2)
	}
}
