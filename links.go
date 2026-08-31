package main

// Daemon links make another daemon's PTY namespace available to sessions on
// this daemon. A link is deliberately identified by the peer daemon's TLS
// fingerprint, not by a relay route: the same machine may be visible through
// Home and Remote, but it is still one peer and cannot be linked to itself by
// choosing a different route.

import (
	"bufio"
	"bytes"
	"context"
	"crypto/tls"
	"crypto/x509"
	"database/sql"
	"encoding/pem"
	"fmt"
	"io"
	"net"
	"net/http"
	"net/url"
	"os"
	"strings"
	"time"
)

const (
	linkRequestBodyLimit  = 8 << 20
	linkResponseBodyLimit = 32 << 20
	linkRequestTimeout    = 30 * time.Second
)

type DaemonLink struct {
	Name            string `json:"name"`
	PeerFingerprint string `json:"peer_fingerprint"`
	RelayName       string `json:"relay_name"`
	RelayAddress    string `json:"relay_address"`
	State           string `json:"state"`
	LastSuccess     string `json:"last_success,omitempty"`
	LastError       string `json:"last_error,omitempty"`
	CreatedAt       string `json:"created_at"`
	UpdatedAt       string `json:"updated_at"`
}

func initDaemonLinksTable() {
	if _, err := db.Exec(`
		CREATE TABLE IF NOT EXISTS daemon_links (
			peer_fingerprint TEXT PRIMARY KEY,
			name             TEXT NOT NULL COLLATE NOCASE UNIQUE,
			relay_name       TEXT NOT NULL,
			state            TEXT NOT NULL DEFAULT 'pending',
			last_success     DATETIME,
			last_error       TEXT NOT NULL DEFAULT '',
			managed_client   INTEGER NOT NULL DEFAULT 0,
			previous_name    TEXT NOT NULL DEFAULT '',
			previous_role    TEXT NOT NULL DEFAULT '',
			created_at       DATETIME DEFAULT CURRENT_TIMESTAMP,
			updated_at       DATETIME DEFAULT CURRENT_TIMESTAMP
		)
	`); err != nil {
		panic(fmt.Errorf("create daemon_links: %w", err))
	}
}

func daemonFingerprint() (string, error) {
	if fp := strings.TrimSpace(tlsServerFingerprint); fp != "" {
		return normalizeFingerprint(fp)
	}
	data, err := os.ReadFile(tlsCertPath())
	if err != nil {
		return "", fmt.Errorf("read daemon certificate: %w", err)
	}
	cert, err := parseFirstCertificate(data)
	if err != nil {
		return "", fmt.Errorf("parse daemon certificate: %w", err)
	}
	return certFingerprint(cert.Raw), nil
}

func validateLinkName(name string) (string, error) {
	name = strings.TrimSpace(name)
	if name == "" {
		return "", fmt.Errorf("link name must not be empty")
	}
	if len(name) > 80 {
		return "", fmt.Errorf("link name is longer than 80 bytes")
	}
	if strings.ContainsAny(name, "/\r\n\x00") {
		return "", fmt.Errorf("link name must not contain '/', newlines, or NUL")
	}
	return name, nil
}

func relayForLink(name, address string) (RelayConfig, error) {
	name = strings.TrimSpace(name)
	address = strings.TrimSpace(address)
	if address != "" {
		normalized, err := normalizeRelayAddress(address)
		if err != nil {
			return RelayConfig{}, err
		}
		address = normalized
	}
	for _, cfg := range loadRelayConfigs() {
		if !cfg.Enabled {
			continue
		}
		if name != "" && cfg.Name == name {
			return cfg, nil
		}
		if address != "" && cfg.Address == address {
			return cfg, nil
		}
	}
	if name != "" {
		return RelayConfig{}, fmt.Errorf("relay route %q is not configured and enabled on this daemon", name)
	}
	return RelayConfig{}, fmt.Errorf("relay %q is not configured and enabled on this daemon", address)
}

func listDaemonLinks() ([]DaemonLink, error) {
	rows, err := db.Query(`
		SELECT name, peer_fingerprint, relay_name, state,
		       COALESCE(last_success, ''), last_error,
		       COALESCE(created_at, ''), COALESCE(updated_at, '')
		FROM daemon_links ORDER BY name COLLATE NOCASE
	`)
	if err != nil {
		return nil, err
	}
	defer rows.Close()
	links := []DaemonLink{}
	for rows.Next() {
		var item DaemonLink
		if err := rows.Scan(&item.Name, &item.PeerFingerprint, &item.RelayName,
			&item.State, &item.LastSuccess, &item.LastError,
			&item.CreatedAt, &item.UpdatedAt); err != nil {
			return nil, err
		}
		if cfg, err := relayForLink(item.RelayName, ""); err == nil {
			item.RelayAddress = cfg.Address
		}
		links = append(links, item)
	}
	return links, rows.Err()
}

func findDaemonLink(selector string) (DaemonLink, error) {
	selector = strings.TrimSpace(selector)
	if selector == "" {
		return DaemonLink{}, fmt.Errorf("link selector must not be empty")
	}
	links, err := listDaemonLinks()
	if err != nil {
		return DaemonLink{}, err
	}
	var normalized string
	if fp, err := normalizeFingerprint(selector); err == nil {
		normalized = fp
	}
	for _, link := range links {
		if strings.EqualFold(link.Name, selector) || (normalized != "" && link.PeerFingerprint == normalized) {
			return link, nil
		}
	}
	return DaemonLink{}, fmt.Errorf("daemon link %q not found", selector)
}

type upsertDaemonLinkRequest struct {
	Name            string `json:"name"`
	PeerFingerprint string `json:"peer_fingerprint"`
	RelayName       string `json:"relay_name"`
	RelayAddress    string `json:"relay_address"`
}

func upsertDaemonLink(body upsertDaemonLinkRequest) (DaemonLink, bool, error) {
	name, err := validateLinkName(body.Name)
	if err != nil {
		return DaemonLink{}, false, err
	}
	peer, err := normalizeFingerprint(body.PeerFingerprint)
	if err != nil {
		return DaemonLink{}, false, err
	}
	self, err := daemonFingerprint()
	if err != nil {
		return DaemonLink{}, false, err
	}
	if peer == self {
		return DaemonLink{}, false, fmt.Errorf("a daemon cannot link to itself, including through another relay")
	}
	relay, err := relayForLink(body.RelayName, body.RelayAddress)
	if err != nil {
		return DaemonLink{}, false, err
	}

	tx, err := db.Begin()
	if err != nil {
		return DaemonLink{}, false, err
	}
	rollback := func(cause error) (DaemonLink, bool, error) {
		_ = tx.Rollback()
		return DaemonLink{}, false, cause
	}

	var existingName string
	var managed int
	var previousName, previousRole string
	err = tx.QueryRow(`SELECT name, managed_client, previous_name, previous_role FROM daemon_links WHERE peer_fingerprint = ?`, peer).
		Scan(&existingName, &managed, &previousName, &previousRole)
	created := err == sql.ErrNoRows
	if err != nil && err != sql.ErrNoRows {
		return rollback(err)
	}
	if created {
		var oldName, oldRole string
		err = tx.QueryRow(`SELECT name, role FROM tls_clients WHERE fingerprint = ?`, peer).Scan(&oldName, &oldRole)
		switch err {
		case sql.ErrNoRows:
			managed = 1
		case nil:
			previousName, previousRole = oldName, oldRole
		default:
			return rollback(err)
		}
	}

	clientName := previousName
	if managed != 0 || clientName == "" {
		clientName = "daemon-link:" + name
	}
	role := previousRole
	if role == "" || role == ClientRoleReadOnly {
		role = ClientRoleOperator
	}
	if _, err := tx.Exec(`
		INSERT INTO tls_clients (fingerprint, name, role, added_at)
		VALUES (?, ?, ?, CURRENT_TIMESTAMP)
		ON CONFLICT(fingerprint) DO UPDATE SET name=excluded.name, role=excluded.role
	`, peer, clientName, role); err != nil {
		return rollback(err)
	}
	if _, err := tx.Exec(`
		INSERT INTO daemon_links
			(peer_fingerprint, name, relay_name, state, last_error, managed_client, previous_name, previous_role, updated_at)
		VALUES (?, ?, ?, 'pending', '', ?, ?, ?, CURRENT_TIMESTAMP)
		ON CONFLICT(peer_fingerprint) DO UPDATE SET
			name=excluded.name, relay_name=excluded.relay_name,
			state='pending', last_error='', managed_client=excluded.managed_client,
			previous_name=excluded.previous_name, previous_role=excluded.previous_role,
			updated_at=CURRENT_TIMESTAMP
	`, peer, name, relay.Name, managed, previousName, previousRole); err != nil {
		return rollback(err)
	}
	if err := tx.Commit(); err != nil {
		return DaemonLink{}, false, err
	}
	link, err := findDaemonLink(peer)
	return link, created, err
}

func deleteDaemonLink(selector string) (DaemonLink, error) {
	link, err := findDaemonLink(selector)
	if err != nil {
		return DaemonLink{}, err
	}
	tx, err := db.Begin()
	if err != nil {
		return DaemonLink{}, err
	}
	var managed int
	var previousName, previousRole string
	if err := tx.QueryRow(`SELECT managed_client, previous_name, previous_role FROM daemon_links WHERE peer_fingerprint = ?`, link.PeerFingerprint).
		Scan(&managed, &previousName, &previousRole); err != nil {
		_ = tx.Rollback()
		return DaemonLink{}, err
	}
	if _, err := tx.Exec(`DELETE FROM daemon_links WHERE peer_fingerprint = ?`, link.PeerFingerprint); err != nil {
		_ = tx.Rollback()
		return DaemonLink{}, err
	}
	if managed != 0 {
		if _, err := tx.Exec(`DELETE FROM tls_clients WHERE fingerprint = ?`, link.PeerFingerprint); err != nil {
			_ = tx.Rollback()
			return DaemonLink{}, err
		}
	} else if previousName != "" && previousRole != "" {
		if _, err := tx.Exec(`UPDATE tls_clients SET name = ?, role = ? WHERE fingerprint = ?`, previousName, previousRole, link.PeerFingerprint); err != nil {
			_ = tx.Rollback()
			return DaemonLink{}, err
		}
	}
	if err := tx.Commit(); err != nil {
		return DaemonLink{}, err
	}
	return link, nil
}

func markDaemonLink(peer, state, lastError string, success bool) {
	if success {
		_, _ = db.Exec(`UPDATE daemon_links SET state=?, last_error='', last_success=CURRENT_TIMESTAMP, updated_at=CURRENT_TIMESTAMP WHERE peer_fingerprint=?`, state, peer)
		return
	}
	_, _ = db.Exec(`UPDATE daemon_links SET state=?, last_error=?, updated_at=CURRENT_TIMESTAMP WHERE peer_fingerprint=?`, state, lastError, peer)
}

func handleDaemonLinks(w http.ResponseWriter, r *http.Request) {
	if allowOptions(w, r, "GET, POST, DELETE, OPTIONS") {
		return
	}
	target := strings.Trim(strings.TrimPrefix(r.URL.Path, "/api/links"), "/")
	switch {
	case r.Method == http.MethodGet && target == "":
		links, err := listDaemonLinks()
		if err != nil {
			writeError(w, http.StatusInternalServerError, err.Error())
			return
		}
		self, _ := daemonFingerprint()
		writeJSON(w, 0, map[string]interface{}{"self_fingerprint": self, "links": links})
	case r.Method == http.MethodPost && target == "":
		var body upsertDaemonLinkRequest
		if err := decodeClientAdminBody(w, r, &body); err != nil {
			writeError(w, http.StatusBadRequest, "expected {name, peer_fingerprint, relay_name or relay_address}")
			return
		}
		link, created, err := upsertDaemonLink(body)
		if err != nil {
			writeError(w, http.StatusBadRequest, err.Error())
			return
		}
		status := http.StatusOK
		if created {
			status = http.StatusCreated
		}
		writeJSON(w, status, link)
	case r.Method == http.MethodDelete && target != "":
		selector, err := url.PathUnescape(target)
		if err != nil {
			writeError(w, http.StatusBadRequest, "invalid link selector")
			return
		}
		link, err := deleteDaemonLink(selector)
		if err != nil {
			writeError(w, http.StatusNotFound, err.Error())
			return
		}
		writeJSON(w, 0, map[string]interface{}{"deleted": link.PeerFingerprint, "name": link.Name})
	default:
		writeError(w, http.StatusMethodNotAllowed, "Method not allowed")
	}
}

// handleDaemonLinksAdmin keeps GET readable by normal clients. Creating a
// peer is part of ordinary PTY operation, so an operator may mutate links;
// this introduces no separate link-specific role.
func handleDaemonLinksAdmin(w http.ResponseWriter, r *http.Request) {
	access := accessRead
	if r.Method != http.MethodGet && r.Method != http.MethodOptions {
		access = accessOperate
	}
	requireDaemonAccess(access, handleDaemonLinks)(w, r)
}

func validateRemotePTYPath(raw string) (string, error) {
	if len(raw) > 4096 {
		return "", fmt.Errorf("remote path is too long")
	}
	u, err := url.ParseRequestURI(raw)
	if err != nil || u.IsAbs() || u.Host != "" {
		return "", fmt.Errorf("invalid remote path")
	}
	if u.Path != "/api/pty" && !strings.HasPrefix(u.Path, "/api/pty/") {
		return "", fmt.Errorf("remote links expose only /api/pty")
	}
	return u.RequestURI(), nil
}

func dialLinkedDaemon(ctx context.Context, link DaemonLink) (net.Conn, error) {
	relay, err := relayForLink(link.RelayName, link.RelayAddress)
	if err != nil {
		return nil, err
	}
	dialer := &net.Dialer{Timeout: relayDialTimeout}
	conn, err := dialer.DialContext(ctx, "tcp", relay.Address)
	if err != nil {
		return nil, fmt.Errorf("dial relay %s: %w", relay.Address, err)
	}
	fail := func(cause error) (net.Conn, error) {
		_ = conn.Close()
		return nil, cause
	}
	_ = conn.SetDeadline(time.Now().Add(relayDialTimeout))
	if _, err := fmt.Fprintf(conn, "%s CONNECT %s\n", relayProtoMagic, link.PeerFingerprint); err != nil {
		return fail(fmt.Errorf("write relay CONNECT: %w", err))
	}
	line, err := relayReadLine(conn, relayMaxLine)
	if err != nil {
		return fail(fmt.Errorf("read relay CONNECT reply: %w", err))
	}
	fields := strings.Fields(line)
	if len(fields) < 2 || fields[0] != relayProtoMagic || strings.ToUpper(fields[1]) != "OK" {
		return fail(fmt.Errorf("relay refused peer %s: %s", link.Name, line))
	}

	identity, err := tls.LoadX509KeyPair(tlsCertPath(), tlsKeyPath())
	if err != nil {
		return fail(fmt.Errorf("load daemon peer identity: %w", err))
	}
	want := link.PeerFingerprint
	tlsConn := tls.Client(conn, &tls.Config{
		Certificates:       []tls.Certificate{identity},
		MinVersion:         tls.VersionTLS12,
		InsecureSkipVerify: true,
		VerifyConnection: func(cs tls.ConnectionState) error {
			if len(cs.PeerCertificates) == 0 {
				return fmt.Errorf("peer presented no certificate")
			}
			got := certFingerprint(cs.PeerCertificates[0].Raw)
			if got != want {
				return fmt.Errorf("peer certificate %s does not match linked daemon %s", got, want)
			}
			return nil
		},
	})
	if err := tlsConn.HandshakeContext(ctx); err != nil {
		return fail(fmt.Errorf("peer TLS handshake: %w", err))
	}
	_ = tlsConn.SetDeadline(time.Time{})
	return tlsConn, nil
}

func requestLinkedDaemon(ctx context.Context, link DaemonLink, method, path string, body []byte) (int, http.Header, []byte, error) {
	path, err := validateRemotePTYPath(path)
	if err != nil {
		return 0, nil, nil, err
	}
	switch method {
	case http.MethodGet, http.MethodPost, http.MethodPatch, http.MethodDelete:
	default:
		return 0, nil, nil, fmt.Errorf("unsupported remote method %q", method)
	}
	conn, err := dialLinkedDaemon(ctx, link)
	if err != nil {
		markDaemonLink(link.PeerFingerprint, "offline", err.Error(), false)
		return 0, nil, nil, err
	}
	defer conn.Close()
	req, err := http.NewRequestWithContext(ctx, method, "https://daemon"+path, bytes.NewReader(body))
	if err != nil {
		return 0, nil, nil, err
	}
	req.Header.Set("Content-Type", "application/json")
	req.Close = true
	if err := req.Write(conn); err != nil {
		markDaemonLink(link.PeerFingerprint, "broken", err.Error(), false)
		return 0, nil, nil, fmt.Errorf("write peer request: %w", err)
	}
	resp, err := http.ReadResponse(bufio.NewReader(conn), req)
	if err != nil {
		markDaemonLink(link.PeerFingerprint, "broken", err.Error(), false)
		return 0, nil, nil, fmt.Errorf("read peer response: %w", err)
	}
	defer resp.Body.Close()
	data, err := io.ReadAll(io.LimitReader(resp.Body, linkResponseBodyLimit+1))
	if err != nil {
		return 0, nil, nil, err
	}
	if len(data) > linkResponseBodyLimit {
		return 0, nil, nil, fmt.Errorf("peer response exceeds %d bytes", linkResponseBodyLimit)
	}
	if resp.StatusCode >= 200 && resp.StatusCode < 300 {
		markDaemonLink(link.PeerFingerprint, "active", "", true)
	} else {
		markDaemonLink(link.PeerFingerprint, "broken", fmt.Sprintf("HTTP %d", resp.StatusCode), false)
	}
	return resp.StatusCode, resp.Header.Clone(), data, nil
}

// A linked daemon arrives with a certificate principal, never a local session
// principal. Requiring SessionID here makes forwarding exactly one hop: a
// daemon can serve a request from its peer, but cannot recursively ask that
// peer to forward it again.
func handleDaemonLinkProxy(w http.ResponseWriter, r *http.Request) {
	principal, ok := principalFromRequest(r)
	if !ok || principal.SessionID == "" {
		writeError(w, http.StatusForbidden, "remote daemon requests cannot be forwarded again")
		return
	}
	if r.Method != http.MethodPost {
		writeError(w, http.StatusMethodNotAllowed, "Method not allowed")
		return
	}
	target := strings.Trim(strings.TrimPrefix(r.URL.Path, "/api/link-proxy/"), "/")
	selector, err := url.PathUnescape(target)
	if err != nil || selector == "" {
		writeError(w, http.StatusBadRequest, "a daemon link is required")
		return
	}
	link, err := findDaemonLink(selector)
	if err != nil {
		writeError(w, http.StatusNotFound, err.Error())
		return
	}
	method := strings.ToUpper(strings.TrimSpace(r.URL.Query().Get("method")))
	path, err := validateRemotePTYPath(r.URL.Query().Get("path"))
	if err != nil {
		writeError(w, http.StatusBadRequest, err.Error())
		return
	}
	body, err := io.ReadAll(http.MaxBytesReader(w, r.Body, linkRequestBodyLimit))
	if err != nil {
		writeError(w, http.StatusBadRequest, "request body is too large")
		return
	}
	ctx, cancel := context.WithTimeout(r.Context(), linkRequestTimeout)
	defer cancel()
	status, headers, data, err := requestLinkedDaemon(ctx, link, method, path, body)
	if err != nil {
		writeError(w, http.StatusBadGateway, err.Error())
		return
	}
	if contentType := headers.Get("Content-Type"); contentType != "" {
		w.Header().Set("Content-Type", contentType)
	}
	w.WriteHeader(status)
	_, _ = w.Write(data)
}

func linkedSessionRequest(link, method, path string, body []byte) ([]byte, error) {
	proxyPath := "/api/link-proxy/" + url.PathEscape(link) + "?method=" + url.QueryEscape(method) + "&path=" + url.QueryEscape(path)
	return cliRequest(http.MethodPost, proxyPath, body)
}

// Kept tiny and local because encoding/pem is otherwise only needed here.
func parseFirstCertificate(pemBytes []byte) (*x509.Certificate, error) {
	block, _ := pem.Decode(pemBytes)
	if block == nil || block.Type != "CERTIFICATE" {
		return nil, fmt.Errorf("certificate PEM block not found")
	}
	return x509.ParseCertificate(block.Bytes)
}
