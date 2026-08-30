package main

import (
	"crypto/tls"
	"crypto/x509"
	"net/http"
	"net/http/httptest"
	"testing"
)

func TestProtectedExternalAPIRejectsOffAndOptionalModes(t *testing.T) {
	clearClients(t)
	_, fp := newClientCert(t)
	if err := addAuthorizedClient("operator", fp, ClientRoleOperator); err != nil {
		t.Fatal(err)
	}

	for _, mode := range []string{TLSModeOff, TLSModeOptional} {
		t.Run(mode, func(t *testing.T) {
			t.Setenv(tlsModeEnv, mode)
			req := httptest.NewRequest(http.MethodGet, "/api/pty", nil)
			req.RemoteAddr = "192.0.2.10:1234"
			req.TLS = &tls.ConnectionState{PeerCertificates: []*x509.Certificate{{Raw: []byte("not-used-before-mode-rejection")}}}
			rec := httptest.NewRecorder()
			buildMux().ServeHTTP(rec, req)
			if rec.Code != http.StatusForbidden {
				t.Fatalf("mode %s exposed protected API: %d %s", mode, rec.Code, rec.Body.String())
			}
		})
	}
}

func TestInSessionTokenIsLoopbackOnlyAndNotAdmin(t *testing.T) {
	clearClients(t)
	id := "auth-test-session"
	s := &Session{ID: id, Name: id, Alive: true}
	sessionsMu.Lock()
	sessions[id] = s
	sessionsMu.Unlock()
	t.Cleanup(func() {
		sessionsMu.Lock()
		delete(sessions, id)
		sessionsMu.Unlock()
	})
	token := deriveSessionToken(id)

	req := httptest.NewRequest(http.MethodGet, "/api/pty", nil)
	req.RemoteAddr = "127.0.0.1:1234"
	req.Header.Set("Authorization", "Bearer "+token)
	rec := httptest.NewRecorder()
	buildMux().ServeHTTP(rec, req)
	if rec.Code != http.StatusOK {
		t.Fatalf("live loopback session token rejected: %d %s", rec.Code, rec.Body.String())
	}

	req = httptest.NewRequest(http.MethodGet, "/api/pty", nil)
	req.RemoteAddr = "192.0.2.10:1234"
	req.Header.Set("Authorization", "Bearer "+token)
	rec = httptest.NewRecorder()
	buildMux().ServeHTTP(rec, req)
	if rec.Code != http.StatusUnauthorized {
		t.Fatalf("remote session token returned %d, want 401", rec.Code)
	}

	req = httptest.NewRequest(http.MethodGet, "/api/tls/clients", nil)
	req.RemoteAddr = "127.0.0.1:1234"
	req.Header.Set("Authorization", "Bearer "+token)
	rec = httptest.NewRecorder()
	buildMux().ServeHTTP(rec, req)
	if rec.Code != http.StatusForbidden {
		t.Fatalf("session token entered admin ACL: %d %s", rec.Code, rec.Body.String())
	}
}

func TestSessionTokenExpiresWithSessionAndDaemonSecret(t *testing.T) {
	id := "auth-expiry-session"
	s := &Session{ID: id, Name: id, Alive: true}
	sessionsMu.Lock()
	sessions[id] = s
	sessionsMu.Unlock()
	t.Cleanup(func() {
		sessionsMu.Lock()
		delete(sessions, id)
		sessionsMu.Unlock()
	})
	token := deriveSessionToken(id)
	if got, ok := validateSessionToken(token); !ok || got != id {
		t.Fatalf("fresh token invalid: id=%q ok=%v", got, ok)
	}
	s.setAlive(false)
	if _, ok := validateSessionToken(token); ok {
		t.Fatal("token for dead session remained valid")
	}

	s.setAlive(true)
	oldSecret := sessionAuthSecret
	sessionAuthSecret[0] ^= 0xff
	t.Cleanup(func() { sessionAuthSecret = oldSecret })
	if _, ok := validateSessionToken(token); ok {
		t.Fatal("token survived daemon secret rotation")
	}
}
