package main

// Who may change this machine's allow-list.
//
// The endpoint under test is the one that lets a person add a second phone
// without an SSH session, and it is also the one place in the whole system
// where a mistake hands out durable access to a machine. So the tests here
// are mostly about refusals: every path that must not reach the table, tried.

import (
	"crypto/tls"
	"encoding/json"
	"fmt"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/golang-jwt/jwt/v5"
)

func clearClients(t *testing.T) {
	t.Helper()
	initTestDB()
	initTLSClientsTable()
	if _, err := db.Exec(`DELETE FROM tls_clients`); err != nil {
		t.Fatalf("clearing tls_clients: %v", err)
	}
}

// jwtFor makes the daemon accept a bearer token in these tests. The endpoint
// demands one on top of the certificate, so every test needs it and none of
// them are about it.
func jwtFor(t *testing.T) string {
	t.Helper()
	secret := strings.Repeat("a", 64)
	path := filepath.Join(t.TempDir(), ".jwt-secret")
	if err := os.WriteFile(path, []byte(secret), 0o600); err != nil {
		t.Fatal(err)
	}
	t.Setenv(jwtSecretPathEnv, path)
	// The cache is process-wide and holds whatever an earlier test left in
	// it; forcing a reload is the only way this one's secret is the one the
	// handler checks against.
	jwtCache.mu.Lock()
	jwtCache.secret = ""
	jwtCache.lastLoad = time.Time{}
	jwtCache.mu.Unlock()
	t.Cleanup(func() {
		jwtCache.mu.Lock()
		jwtCache.secret = ""
		jwtCache.lastLoad = time.Time{}
		jwtCache.mu.Unlock()
	})
	token := jwt.NewWithClaims(jwt.SigningMethodHS256, jwt.MapClaims{
		"sub": "ab-pty-test",
		"iat": time.Now().Unix(),
		"exp": time.Now().Add(time.Hour).Unix(),
	})
	signed, err := token.SignedString([]byte(secret))
	if err != nil {
		t.Fatalf("minting a test JWT: %v", err)
	}
	return signed
}

// call performs one request through the relay listener — i.e. over mutual TLS
// with a client certificate, which is the only way this endpoint is reachable
// at all.
func call(t *testing.T, rt *relayTestServer, cert tls.Certificate, token, method, path, body string) (int, map[string]interface{}) {
	t.Helper()
	var reader *strings.Reader
	if body == "" {
		reader = strings.NewReader("")
	} else {
		reader = strings.NewReader(body)
	}
	req, err := http.NewRequest(method, "https://relay"+path, reader)
	if err != nil {
		t.Fatal(err)
	}
	if token != "" {
		req.Header.Set("Authorization", "Bearer "+token)
	}
	req.Header.Set("Content-Type", "application/json")
	var certs []tls.Certificate
	if cert.Certificate != nil {
		certs = []tls.Certificate{cert}
	}
	resp, err := rt.client(certs).Do(req)
	if err != nil {
		// A handshake the daemon aborted is a legitimate outcome for some
		// of these; the caller checks the status only when there is one.
		return 0, map[string]interface{}{"transport_error": err.Error()}
	}
	defer resp.Body.Close()
	out := map[string]interface{}{}
	_ = json.NewDecoder(resp.Body).Decode(&out)
	return resp.StatusCode, out
}

// The feature: a device this machine already admits enrols another one, over
// the connection it is already holding, with nobody logging into anything.
func TestAuthorizedClientEnrolsAnotherDevice(t *testing.T) {
	clearClients(t)
	rt := newRelayTestServer(t)
	token := jwtFor(t)

	pair, fp := newClientCert(t)
	if err := addAuthorizedClient("pixel", fp); err != nil {
		t.Fatal(err)
	}
	_, newFP := newClientCert(t)

	status, body := call(t, rt, pair, token, "POST", "/api/tls/clients",
		fmt.Sprintf(`{"name":"spare","fingerprint":%q}`, newFP))
	if status != http.StatusCreated {
		t.Fatalf("want 201, got %d: %v", status, body)
	}
	if body["added_by"] != "pixel" {
		t.Errorf("the answer should name who granted it, got %v", body["added_by"])
	}
	if name, ok := lookupAuthorizedClient(newFP); !ok || name != "spare" {
		t.Fatalf("the new device is not on the allow-list: %q ok=%v", name, ok)
	}
}

// The new device really is in, not merely recorded: it completes a handshake
// the machine would have aborted a moment earlier. That is the whole promise.
func TestADeviceEnrolledThroughTheApiCanThenConnect(t *testing.T) {
	clearClients(t)
	rt := newRelayTestServer(t)
	token := jwtFor(t)

	pair, fp := newClientCert(t)
	if err := addAuthorizedClient("pixel", fp); err != nil {
		t.Fatal(err)
	}
	newPair, newFP := newClientCert(t)

	// Before: refused at the handshake.
	if status, _ := call(t, rt, newPair, token, "GET", "/health", ""); status != 0 {
		t.Fatalf("an unenrolled device reached the daemon (status %d)", status)
	}

	if status, body := call(t, rt, pair, token, "POST", "/api/tls/clients",
		fmt.Sprintf(`{"name":"spare","fingerprint":%q}`, newFP)); status != http.StatusCreated {
		t.Fatalf("enrolling: %d %v", status, body)
	}

	// After: in, with no restart — the allow-list is read per handshake.
	if status, body := call(t, rt, newPair, token, "GET", "/health", ""); status != http.StatusOK {
		t.Fatalf("the newly enrolled device still cannot connect: %d %v", status, body)
	}
}

// The refusal that matters most: a certificate the machine does not know
// cannot enrol anything — and does not even get to the handler, because the
// machine aborts its handshake. Belt and braces are both checked, because the
// braces (the handler check) are what protects a listener configured
// differently later.
func TestUnknownCertificateCannotEnrolAnything(t *testing.T) {
	clearClients(t)
	rt := newRelayTestServer(t)
	token := jwtFor(t)
	strangerPair, _ := newClientCert(t)
	_, victimFP := newClientCert(t)

	status, _ := call(t, rt, strangerPair, token, "POST", "/api/tls/clients",
		fmt.Sprintf(`{"name":"intruder","fingerprint":%q}`, victimFP))
	if status == http.StatusCreated {
		t.Fatal("a certificate this machine has never authorised enrolled another one")
	}
	if _, ok := lookupAuthorizedClient(victimFP); ok {
		t.Fatal("the allow-list gained a row from an unauthorized caller")
	}

	// And the handler's own check, exercised directly, so the guarantee does
	// not rest solely on the listener's configuration.
	rec := httptest.NewRecorder()
	req := httptest.NewRequest("POST", "/api/tls/clients", strings.NewReader(`{"name":"x","fingerprint":"`+victimFP+`"}`))
	req.RemoteAddr = "relay/9"
	requireEnrolledClient(handleTLSClients)(rec, req)
	if rec.Code != http.StatusForbidden {
		t.Fatalf("a request with no client certificate should be refused, got %d: %s", rec.Code, rec.Body)
	}
	var body map[string]string
	_ = json.Unmarshal(rec.Body.Bytes(), &body)
	if body["code"] != "no_client_certificate" {
		t.Errorf("the refusal should say which of the two problems it is, got %q", body["code"])
	}
}

// The loopback exemption exists so the in-session `ab` CLI and /api/hook keep
// working under mode=required. It hands the caller no certificate, so it must
// buy nothing here: an allow-list is not editable by whatever happens to be
// running on the machine over HTTP.
func TestLoopbackExemptionIsNoWayIntoTheAllowList(t *testing.T) {
	clearClients(t)
	t.Setenv(tlsModeEnv, TLSModeRequired)
	t.Setenv(tlsAllowLoopbackEnv, "1")

	rec := httptest.NewRecorder()
	req := httptest.NewRequest("POST", "/api/tls/clients", strings.NewReader(`{"name":"x","fingerprint":"`+strings.Repeat("ab", 32)+`"}`))
	req.RemoteAddr = "127.0.0.1:5555"
	requireEnrolledClient(handleTLSClients)(rec, req)

	if rec.Code != http.StatusForbidden {
		t.Fatalf("a loopback caller with no certificate was allowed to change the allow-list: %d %s", rec.Code, rec.Body)
	}
	var body map[string]string
	_ = json.Unmarshal(rec.Body.Bytes(), &body)
	// The exemption downgrades this connection to optional, and optional is
	// refused before the certificate is even looked for.
	if body["code"] != "tls_mode" {
		t.Errorf("want the mode refusal for an exempted loopback caller, got %q (%s)", body["code"], rec.Body)
	}
	if _, ok := lookupAuthorizedClient(strings.Repeat("ab", 32)); ok {
		t.Fatal("the allow-list gained a row from a loopback caller")
	}
}

// In `optional` every stranger's certificate is tolerated, so being on the
// allow-list proves nothing about who else can reach this endpoint. The
// endpoint is therefore closed in that mode, whoever is asking.
func TestOptionalModeClosesTheEndpointEntirely(t *testing.T) {
	clearClients(t)
	t.Setenv(tlsModeEnv, TLSModeOptional)
	t.Setenv(tlsAllowLoopbackEnv, "")
	_, fp := newClientCert(t)
	if err := addAuthorizedClient("pixel", fp); err != nil {
		t.Fatal(err)
	}

	rec := httptest.NewRecorder()
	req := httptest.NewRequest("GET", "/api/tls/clients", nil)
	req.RemoteAddr = "10.0.0.9:5555"
	requireEnrolledClient(handleTLSClients)(rec, req)
	if rec.Code != http.StatusForbidden {
		t.Fatalf("want the endpoint closed in optional mode, got %d", rec.Code)
	}
	var body map[string]string
	_ = json.Unmarshal(rec.Body.Bytes(), &body)
	if body["code"] != "tls_mode" || body["tls_mode"] != TLSModeOptional {
		t.Errorf("the refusal should name the mode so the app can say what to change: %s", rec.Body)
	}
}

// A daemon whose own port is plain HTTP is the ordinary relay deployment. The
// connection through the relay always demanded a certificate, so the endpoint
// has to be open on it — a check that consulted the process-wide mode would
// refuse the only path the app actually uses.
func TestRelayConnectionCountsAsRequiredEvenWhenTheDaemonIsOff(t *testing.T) {
	t.Setenv(tlsModeEnv, TLSModeOff)
	req := httptest.NewRequest("GET", "/api/tls/clients", nil)
	req.RemoteAddr = "relay/3"
	if got := effectiveTLSMode(req); got != TLSModeRequired {
		t.Errorf("a relay connection is always mutual TLS, got mode %q", got)
	}
	req.RemoteAddr = "192.168.1.5:4444"
	if got := effectiveTLSMode(req); got != TLSModeOff {
		t.Errorf("the network listener follows the environment, got %q", got)
	}
}

// Revoking the certificate the request arrived on is never what somebody
// meant, and it is not undoable from the app.
func TestADeviceCannotRevokeItself(t *testing.T) {
	clearClients(t)
	rt := newRelayTestServer(t)
	token := jwtFor(t)
	pair, fp := newClientCert(t)
	if err := addAuthorizedClient("pixel", fp); err != nil {
		t.Fatal(err)
	}

	for _, target := range []string{"pixel", fp} {
		status, body := call(t, rt, pair, token, "DELETE", "/api/tls/clients/"+target, "")
		if status != http.StatusForbidden {
			t.Fatalf("revoking %q (itself) returned %d: %v", target, status, body)
		}
		if body["code"] != "self_revoke" {
			t.Errorf("the refusal should be nameable by the app, got %v", body["code"])
		}
	}
	if _, ok := lookupAuthorizedClient(fp); !ok {
		t.Fatal("the caller revoked itself anyway")
	}
}

// Revoking somebody else is an ordinary operation, and it bites at once: the
// allow-list is read per handshake, so the next connection from that device
// does not complete.
func TestRevokingAnotherDeviceTakesEffectImmediately(t *testing.T) {
	clearClients(t)
	rt := newRelayTestServer(t)
	token := jwtFor(t)
	pair, fp := newClientCert(t)
	if err := addAuthorizedClient("pixel", fp); err != nil {
		t.Fatal(err)
	}
	oldPair, oldFP := newClientCert(t)
	if err := addAuthorizedClient("lost-phone", oldFP); err != nil {
		t.Fatal(err)
	}
	if status, _ := call(t, rt, oldPair, token, "GET", "/health", ""); status != http.StatusOK {
		t.Fatal("the device to be revoked could not connect in the first place")
	}

	status, body := call(t, rt, pair, token, "DELETE", "/api/tls/clients/lost-phone", "")
	if status != http.StatusOK {
		t.Fatalf("revoking: %d %v", status, body)
	}
	if status, _ := call(t, rt, oldPair, token, "GET", "/health", ""); status != 0 {
		t.Fatalf("a revoked device still reached the daemon (status %d)", status)
	}
}

// The list is what the app draws, and the one thing it cannot work out for
// itself is which row is this phone.
func TestListMarksTheCallersOwnRow(t *testing.T) {
	clearClients(t)
	rt := newRelayTestServer(t)
	token := jwtFor(t)
	pair, fp := newClientCert(t)
	if err := addAuthorizedClient("pixel", fp); err != nil {
		t.Fatal(err)
	}
	_, otherFP := newClientCert(t)
	if err := addAuthorizedClient("laptop", otherFP); err != nil {
		t.Fatal(err)
	}

	status, body := call(t, rt, pair, token, "GET", "/api/tls/clients", "")
	if status != http.StatusOK {
		t.Fatalf("listing: %d %v", status, body)
	}
	rows, _ := body["clients"].([]interface{})
	if len(rows) != 2 {
		t.Fatalf("expected both rows, got %v", body)
	}
	seen := map[string]bool{}
	for _, raw := range rows {
		row := raw.(map[string]interface{})
		seen[row["name"].(string)] = row["self"].(bool)
	}
	if !seen["pixel"] || seen["laptop"] {
		t.Errorf("self should mark exactly the caller: %v", seen)
	}
}

func TestEnrolmentRefusesRubbish(t *testing.T) {
	clearClients(t)
	rt := newRelayTestServer(t)
	token := jwtFor(t)
	pair, fp := newClientCert(t)
	if err := addAuthorizedClient("pixel", fp); err != nil {
		t.Fatal(err)
	}

	for _, tc := range []struct{ name, body string }{
		{"not a fingerprint", `{"name":"x","fingerprint":"hello"}`},
		{"half a fingerprint", `{"name":"x","fingerprint":"abcd"}`},
		{"no name", `{"name":"  ","fingerprint":"` + strings.Repeat("ab", 32) + `"}`},
		{"not json", `hello`},
	} {
		t.Run(tc.name, func(t *testing.T) {
			if status, body := call(t, rt, pair, token, "POST", "/api/tls/clients", tc.body); status != http.StatusBadRequest {
				t.Errorf("want 400, got %d: %v", status, body)
			}
		})
	}
}
