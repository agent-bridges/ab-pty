package main

import (
	"crypto/tls"
	"database/sql"
	"encoding/json"
	"fmt"
	"net/http"
	"strings"
	"testing"
)

func clearClients(t *testing.T) {
	t.Helper()
	initTestDB()
	initTLSClientsTable()
	if _, err := db.Exec(`DELETE FROM tls_clients`); err != nil {
		t.Fatalf("clearing tls_clients: %v", err)
	}
}

func call(t *testing.T, rt *relayTestServer, cert tls.Certificate, method, path, body string, authorization string) (int, map[string]interface{}) {
	t.Helper()
	req, err := http.NewRequest(method, "https://relay"+path, strings.NewReader(body))
	if err != nil {
		t.Fatal(err)
	}
	if authorization != "" {
		req.Header.Set("Authorization", authorization)
	}
	req.Header.Set("Content-Type", "application/json")
	var certs []tls.Certificate
	if cert.Certificate != nil {
		certs = []tls.Certificate{cert}
	}
	resp, err := rt.client(certs).Do(req)
	if err != nil {
		return 0, map[string]interface{}{"transport_error": err.Error()}
	}
	defer resp.Body.Close()
	out := map[string]interface{}{}
	_ = json.NewDecoder(resp.Body).Decode(&out)
	return resp.StatusCode, out
}

func TestAdminClientEnrollsExplicitRole(t *testing.T) {
	clearClients(t)
	rt := newRelayTestServer(t)
	pair, fp := newClientCert(t)
	if err := addAuthorizedClient("pixel", fp, ClientRoleAdmin); err != nil {
		t.Fatal(err)
	}
	_, newFP := newClientCert(t)

	status, body := call(t, rt, pair, http.MethodPost, "/api/tls/clients",
		fmt.Sprintf(`{"name":"spare","fingerprint":%q,"role":"read-only"}`, newFP), "")
	if status != http.StatusCreated {
		t.Fatalf("want 201, got %d: %v", status, body)
	}
	client, ok := lookupAuthorizedClient(newFP)
	if !ok || client.Name != "spare" || client.Role != ClientRoleReadOnly {
		t.Fatalf("unexpected stored client: %+v ok=%v", client, ok)
	}
}

func TestOperatorCannotManageClientACL(t *testing.T) {
	clearClients(t)
	rt := newRelayTestServer(t)
	pair, fp := newClientCert(t)
	if err := addAuthorizedClient("laptop", fp, ClientRoleOperator); err != nil {
		t.Fatal(err)
	}

	for _, method := range []string{http.MethodGet, http.MethodPost, http.MethodPatch, http.MethodDelete} {
		path := "/api/tls/clients"
		if method == http.MethodPatch || method == http.MethodDelete {
			path += "/someone"
		}
		status, body := call(t, rt, pair, method, path, `{}`, "")
		if status != http.StatusForbidden {
			t.Fatalf("%s ACL with operator returned %d: %v", method, status, body)
		}
	}
}

func TestAdminChangesRoleImmediately(t *testing.T) {
	clearClients(t)
	rt := newRelayTestServer(t)
	adminPair, adminFP := newClientCert(t)
	if err := addAuthorizedClient("admin-phone", adminFP, ClientRoleAdmin); err != nil {
		t.Fatal(err)
	}
	_, targetFP := newClientCert(t)
	if err := addAuthorizedClient("viewer", targetFP, ClientRoleReadOnly); err != nil {
		t.Fatal(err)
	}

	status, body := call(t, rt, adminPair, http.MethodPatch, "/api/tls/clients/viewer", `{"role":"operator"}`, "")
	if status != http.StatusOK {
		t.Fatalf("role change: %d %v", status, body)
	}
	client, ok := lookupAuthorizedClient(targetFP)
	if !ok || client.Role != ClientRoleOperator {
		t.Fatalf("role was not changed: %+v ok=%v", client, ok)
	}
}

func TestEnrollmentRequiresRoleAndRejectsUnknownFields(t *testing.T) {
	clearClients(t)
	rt := newRelayTestServer(t)
	pair, fp := newClientCert(t)
	if err := addAuthorizedClient("pixel", fp, ClientRoleAdmin); err != nil {
		t.Fatal(err)
	}
	_, newFP := newClientCert(t)

	for _, body := range []string{
		fmt.Sprintf(`{"name":"x","fingerprint":%q}`, newFP),
		fmt.Sprintf(`{"name":"x","fingerprint":%q,"role":"owner"}`, newFP),
		fmt.Sprintf(`{"name":"x","fingerprint":%q,"role":"operator","jwt":"secret"}`, newFP),
		fmt.Sprintf(`{"name":"x","fingerprint":%q,"role":"operator"} {}`, newFP),
	} {
		status, response := call(t, rt, pair, http.MethodPost, "/api/tls/clients", body, "")
		if status != http.StatusBadRequest {
			t.Fatalf("want 400 for %s, got %d: %v", body, status, response)
		}
	}
}

func TestExternalAuthorizationHeaderNeverFallsBackToCertificate(t *testing.T) {
	clearClients(t)
	rt := newRelayTestServer(t)
	pair, fp := newClientCert(t)
	if err := addAuthorizedClient("pixel", fp, ClientRoleAdmin); err != nil {
		t.Fatal(err)
	}

	status, _ := call(t, rt, pair, http.MethodGet, "/api/tls/clients", "", "Bearer legacy-daemon-jwt")
	if status != http.StatusUnauthorized {
		t.Fatalf("external Authorization must be rejected without mTLS fallback, got %d", status)
	}
}

func TestReadOnlyRoleCannotMutateOrAttachInteractiveWS(t *testing.T) {
	clearClients(t)
	rt := newRelayTestServer(t)
	pair, fp := newClientCert(t)
	if err := addAuthorizedClient("viewer", fp, ClientRoleReadOnly); err != nil {
		t.Fatal(err)
	}

	if status, body := call(t, rt, pair, http.MethodGet, "/api/pty", "", ""); status != http.StatusOK {
		t.Fatalf("read-only GET failed: %d %v", status, body)
	}
	if status, _ := call(t, rt, pair, http.MethodPost, "/api/board/items", `{}`, ""); status != http.StatusForbidden {
		t.Fatalf("read-only mutation returned %d", status)
	}
	if status, _ := call(t, rt, pair, http.MethodGet, "/ws", "", ""); status != http.StatusForbidden {
		t.Fatalf("read-only interactive websocket returned %d", status)
	}
}

func TestClientRoleValidation(t *testing.T) {
	for _, role := range []string{ClientRoleReadOnly, ClientRoleOperator, ClientRoleAdmin} {
		if got, err := normalizeClientRole(role); err != nil || got != role {
			t.Fatalf("valid role %q: got=%q err=%v", role, got, err)
		}
	}
	for _, role := range []string{"", "owner", "write", "*"} {
		if _, err := normalizeClientRole(role); err == nil {
			t.Fatalf("invalid role %q accepted", role)
		}
	}
}

func TestLegacyClientRowsMigrateToOperatorWithoutAdminElevation(t *testing.T) {
	legacyDB, err := sql.Open("sqlite3", t.TempDir()+"/legacy.db")
	if err != nil {
		t.Fatal(err)
	}
	defer legacyDB.Close()
	if _, err := legacyDB.Exec(`CREATE TABLE tls_clients (
		fingerprint TEXT PRIMARY KEY,
		name TEXT NOT NULL,
		added_at DATETIME DEFAULT CURRENT_TIMESTAMP,
		last_seen DATETIME
	)`); err != nil {
		t.Fatal(err)
	}
	fp := strings.Repeat("ab", 32)
	if _, err := legacyDB.Exec(`INSERT INTO tls_clients(fingerprint,name) VALUES (?,?)`, fp, "old-phone"); err != nil {
		t.Fatal(err)
	}
	if err := ensureTLSClientsTable(legacyDB); err != nil {
		t.Fatal(err)
	}
	var role string
	if err := legacyDB.QueryRow(`SELECT role FROM tls_clients WHERE fingerprint=?`, fp).Scan(&role); err != nil {
		t.Fatal(err)
	}
	if role != ClientRoleOperator {
		t.Fatalf("legacy row migrated to %q, want operator", role)
	}
}
