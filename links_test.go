package main

import (
	"context"
	"net/http"
	"net/http/httptest"
	"path/filepath"
	"strings"
	"testing"
)

func prepareLinkTest(t *testing.T) (selfFP string) {
	t.Helper()
	initTestDB()
	initTLSClientsTable()
	initRelayTable()
	initDaemonLinksTable()
	if _, err := db.Exec(`DELETE FROM daemon_links`); err != nil {
		t.Fatal(err)
	}
	if _, err := db.Exec(`DELETE FROM tls_clients`); err != nil {
		t.Fatal(err)
	}
	if _, err := db.Exec(`DELETE FROM relay_configs`); err != nil {
		t.Fatal(err)
	}
	t.Setenv(relayAddrEnv, "")
	t.Setenv(relayLabelEnv, "")
	t.Setenv(relayPinEnv, "")
	dir := t.TempDir()
	certPath := filepath.Join(dir, "server.crt")
	keyPath := filepath.Join(dir, "server.key")
	if err := generateSelfSignedCert(certPath, keyPath, []string{"localhost"}, 1); err != nil {
		t.Fatal(err)
	}
	t.Setenv(tlsCertEnv, certPath)
	t.Setenv(tlsKeyEnv, keyPath)
	oldFP := tlsServerFingerprint
	tlsServerFingerprint = ""
	t.Cleanup(func() { tlsServerFingerprint = oldFP })
	fp, err := daemonFingerprint()
	if err != nil {
		t.Fatal(err)
	}
	return fp
}

func TestDaemonLinkIdentityIsPeerFingerprintNotRelay(t *testing.T) {
	self := prepareLinkTest(t)
	if err := saveRelayConfig(RelayConfig{Name: "home", Enabled: true, Address: "home.example:9500"}); err != nil {
		t.Fatal(err)
	}
	if err := saveRelayConfig(RelayConfig{Name: "remote", Enabled: true, Address: "remote.example:9500"}); err != nil {
		t.Fatal(err)
	}
	_, peer := newClientCert(t)

	link, created, err := upsertDaemonLink(upsertDaemonLinkRequest{
		Name: "worker", PeerFingerprint: peer, RelayName: "home",
	})
	if err != nil || !created {
		t.Fatalf("create link: created=%v link=%+v err=%v", created, link, err)
	}
	if link.RelayName != "home" {
		t.Fatalf("route=%q, want home", link.RelayName)
	}

	link, created, err = upsertDaemonLink(upsertDaemonLinkRequest{
		Name: "worker-renamed", PeerFingerprint: peer, RelayName: "remote",
	})
	if err != nil || created {
		t.Fatalf("update same peer: created=%v link=%+v err=%v", created, link, err)
	}
	links, err := listDaemonLinks()
	if err != nil || len(links) != 1 {
		t.Fatalf("same peer through two relays became duplicate: %+v err=%v", links, err)
	}
	if links[0].RelayName != "remote" || links[0].Name != "worker-renamed" {
		t.Fatalf("link was not updated in place: %+v", links[0])
	}

	if _, _, err := upsertDaemonLink(upsertDaemonLinkRequest{
		Name: "myself-through-remote", PeerFingerprint: self, RelayName: "remote",
	}); err == nil || !strings.Contains(err.Error(), "cannot link to itself") {
		t.Fatalf("self-link was accepted: %v", err)
	}
}

func TestDaemonLinkGrantsOperatorAndUnlinkRestoresPriorClient(t *testing.T) {
	prepareLinkTest(t)
	if err := saveRelayConfig(RelayConfig{Name: "remote", Enabled: true, Address: "remote.example:9500"}); err != nil {
		t.Fatal(err)
	}
	_, peer := newClientCert(t)
	if err := addAuthorizedClient("viewer", peer, ClientRoleReadOnly); err != nil {
		t.Fatal(err)
	}
	if _, _, err := upsertDaemonLink(upsertDaemonLinkRequest{
		Name: "peer", PeerFingerprint: peer, RelayName: "remote",
	}); err != nil {
		t.Fatal(err)
	}
	client, ok := lookupAuthorizedClient(peer)
	if !ok || client.Role != ClientRoleOperator {
		t.Fatalf("linked peer did not receive ordinary operator access: %+v ok=%v", client, ok)
	}
	if _, err := deleteDaemonLink("peer"); err != nil {
		t.Fatal(err)
	}
	client, ok = lookupAuthorizedClient(peer)
	if !ok || client.Name != "viewer" || client.Role != ClientRoleReadOnly {
		t.Fatalf("unlink did not restore prior client row: %+v ok=%v", client, ok)
	}
}

func TestLinkProxyCannotMakeASecondHop(t *testing.T) {
	req := httptest.NewRequest(http.MethodPost, "/api/link-proxy/peer?method=GET&path=%2Fapi%2Fpty", nil)
	req = req.WithContext(context.WithValue(req.Context(), authPrincipalContextKey{}, authPrincipal{
		Client: AuthorizedClient{Name: "another-daemon", Fingerprint: strings.Repeat("a", 64), Role: ClientRoleOperator},
	}))
	rec := httptest.NewRecorder()
	handleDaemonLinkProxy(rec, req)
	if rec.Code != http.StatusForbidden || !strings.Contains(rec.Body.String(), "cannot be forwarded again") {
		t.Fatalf("peer request entered another hop: %d %s", rec.Code, rec.Body.String())
	}
}

func TestRemotePTYPathCannotEscapeIntoLinksOrOtherAPIs(t *testing.T) {
	for _, good := range []string{"/api/pty", "/api/pty/id/stdin", "/api/pty/id/scrollback?lines=20"} {
		if _, err := validateRemotePTYPath(good); err != nil {
			t.Fatalf("valid PTY path %q rejected: %v", good, err)
		}
	}
	for _, bad := range []string{"/api/links", "/api/tls/clients", "https://other/api/pty", "//other/api/pty"} {
		if _, err := validateRemotePTYPath(bad); err == nil {
			t.Fatalf("non-PTY path %q accepted", bad)
		}
	}
}
