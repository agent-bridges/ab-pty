package main

import (
	"bytes"
	"crypto/tls"
	"database/sql"
	"encoding/json"
	"net"
	"net/http"
	"net/http/httptest"
	"path/filepath"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/gorilla/websocket"
	_ "github.com/mattn/go-sqlite3"
)

func init() {
	// Initialize test DB in memory
	initTestDB()
}

var testDBOnce sync.Once

// initTestDB gives the package-level `db` handle a clean slate.
//
// The handle is opened exactly ONCE per test binary. It used to be
// reopened on every call, which reassigned the global `db` while
// readPtyLoop goroutines spawned by earlier tests were still draining —
// those goroutines call deactivateSession, which reads `db`. `go test
// -race` flagged the pair (initTestDB write vs deactivateSession read) as
// a data race, and it fired in ~4 of 5 runs across a rotating cast of
// tests, because which goroutine was mid-drain when the next test started
// is pure timing.
//
// Production never reassigns `db` — initDB opens it once at startup and
// every later access is read-only — so opening once here matches the real
// lifecycle instead of inventing a mutation the daemon never performs.
// Callers still get their fresh slate: the table is recreated if missing
// and its rows are cleared on every call.
func initTestDB() {
	testDBOnce.Do(func() {
		var err error
		// Shared-cache DSN, not a bare ":memory:". A plain in-memory
		// sqlite database is scoped to a single connection, so the moment
		// database/sql's pool opens a second one (any concurrent query
		// does it) that query lands on an empty database with no tables —
		// which showed up as a rare, rotating test failure rather than an
		// obvious error. `cache=shared` with a named file: DSN gives every
		// pooled connection the same database.
		db, err = sql.Open("sqlite3", "file:abpty_test?mode=memory&cache=shared")
		if err != nil {
			panic(err)
		}
	})
	if _, err := db.Exec(`
		CREATE TABLE IF NOT EXISTS session_meta (
			id TEXT PRIMARY KEY,
			name TEXT NOT NULL DEFAULT '',
			locked INTEGER DEFAULT 0,
			active INTEGER DEFAULT 1,
			meta TEXT DEFAULT '{}',
			created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
			updated_at DATETIME DEFAULT CURRENT_TIMESTAMP
		)
	`); err != nil {
		panic(err)
	}
	if _, err := db.Exec(`DELETE FROM session_meta`); err != nil {
		panic(err)
	}
}

func TestHealthEndpoint(t *testing.T) {
	req := httptest.NewRequest("GET", "/health", nil)
	w := httptest.NewRecorder()

	handleHealth(w, req)

	if w.Code != http.StatusOK {
		t.Errorf("Expected status 200, got %d", w.Code)
	}

	var resp map[string]interface{}
	json.Unmarshal(w.Body.Bytes(), &resp)

	if resp["status"] != "ok" {
		t.Errorf("Expected status 'ok', got %v", resp["status"])
	}
}

func TestCliTLSConfigRequiresCompleteValidKeypair(t *testing.T) {
	t.Setenv(ptyClientCertEnv, "/tmp/client.crt")
	t.Setenv(ptyClientKeyEnv, "")
	if _, err := cliTLSConfig(); err == nil || !strings.Contains(err.Error(), ptyClientKeyEnv+" is missing") {
		t.Fatalf("expected missing-key error naming %s, got %v", ptyClientKeyEnv, err)
	}

	t.Setenv(ptyClientCertEnv, "")
	t.Setenv(ptyClientKeyEnv, "/tmp/client.key")
	if _, err := cliTLSConfig(); err == nil || !strings.Contains(err.Error(), ptyClientCertEnv+" is missing") {
		t.Fatalf("expected missing-certificate error naming %s, got %v", ptyClientCertEnv, err)
	}

	t.Setenv(ptyClientCertEnv, "/tmp/client.crt")
	t.Setenv(ptyClientKeyEnv, "/tmp/client.key")
	if _, err := cliTLSConfig(); err == nil || !strings.Contains(err.Error(), "load HTTPS client X509 keypair") {
		t.Fatalf("expected invalid-keypair error, got %v", err)
	}
}

func TestCliRequestPresentsConfiguredClientCertificate(t *testing.T) {
	dir := t.TempDir()
	serverCert := filepath.Join(dir, "server.crt")
	serverKey := filepath.Join(dir, "server.key")
	clientCert := filepath.Join(dir, "client.crt")
	clientKey := filepath.Join(dir, "client.key")
	if err := generateSelfSignedCert(serverCert, serverKey, []string{"localhost"}, 1); err != nil {
		t.Fatal(err)
	}
	if err := generateSelfSignedCert(clientCert, clientKey, []string{"client"}, 1); err != nil {
		t.Fatal(err)
	}
	serverPair, err := tls.LoadX509KeyPair(serverCert, serverKey)
	if err != nil {
		t.Fatal(err)
	}

	presented := make(chan bool, 1)
	server := httptest.NewUnstartedServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) {
		presented <- r.TLS != nil && len(r.TLS.PeerCertificates) == 1
		_, _ = w.Write([]byte("ok"))
	}))
	server.TLS = &tls.Config{
		Certificates: []tls.Certificate{serverPair},
		ClientAuth:   tls.RequireAnyClientCert,
		MinVersion:   tls.VersionTLS12,
	}
	server.StartTLS()
	defer server.Close()

	_, port, err := net.SplitHostPort(server.Listener.Addr().String())
	if err != nil {
		t.Fatal(err)
	}
	t.Setenv(tlsModeEnv, TLSModeRequired)
	t.Setenv("AB_PTY_PORT", port)
	t.Setenv(ptyClientCertEnv, clientCert)
	t.Setenv(ptyClientKeyEnv, clientKey)

	body, err := cliRequest(http.MethodGet, "/", nil)
	if err != nil {
		t.Fatalf("HTTPS client request failed: %v", err)
	}
	if string(body) != "ok" || !<-presented {
		t.Fatalf("configured client certificate was not presented; body=%q", body)
	}
}

func TestCreatePtySessionPropagatesClientCertificateEnvironment(t *testing.T) {
	initTestDB()
	sessionsMu.Lock()
	sessions = make(map[string]*Session)
	sessionsMu.Unlock()

	t.Setenv(ptyClientCertEnv, "/state/client-certs/local.crt")
	t.Setenv(ptyClientKeyEnv, "/state/client-certs/local.key")
	session, err := createPtySession("/tmp", 24, 80, "tls-child", "", true, "pty_tls_env_10001", nil)
	if err != nil {
		t.Fatal(err)
	}
	defer killSession(session.ID)

	env := map[string]string{}
	for _, entry := range session.Cmd.Env {
		key, value, ok := strings.Cut(entry, "=")
		if ok {
			env[key] = value
		}
	}
	if env[ptyClientCertEnv] != "/state/client-certs/local.crt" || env[ptyClientKeyEnv] != "/state/client-certs/local.key" {
		t.Fatalf("client identity was not propagated: cert=%q key=%q", env[ptyClientCertEnv], env[ptyClientKeyEnv])
	}
}

func TestHandleHookPrefersPidAncestryOverCache(t *testing.T) {
	initTestDB()

	origGet := getPtyForClaudeSessionFn
	origPid := findPtyByPidAncestryFn
	origProc := findPtyByClaudeProcessFn
	origCwd := findPtyIDByCwdFn
	t.Cleanup(func() {
		getPtyForClaudeSessionFn = origGet
		findPtyByPidAncestryFn = origPid
		findPtyByClaudeProcessFn = origProc
		findPtyIDByCwdFn = origCwd

		claudeSessionMapMu.Lock()
		claudeSessionMap = map[string]string{}
		claudeSessionMapMu.Unlock()

		aiStatusMu.Lock()
		aiStatuses = map[string]aiStatusEntry{}
		aiStatusMu.Unlock()
	})

	claudeSessionMapMu.Lock()
	claudeSessionMap = map[string]string{"sess-1": "pty-old"}
	claudeSessionMapMu.Unlock()

	findPtyByPidAncestryFn = func(pid int) string {
		if pid == 4242 {
			return "pty-new"
		}
		return ""
	}
	findPtyByClaudeProcessFn = func(string) string { return "" }
	findPtyIDByCwdFn = func(string) string { return "" }

	req := httptest.NewRequest("POST", "/api/hook", bytes.NewBufferString(`{
		"hook_event_name":"SessionStart",
		"session_id":"sess-1",
		"cwd":"/",
		"caller_pid":4242
	}`))
	w := httptest.NewRecorder()

	handleHook(w, req)

	if w.Code != http.StatusOK {
		t.Fatalf("Expected status 200, got %d", w.Code)
	}

	if got := getPtyForClaudeSession("sess-1"); got != "pty-new" {
		t.Fatalf("Expected session to remap to pty-new, got %q", got)
	}

	if got := getAiStatus("pty-new"); got != "working" {
		t.Fatalf("Expected ai status for pty-new to be working, got %q", got)
	}
}

func TestGetCodexHeuristicStatusWorkingOnRecentActivity(t *testing.T) {
	session := &Session{}
	session.LastInputAt = time.Now().Add(-2 * time.Second)

	status := getCodexHeuristicStatus(session, []ProcessInfo{
		{Pid: 1, Cmd: "codex", Args: "codex"},
	})

	if status != "working" {
		t.Fatalf("Expected codex status to be working, got %q", status)
	}
}

func TestGetCodexHeuristicStatusIgnoresRecentOutputWithoutInput(t *testing.T) {
	session := &Session{}
	session.LastOutputAt = time.Now().Add(-2 * time.Second)

	status := getCodexHeuristicStatus(session, []ProcessInfo{
		{Pid: 1, Cmd: "codex", Args: "codex"},
	})

	if status != "idle" {
		t.Fatalf("Expected codex status to be idle without user input, got %q", status)
	}
}

func TestGetCodexHeuristicStatusKeepsWorkingOnOutputAfterInput(t *testing.T) {
	session := &Session{}
	session.LastInputAt = time.Now().Add(-30 * time.Second)
	session.LastOutputAt = time.Now().Add(-2 * time.Second)

	status := getCodexHeuristicStatus(session, []ProcessInfo{
		{Pid: 1, Cmd: "codex", Args: "codex"},
	})

	if status != "working" {
		t.Fatalf("Expected codex status to stay working after input-driven output, got %q", status)
	}
}

func TestGetCodexHeuristicStatusToolFromBusyChild(t *testing.T) {
	session := &Session{}

	status := getCodexHeuristicStatus(session, []ProcessInfo{
		{Pid: 1, Cmd: "codex", Args: "codex"},
		{Pid: 2, Cmd: "rg", Args: "rg --files"},
	})

	if status != "tool:rg" {
		t.Fatalf("Expected codex status to be tool:rg, got %q", status)
	}
}

func TestExtractMeaningfulTerminalOutputIgnoresAnsiNoise(t *testing.T) {
	if got := extractMeaningfulTerminalOutput("\x1b[?2004h\x1b[6n\x1b]10;?\x1b\\"); got != "" {
		t.Fatalf("Expected pure ANSI control output to be ignored, got %q", got)
	}
	if got := extractMeaningfulTerminalOutput("\x1b[32mhello\x1b[0m"); got != "hello" {
		t.Fatalf("Expected visible text wrapped in ANSI to survive stripping, got %q", got)
	}
}

func TestListPtyEmpty(t *testing.T) {
	// Clear sessions
	sessionsMu.Lock()
	sessions = make(map[string]*Session)
	sessionsMu.Unlock()

	req := httptest.NewRequest("GET", "/api/pty", nil)
	w := httptest.NewRecorder()

	handleListPty(w, req)

	if w.Code != http.StatusOK {
		t.Errorf("Expected status 200, got %d", w.Code)
	}

	var resp []interface{}
	json.Unmarshal(w.Body.Bytes(), &resp)

	if len(resp) != 0 {
		t.Errorf("Expected empty list, got %d items", len(resp))
	}
}

func TestSessionMeta(t *testing.T) {
	initTestDB() // Reset DB

	// Test create
	name := "test-name"
	meta := setSessionMeta("test-session-1", &name, nil, nil)

	if meta == nil {
		t.Fatal("Expected meta to be created")
	}
	if meta.Name != "test-name" {
		t.Errorf("Expected name 'test-name', got '%s'", meta.Name)
	}

	// Test lock
	locked := true
	meta = setSessionMeta("test-session-1", nil, &locked, nil)
	if !meta.Locked {
		t.Error("Expected session to be locked")
	}

	// Test unlock
	locked = false
	meta = setSessionMeta("test-session-1", nil, &locked, nil)
	if meta.Locked {
		t.Error("Expected session to be unlocked")
	}

	// Test meta update
	meta = setSessionMeta("test-session-1", nil, nil, map[string]interface{}{
		"claude_session_id": "abc123",
	})
	if meta.Meta["claude_session_id"] != "abc123" {
		t.Errorf("Expected claude_session_id 'abc123', got '%v'", meta.Meta["claude_session_id"])
	}

	// Test get
	meta = getSessionMeta("test-session-1")
	if meta == nil {
		t.Fatal("Expected to get session meta")
	}
	if meta.Name != "test-name" {
		t.Errorf("Expected name 'test-name', got '%s'", meta.Name)
	}
}

func TestEnsureSessionMetaSchemaMigratesNameAndDropsLabel(t *testing.T) {
	legacyDB, err := sql.Open("sqlite3", "file:abpty_legacy_schema?mode=memory&cache=shared")
	if err != nil {
		t.Fatal(err)
	}
	defer legacyDB.Close()
	if _, err := legacyDB.Exec(`
		CREATE TABLE session_meta (
			id TEXT PRIMARY KEY,
			label TEXT DEFAULT '',
			locked INTEGER DEFAULT 0,
			active INTEGER DEFAULT 0,
			meta TEXT DEFAULT '{}',
			created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
			updated_at DATETIME DEFAULT CURRENT_TIMESTAMP
		);
		INSERT INTO session_meta (id, label, active, meta)
		VALUES ('pty_1_12345', 'discard-me', 1, '{"project_name":"persisted-name","project_path":"/tmp/project","shell_only":true}')
	`); err != nil {
		t.Fatal(err)
	}

	if err := ensureSessionMetaSchema(legacyDB); err != nil {
		t.Fatalf("migration failed: %v", err)
	}

	columns := map[string]bool{}
	rows, err := legacyDB.Query(`PRAGMA table_info(session_meta)`)
	if err != nil {
		t.Fatal(err)
	}
	for rows.Next() {
		var cid, notNull, pk int
		var name, columnType string
		var defaultValue interface{}
		if err := rows.Scan(&cid, &name, &columnType, &notNull, &defaultValue, &pk); err != nil {
			t.Fatal(err)
		}
		columns[name] = true
	}
	rows.Close()
	if !columns["name"] || columns["label"] {
		t.Fatalf("expected name-only identity schema, columns=%v", columns)
	}

	var name, metaJSON string
	if err := legacyDB.QueryRow(`SELECT name, meta FROM session_meta WHERE id = 'pty_1_12345'`).Scan(&name, &metaJSON); err != nil {
		t.Fatal(err)
	}
	if name != "persisted-name" {
		t.Fatalf("expected migrated name, got %q", name)
	}
	var meta map[string]interface{}
	if err := json.Unmarshal([]byte(metaJSON), &meta); err != nil {
		t.Fatal(err)
	}
	if _, exists := meta["project_name"]; exists {
		t.Fatalf("legacy project_name identity was retained: %s", metaJSON)
	}
	if _, err := legacyDB.Exec(`INSERT INTO session_meta (id, name, active) VALUES ('pty_1_99999', 'persisted-name', 1)`); err == nil {
		t.Fatal("live-name uniqueness index was not installed")
	}
}

func TestDefaultSessionNameUsesProjectBasename(t *testing.T) {
	if got := defaultSessionName("pty_123_45678", "/work/readable-project"); got != "readable-project-45678" {
		t.Fatalf("unexpected generated name %q", got)
	}
}

func TestResolveClientSessionTargetUsesExactIDThenUniqueLiveName(t *testing.T) {
	data := []byte(`[
		{"id":"pty_exact","name":"old","alive":false},
		{"id":"pty_live","name":"pty_exact","alive":true},
		{"id":"pty_named","name":"worker","alive":true},
		{"id":"pty_dead","name":"worker","alive":false}
	]`)
	if got, err := resolveClientSessionTarget(data, "pty_exact"); err != nil || got != "pty_exact" {
		t.Fatalf("exact id did not win: got=%q err=%v", got, err)
	}
	if got, err := resolveClientSessionTarget(data, "worker"); err != nil || got != "pty_named" {
		t.Fatalf("unique live name did not resolve: got=%q err=%v", got, err)
	}
	if _, err := resolveClientSessionTarget(data, "missing"); err == nil || !strings.Contains(err.Error(), "not found") {
		t.Fatalf("missing name did not fail explicitly: %v", err)
	}

	ambiguous := []byte(`{"sessions":[
		{"id":"pty_a","name":"worker","alive":true},
		{"id":"pty_b","name":"worker","alive":true}
	]}`)
	if _, err := resolveClientSessionTarget(ambiguous, "worker"); err == nil || !strings.Contains(err.Error(), "ambiguous") {
		t.Fatalf("ambiguous live name did not fail explicitly: %v", err)
	}
}

func TestExpandPath(t *testing.T) {
	tests := []struct {
		input    string
		contains string
	}{
		{"~", "/"},
		{"~/test", "/test"},
		{"/tmp", "/tmp"},
		{"/absolute/path", "/absolute/path"},
	}

	for _, tt := range tests {
		result := expandPath(tt.input)
		if !strings.Contains(result, tt.contains) {
			t.Errorf("expandPath(%s) = %s, expected to contain %s", tt.input, result, tt.contains)
		}
	}
}

func TestCreateAndKillSession(t *testing.T) {
	// Clear sessions
	sessionsMu.Lock()
	sessions = make(map[string]*Session)
	sessionsMu.Unlock()

	// Create bash session
	session, err := createPtySession("/tmp", 24, 80, "test", "", true, "", nil)
	if err != nil || session == nil {
		t.Fatalf("Failed to create session: %v", err)
	}

	if session.ProjectPath != "/tmp" {
		t.Errorf("Expected project path '/tmp', got '%s'", session.ProjectPath)
	}

	if !session.ShellOnly {
		t.Error("Expected shell_only to be true")
	}

	if !session.Alive {
		t.Error("Expected session to be alive")
	}

	// Check session is in map
	sessionsMu.RLock()
	_, exists := sessions[session.ID]
	sessionsMu.RUnlock()

	if !exists {
		t.Error("Session not found in sessions map")
	}

	// Give it time to start
	time.Sleep(100 * time.Millisecond)

	// Kill session
	killSession(session.ID)

	// Check session is removed
	sessionsMu.RLock()
	_, exists = sessions[session.ID]
	sessionsMu.RUnlock()

	if exists {
		t.Error("Session should be removed after kill")
	}
}

func TestPtyLockUnlockAPI(t *testing.T) {
	initTestDB()

	// Create a session first
	sessionsMu.Lock()
	sessions = make(map[string]*Session)
	sessionsMu.Unlock()

	session, err := createPtySession("/tmp", 24, 80, "test", "", true, "test-lock-session", nil)
	if err != nil || session == nil {
		t.Fatalf("Failed to create session: %v", err)
	}
	defer killSession(session.ID)

	// Test lock
	req := httptest.NewRequest("POST", "/api/pty/test-lock-session/lock", nil)
	w := httptest.NewRecorder()
	handlePtyAPI(w, req)

	var resp map[string]interface{}
	json.Unmarshal(w.Body.Bytes(), &resp)

	if resp["locked"] != true {
		t.Errorf("Expected locked=true, got %v", resp["locked"])
	}

	// Verify in DB
	meta := getSessionMeta("test-lock-session")
	if !meta.Locked {
		t.Error("Session should be locked in DB")
	}

	// Test unlock
	req = httptest.NewRequest("DELETE", "/api/pty/test-lock-session/lock", nil)
	w = httptest.NewRecorder()
	handlePtyAPI(w, req)

	json.Unmarshal(w.Body.Bytes(), &resp)
	if resp["locked"] != false {
		t.Errorf("Expected locked=false, got %v", resp["locked"])
	}
}

func TestPtyDeleteAPI(t *testing.T) {
	sessionsMu.Lock()
	sessions = make(map[string]*Session)
	sessionsMu.Unlock()

	session, err := createPtySession("/tmp", 24, 80, "test", "", true, "test-delete-session", nil)
	if err != nil || session == nil {
		t.Fatalf("Failed to create session: %v", err)
	}

	// Delete via API
	req := httptest.NewRequest("DELETE", "/api/pty/test-delete-session", nil)
	w := httptest.NewRecorder()
	handlePtyAPI(w, req)

	if w.Code != http.StatusOK {
		t.Errorf("Expected status 200, got %d", w.Code)
	}

	var resp map[string]interface{}
	json.Unmarshal(w.Body.Bytes(), &resp)

	if resp["ok"] != true {
		t.Errorf("Expected ok=true, got %v", resp["ok"])
	}

	// Verify session is gone
	sessionsMu.RLock()
	_, exists := sessions["test-delete-session"]
	sessionsMu.RUnlock()

	if exists {
		t.Error("Session should be deleted")
	}
}

func TestPtyMetaUpdateAPIRejectsSessionLabel(t *testing.T) {
	initTestDB()

	// Create session
	sessionsMu.Lock()
	sessions = make(map[string]*Session)
	sessionsMu.Unlock()

	session, err := createPtySession("/tmp", 24, 80, "test", "", true, "test-meta-session", nil)
	if err != nil || session == nil {
		t.Fatalf("Failed to create session: %v", err)
	}
	defer killSession(session.ID)

	// Session label is no longer part of the contract.
	body := strings.NewReader(`{"label":"my-label","meta":{"custom":"value"}}`)
	req := httptest.NewRequest("PATCH", "/api/pty/test-meta-session/meta", body)
	w := httptest.NewRecorder()
	handlePtyAPI(w, req)

	if w.Code != http.StatusBadRequest {
		t.Fatalf("Expected status 400, got %d: %s", w.Code, w.Body.String())
	}
	if strings.Contains(w.Body.String(), `"label":"my-label"`) {
		t.Fatalf("response retained the removed session label: %s", w.Body.String())
	}
}

func TestPtyCreateAPIRejectsLegacyIdentityFields(t *testing.T) {
	for _, body := range []string{
		`{"project_path":"/tmp","shell_only":true,"label":"legacy"}`,
		`{"project_path":"/tmp","shell_only":true,"project_name":"legacy"}`,
	} {
		req := httptest.NewRequest(http.MethodPost, "/api/pty", strings.NewReader(body))
		w := httptest.NewRecorder()
		handleListPty(w, req)
		if w.Code != http.StatusBadRequest {
			t.Fatalf("expected legacy identity field rejection, status=%d body=%s", w.Code, w.Body.String())
		}
	}
}

func TestPtyCreateAPIReturnsConflictForDuplicateLiveName(t *testing.T) {
	initTestDB()
	sessionsMu.Lock()
	sessions = make(map[string]*Session)
	sessionsMu.Unlock()

	requestBody := `{"project_path":"/tmp","shell_only":true,"name":"duplicate-live-name"}`
	firstReq := httptest.NewRequest(http.MethodPost, "/api/pty", strings.NewReader(requestBody))
	firstResp := httptest.NewRecorder()
	handleListPty(firstResp, firstReq)
	if firstResp.Code != http.StatusOK {
		t.Fatalf("first create failed: status=%d body=%s", firstResp.Code, firstResp.Body.String())
	}
	var created struct {
		SessionID string `json:"session_id"`
	}
	if err := json.Unmarshal(firstResp.Body.Bytes(), &created); err != nil || created.SessionID == "" {
		t.Fatalf("invalid first create response: err=%v body=%s", err, firstResp.Body.String())
	}
	defer killSession(created.SessionID)

	duplicateReq := httptest.NewRequest(http.MethodPost, "/api/pty", strings.NewReader(requestBody))
	duplicateResp := httptest.NewRecorder()
	handleListPty(duplicateResp, duplicateReq)
	if duplicateResp.Code != http.StatusConflict {
		t.Fatalf("expected status 409, got %d: %s", duplicateResp.Code, duplicateResp.Body.String())
	}
	var conflict map[string]interface{}
	if err := json.Unmarshal(duplicateResp.Body.Bytes(), &conflict); err != nil {
		t.Fatal(err)
	}
	if conflict["error_type"] != "session_name_conflict" {
		t.Fatalf("unexpected conflict classification: %v", conflict)
	}

	sessionsMu.RLock()
	count := len(sessions)
	sessionsMu.RUnlock()
	if count != 1 {
		t.Fatalf("duplicate create changed live sessions: got %d", count)
	}
}

func TestPtyRenameAPIIsUniqueAndPersistent(t *testing.T) {
	initTestDB()
	sessionsMu.Lock()
	sessions = make(map[string]*Session)
	sessionsMu.Unlock()

	first, err := createPtySession("/tmp", 24, 80, "alpha", "", true, "pty_rename_10001", nil)
	if err != nil {
		t.Fatal(err)
	}
	defer killSession(first.ID)
	second, err := createPtySession("/tmp", 24, 80, "beta", "", true, "pty_rename_10002", nil)
	if err != nil {
		t.Fatal(err)
	}
	defer killSession(second.ID)

	// HTTP accepts only the canonical id, never a session name.
	req := httptest.NewRequest(http.MethodPatch, "/api/pty/alpha/name", strings.NewReader(`{"name":"gamma"}`))
	w := httptest.NewRecorder()
	handlePtyAPI(w, req)
	if w.Code != http.StatusNotFound {
		t.Fatalf("expected name-routed API request to fail, status=%d body=%s", w.Code, w.Body.String())
	}

	req = httptest.NewRequest(http.MethodPatch, "/api/pty/"+first.ID+"/name", strings.NewReader(`{"name":"gamma"}`))
	w = httptest.NewRecorder()
	handlePtyAPI(w, req)
	if w.Code != http.StatusOK {
		t.Fatalf("rename failed: status=%d body=%s", w.Code, w.Body.String())
	}
	var resp map[string]interface{}
	if err := json.Unmarshal(w.Body.Bytes(), &resp); err != nil {
		t.Fatal(err)
	}
	if resp["id"] != first.ID || resp["name"] != "gamma" {
		t.Fatalf("unexpected rename response: %v", resp)
	}
	if _, exists := resp["label"]; exists {
		t.Fatalf("rename response exposed removed label: %v", resp)
	}
	if persisted := getSessionMeta(first.ID); persisted == nil || persisted.Name != "gamma" {
		t.Fatalf("renamed name was not persisted: %#v", persisted)
	}
	sessionsMu.RLock()
	if sessions[first.ID].Name != "gamma" {
		t.Fatalf("in-memory name was not updated: %q", sessions[first.ID].Name)
	}
	sessionsMu.RUnlock()

	req = httptest.NewRequest(http.MethodPatch, "/api/pty/"+first.ID+"/name", strings.NewReader(`{"name":"beta"}`))
	w = httptest.NewRecorder()
	handlePtyAPI(w, req)
	if w.Code != http.StatusConflict {
		t.Fatalf("expected duplicate rename conflict, status=%d body=%s", w.Code, w.Body.String())
	}
	if persisted := getSessionMeta(first.ID); persisted == nil || persisted.Name != "gamma" {
		t.Fatalf("failed rename changed persisted name: %#v", persisted)
	}

	req = httptest.NewRequest(http.MethodPatch, "/api/pty/"+first.ID+"/name", strings.NewReader(`{"name":"   "}`))
	w = httptest.NewRecorder()
	handlePtyAPI(w, req)
	if w.Code != http.StatusBadRequest {
		t.Fatalf("expected empty rename rejection, status=%d body=%s", w.Code, w.Body.String())
	}
}

func TestPtyMetaUpdatePayloadHasOnlyCanonicalIdentity(t *testing.T) {
	initTestDB()
	sessionsMu.Lock()
	sessions = make(map[string]*Session)
	sessionsMu.Unlock()

	session, err := createPtySession("/tmp", 24, 80, "canonical", "", true, "pty_meta_10001", nil)
	if err != nil {
		t.Fatal(err)
	}
	defer killSession(session.ID)

	req := httptest.NewRequest(http.MethodPatch, "/api/pty/"+session.ID+"/meta", strings.NewReader(`{"meta":{"custom":"value"}}`))
	w := httptest.NewRecorder()
	handlePtyAPI(w, req)
	if w.Code != http.StatusOK {
		t.Fatalf("meta update failed: status=%d body=%s", w.Code, w.Body.String())
	}
	var resp map[string]interface{}
	if err := json.Unmarshal(w.Body.Bytes(), &resp); err != nil {
		t.Fatal(err)
	}
	if resp["id"] != session.ID || resp["name"] != session.Name {
		t.Fatalf("canonical identity missing: %v", resp)
	}
	if _, exists := resp["label"]; exists {
		t.Fatalf("meta response exposed removed label: %v", resp)
	}
	meta, _ := resp["meta"].(map[string]interface{})
	if meta["custom"] != "value" {
		t.Fatalf("metadata update missing: %v", resp)
	}
}

func TestListPtyWithSession(t *testing.T) {
	initTestDB()

	sessionsMu.Lock()
	sessions = make(map[string]*Session)
	sessionsMu.Unlock()

	session, err := createPtySession("/tmp", 24, 80, "test-session", "", true, "list-test-session", nil)
	if err != nil || session == nil {
		t.Fatalf("Failed to create session: %v", err)
	}
	defer killSession(session.ID)

	req := httptest.NewRequest("GET", "/api/pty", nil)
	w := httptest.NewRecorder()
	handleListPty(w, req)

	var resp []map[string]interface{}
	json.Unmarshal(w.Body.Bytes(), &resp)

	if len(resp) != 1 {
		t.Errorf("Expected 1 session, got %d", len(resp))
	}

	if resp[0]["id"] != "list-test-session" {
		t.Errorf("Expected id='list-test-session', got %v", resp[0]["id"])
	}

	if resp[0]["type"] != "bash" {
		t.Errorf("Expected type='bash', got %v", resp[0]["type"])
	}

	if resp[0]["alive"] != true {
		t.Errorf("Expected alive=true, got %v", resp[0]["alive"])
	}
	if resp[0]["name"] != "test-session" {
		t.Errorf("Expected name='test-session', got %v", resp[0]["name"])
	}
	if _, exists := resp[0]["label"]; exists {
		t.Fatalf("REST payload exposed removed label: %v", resp[0])
	}
	if _, exists := resp[0]["project_name"]; exists {
		t.Fatalf("REST payload exposed duplicate project_name identity: %v", resp[0])
	}
	meta, _ := resp[0]["meta"].(map[string]interface{})
	if _, exists := meta["project_name"]; exists {
		t.Fatalf("REST metadata retained duplicate project_name identity: %v", resp[0])
	}
}

func TestWebSocketPtyState(t *testing.T) {
	initTestDB()

	sessionsMu.Lock()
	sessions = make(map[string]*Session)
	sessionsMu.Unlock()

	resetStateSubs()

	// Create test server
	server := httptest.NewServer(http.HandlerFunc(handlePtyState))
	defer server.Close()

	// Connect WebSocket
	wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
	ws, _, err := websocket.DefaultDialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("Failed to connect: %v", err)
	}
	defer ws.Close()

	// Should receive initial state
	ws.SetReadDeadline(time.Now().Add(2 * time.Second))
	_, msg, err := ws.ReadMessage()
	if err != nil {
		t.Fatalf("Failed to read message: %v", err)
	}

	var state map[string]interface{}
	json.Unmarshal(msg, &state)

	if state["type"] != "pty_state" {
		t.Errorf("Expected type='pty_state', got %v", state["type"])
	}

	sessions := state["sessions"].([]interface{})
	if len(sessions) != 0 {
		t.Errorf("Expected 0 sessions, got %d", len(sessions))
	}

	// Test ping/pong
	ws.WriteJSON(map[string]string{"type": "ping"})

	ws.SetReadDeadline(time.Now().Add(2 * time.Second))
	_, msg, err = ws.ReadMessage()
	if err != nil {
		t.Fatalf("Failed to read pong: %v", err)
	}

	var pong map[string]string
	json.Unmarshal(msg, &pong)

	if pong["type"] != "pong" {
		t.Errorf("Expected type='pong', got %v", pong["type"])
	}
}

func TestWebSocketPtyStateUsesNameOnlyIdentity(t *testing.T) {
	initTestDB()
	sessionsMu.Lock()
	sessions = make(map[string]*Session)
	sessionsMu.Unlock()
	resetStateSubs()

	session, err := createPtySession("/tmp", 24, 80, "ws-name", "", true, "pty_ws_10001", nil)
	if err != nil {
		t.Fatal(err)
	}
	defer killSession(session.ID)

	server := httptest.NewServer(http.HandlerFunc(handlePtyState))
	defer server.Close()
	wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
	ws, _, err := websocket.DefaultDialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatal(err)
	}
	defer ws.Close()
	ws.SetReadDeadline(time.Now().Add(2 * time.Second))
	_, msg, err := ws.ReadMessage()
	if err != nil {
		t.Fatal(err)
	}
	var state struct {
		Sessions []map[string]interface{} `json:"sessions"`
	}
	if err := json.Unmarshal(msg, &state); err != nil {
		t.Fatal(err)
	}
	if len(state.Sessions) != 1 {
		t.Fatalf("expected one session, got %s", msg)
	}
	payload := state.Sessions[0]
	if payload["id"] != session.ID || payload["name"] != "ws-name" {
		t.Fatalf("canonical websocket identity missing: %v", payload)
	}
	if _, exists := payload["label"]; exists {
		t.Fatalf("websocket payload exposed removed label: %v", payload)
	}
	if _, exists := payload["project_name"]; exists {
		t.Fatalf("websocket payload exposed duplicate project_name identity: %v", payload)
	}
}

func TestWebSocketTerminal(t *testing.T) {
	initTestDB()

	sessionsMu.Lock()
	sessions = make(map[string]*Session)
	sessionsMu.Unlock()

	// Create test server
	server := httptest.NewServer(http.HandlerFunc(handleWebSocket))
	defer server.Close()

	// Connect WebSocket
	wsURL := "ws" + strings.TrimPrefix(server.URL, "http")
	ws, _, err := websocket.DefaultDialer.Dial(wsURL, nil)
	if err != nil {
		t.Fatalf("Failed to connect: %v", err)
	}
	defer ws.Close()

	// Send init message for bash session
	ws.WriteJSON(map[string]interface{}{
		"action":       "new",
		"project_path": "/tmp",
		"shell_only":   true,
		"rows":         24,
		"cols":         80,
	})

	// Should receive ready message
	ws.SetReadDeadline(time.Now().Add(5 * time.Second))
	_, msg, err := ws.ReadMessage()
	if err != nil {
		t.Fatalf("Failed to read ready message: %v", err)
	}

	var ready map[string]interface{}
	json.Unmarshal(msg, &ready)

	if ready["type"] != "ready" {
		t.Errorf("Expected type='ready', got %v", ready["type"])
	}

	sessionID := ready["session_id"].(string)
	if sessionID == "" {
		t.Error("Expected session_id to be set")
	}

	// Verify session exists
	sessionsMu.RLock()
	session, exists := sessions[sessionID]
	sessionsMu.RUnlock()

	if !exists {
		t.Error("Session should exist")
	}

	// Test input
	ws.WriteJSON(map[string]interface{}{
		"type": "input",
		"data": "echo hello\n",
	})

	// Wait for output
	time.Sleep(200 * time.Millisecond)

	// Test resize
	ws.WriteJSON(map[string]interface{}{
		"type": "resize",
		"rows": 30,
		"cols": 100,
	})

	time.Sleep(100 * time.Millisecond)

	// Read through the accessor: the resize is applied on the websocket
	// handler's goroutine, so touching the fields directly is a data race.
	if rows, cols := session.Winsize(); rows != 30 || cols != 100 {
		t.Errorf("Expected size 30x100, got %dx%d", rows, cols)
	}

	// Test ping
	ws.WriteJSON(map[string]string{"type": "ping"})

	// Read messages until we get pong (skip output messages)
	for i := 0; i < 10; i++ {
		ws.SetReadDeadline(time.Now().Add(2 * time.Second))
		_, msg, err = ws.ReadMessage()
		if err != nil {
			break
		}

		var resp map[string]interface{}
		json.Unmarshal(msg, &resp)
		if resp["type"] == "pong" {
			break
		}
	}

	// Cleanup
	killSession(sessionID)
}

func TestConcurrentSessions(t *testing.T) {
	initTestDB()

	sessionsMu.Lock()
	sessions = make(map[string]*Session)
	sessionsMu.Unlock()

	var wg sync.WaitGroup
	sessionCount := 5

	for i := 0; i < sessionCount; i++ {
		wg.Add(1)
		go func(idx int) {
			defer wg.Done()
			session, err := createPtySession("/tmp", 24, 80, "", "", true, "", nil)
			if err != nil || session == nil {
				t.Errorf("Failed to create session %d: %v", idx, err)
			}
		}(i)
	}

	wg.Wait()

	sessionsMu.RLock()
	count := len(sessions)
	sessionsMu.RUnlock()

	if count != sessionCount {
		t.Errorf("Expected %d sessions, got %d", sessionCount, count)
	}

	// Cleanup
	sessionsMu.RLock()
	ids := make([]string, 0, len(sessions))
	for id := range sessions {
		ids = append(ids, id)
	}
	sessionsMu.RUnlock()

	for _, id := range ids {
		killSession(id)
	}
}

func TestGetFloat(t *testing.T) {
	m := map[string]interface{}{
		"rows": float64(30),
		"cols": float64(100),
	}

	if getFloat(m, "rows", 24) != 30 {
		t.Error("Expected 30 for rows")
	}

	if getFloat(m, "missing", 50) != 50 {
		t.Error("Expected default 50 for missing key")
	}
}
