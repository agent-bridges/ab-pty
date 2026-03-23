package main

import (
	"bytes"
	"database/sql"
	"encoding/json"
	"net/http"
	"net/http/httptest"
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

func initTestDB() {
	var err error
	db, err = sql.Open("sqlite3", ":memory:")
	if err != nil {
		panic(err)
	}
	db.Exec(`
		CREATE TABLE IF NOT EXISTS session_meta (
			id TEXT PRIMARY KEY,
			label TEXT DEFAULT '',
			locked INTEGER DEFAULT 0,
			active INTEGER DEFAULT 1,
			meta TEXT DEFAULT '{}',
			created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
			updated_at DATETIME DEFAULT CURRENT_TIMESTAMP
		)
	`)
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
	label := "test-label"
	meta := setSessionMeta("test-session-1", &label, nil, nil)

	if meta == nil {
		t.Fatal("Expected meta to be created")
	}
	if meta.Label != "test-label" {
		t.Errorf("Expected label 'test-label', got '%s'", meta.Label)
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
	if meta.Label != "test-label" {
		t.Errorf("Expected label 'test-label', got '%s'", meta.Label)
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

func TestPtyMetaUpdateAPI(t *testing.T) {
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

	// Update meta
	body := strings.NewReader(`{"label":"my-label","meta":{"custom":"value"}}`)
	req := httptest.NewRequest("PATCH", "/api/pty/test-meta-session/meta", body)
	w := httptest.NewRecorder()
	handlePtyAPI(w, req)

	var resp map[string]interface{}
	json.Unmarshal(w.Body.Bytes(), &resp)

	if resp["label"] != "my-label" {
		t.Errorf("Expected label='my-label', got %v", resp["label"])
	}

	meta := resp["meta"].(map[string]interface{})
	if meta["custom"] != "value" {
		t.Errorf("Expected meta.custom='value', got %v", meta["custom"])
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
}

func TestWebSocketPtyState(t *testing.T) {
	initTestDB()

	sessionsMu.Lock()
	sessions = make(map[string]*Session)
	sessionsMu.Unlock()

	subsMu.Lock()
	ptySubscribers = make(map[*SafeConn]bool)
	subsMu.Unlock()

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

	if session.LastRows != 30 || session.LastCols != 100 {
		t.Errorf("Expected size 30x100, got %dx%d", session.LastRows, session.LastCols)
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
