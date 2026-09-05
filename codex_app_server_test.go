package main

import (
	"encoding/binary"
	"io"
	"net"
	"path/filepath"
	"testing"
	"time"
)

func TestShouldUseCodexAppServer(t *testing.T) {
	tests := []struct {
		name string
		cmd  []string
		want bool
	}{
		{name: "plain codex", cmd: []string{"codex"}, want: true},
		{name: "codex flags", cmd: []string{"/usr/local/bin/codex", "--full-auto"}, want: true},
		{name: "already remote", cmd: []string{"codex", "--remote", "unix:///x"}, want: false},
		{name: "already remote equals", cmd: []string{"codex", "--remote=unix:///x"}, want: false},
		{name: "app server", cmd: []string{"codex", "app-server"}, want: false},
		{name: "canonical wrapper", cmd: []string{"codexs", "--ab-label", "payments"}, want: true},
		{name: "shell", cmd: []string{"bash"}, want: false},
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			if got := shouldUseCodexAppServer(test.cmd); got != test.want {
				t.Fatalf("shouldUseCodexAppServer(%q) = %v, want %v", test.cmd, got, test.want)
			}
		})
	}
}

func TestPreferCodexResumeLast(t *testing.T) {
	projectPath := "/srv/projects/payments"
	tests := []struct {
		name string
		cmd  []string
		want []string
	}{
		{name: "bare codex", cmd: []string{"codex"}, want: []string{"codex", "-C", projectPath, "resume", "--last"}},
		{name: "absolute codex", cmd: []string{"/usr/local/bin/codex"}, want: []string{"/usr/local/bin/codex", "-C", projectPath, "resume", "--last"}},
		{name: "explicit resume", cmd: []string{"codex", "resume", "thread-id"}, want: []string{"codex", "resume", "thread-id"}},
		{name: "prompt", cmd: []string{"codex", "fix the tests"}, want: []string{"codex", "fix the tests"}},
		{name: "other command", cmd: []string{"bash"}, want: []string{"bash"}},
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			got := preferCodexResumeLast(test.cmd, projectPath)
			if len(got) != len(test.want) {
				t.Fatalf("preferCodexResumeLast(%q) = %q, want %q", test.cmd, got, test.want)
			}
			for index := range test.want {
				if got[index] != test.want[index] {
					t.Fatalf("preferCodexResumeLast(%q) = %q, want %q", test.cmd, got, test.want)
				}
			}
		})
	}
}

func TestShouldRelaunchAICmd(t *testing.T) {
	tests := []struct {
		name      string
		shellOnly bool
		launchCmd []string
		aiCmd     string
		want      bool
	}{
		{name: "manually launched from shell", shellOnly: true, aiCmd: "codex", want: true},
		{name: "app launch already starts codex", shellOnly: true, launchCmd: []string{"codex"}, aiCmd: "codex", want: false},
		{name: "no tracked command", shellOnly: true, want: false},
		{name: "dedicated claude session", shellOnly: false, aiCmd: "claude", want: false},
	}

	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			if got := shouldRelaunchAICmd(test.shellOnly, test.launchCmd, test.aiCmd); got != test.want {
				t.Fatalf("shouldRelaunchAICmd(%v, %q, %q) = %v, want %v", test.shellOnly, test.launchCmd, test.aiCmd, got, test.want)
			}
		})
	}
}

func TestCodexAppServerStatusEvents(t *testing.T) {
	const sessionID = "pty_codex_status_test"
	clearAiStatusForTest(sessionID)
	t.Cleanup(func() { clearAiStatusForTest(sessionID) })

	assertEventStatus(t, sessionID,
		`{"method":"thread/status/changed","params":{"threadId":"main","status":{"type":"idle"}}}`,
		"idle")
	assertEventStatus(t, sessionID,
		`{"method":"thread/status/changed","params":{"threadId":"main","status":{"type":"active","activeFlags":[]}}}`,
		"working")
	assertEventStatus(t, sessionID,
		`{"method":"thread/status/changed","params":{"threadId":"main","status":{"type":"active","activeFlags":["waitingOnApproval"]}}}`,
		"idle")
	assertEventStatus(t, sessionID,
		`{"method":"turn/started","params":{"threadId":"main","turn":{"status":"inProgress"}}}`,
		"working")
	assertEventStatus(t, sessionID,
		`{"method":"thread/started","params":{"thread":{"id":"main","status":{"type":"active","activeFlags":[]}}}}`,
		"working")
	assertEventStatus(t, sessionID,
		`{"method":"turn/completed","params":{"threadId":"main","turn":{"status":"completed"}}}`,
		"idle")
}

func TestCodexAppServerAggregatesConcurrentThreads(t *testing.T) {
	const sessionID = "pty_codex_multi_thread_test"
	clearAiStatusForTest(sessionID)
	t.Cleanup(func() { clearAiStatusForTest(sessionID) })

	assertEventStatus(t, sessionID,
		`{"method":"turn/started","params":{"threadId":"main","turn":{"status":"inProgress"}}}`,
		"working")
	assertEventStatus(t, sessionID,
		`{"method":"turn/started","params":{"threadId":"subagent","turn":{"status":"inProgress"}}}`,
		"working")
	assertEventStatus(t, sessionID,
		`{"method":"turn/completed","params":{"threadId":"subagent","turn":{"status":"completed"}}}`,
		"working")
	assertEventStatus(t, sessionID,
		`{"method":"turn/completed","params":{"threadId":"main","turn":{"status":"completed"}}}`,
		"idle")
}

func TestAuthoritativeStatusDoesNotExpire(t *testing.T) {
	const sessionID = "pty_codex_expiry_test"
	clearAiStatusForTest(sessionID)
	t.Cleanup(func() { clearAiStatusForTest(sessionID) })

	aiStatusMu.Lock()
	aiStatuses[sessionID] = aiStatusEntry{
		Status:        "working",
		UpdatedAt:     time.Now().Add(-time.Hour),
		Authoritative: true,
	}
	aiStatusMu.Unlock()

	if got := getAiStatus(sessionID); got != "working" {
		t.Fatalf("getAiStatus() = %q, want authoritative working status", got)
	}
}

func TestStringSliceFromJSON(t *testing.T) {
	got := stringSliceFromJSON([]interface{}{"codex", "--full-auto"})
	if len(got) != 2 || got[0] != "codex" || got[1] != "--full-auto" {
		t.Fatalf("stringSliceFromJSON() = %#v", got)
	}
	if got := stringSliceFromJSON([]interface{}{"codex", 1}); got != nil {
		t.Fatalf("stringSliceFromJSON() accepted non-string value: %#v", got)
	}
}

func TestLoginExecCommandPreservesArguments(t *testing.T) {
	cmd := loginExecCommand([]string{"codex", "--model", "name with spaces"})
	want := []string{"bash", "--login", "-i", "-c", `exec "$@"`, "ab-codex", "codex", "--model", "name with spaces"}
	if len(cmd.Args) != len(want) {
		t.Fatalf("loginExecCommand args = %#v, want %#v", cmd.Args, want)
	}
	for index := range want {
		if cmd.Args[index] != want[index] {
			t.Fatalf("loginExecCommand arg %d = %q, want %q", index, cmd.Args[index], want[index])
		}
	}
}

func TestCodexProxyForwardsWebSocketAndObservesStatus(t *testing.T) {
	const sessionID = "pty_codex_proxy_test"
	runtimeDir := t.TempDir()
	serverSocket := filepath.Join(runtimeDir, "server.sock")
	proxySocket := filepath.Join(runtimeDir, "client.sock")

	serverListener, err := net.Listen("unix", serverSocket)
	if err != nil {
		t.Fatal(err)
	}
	defer serverListener.Close()
	proxyListener, err := net.Listen("unix", proxySocket)
	if err != nil {
		t.Fatal(err)
	}

	runtime := &codexAppServerRuntime{
		sessionID:    sessionID,
		serverSocket: serverSocket,
		proxySocket:  proxySocket,
		runtimeDir:   runtimeDir,
		listener:     proxyListener,
	}
	go runtime.acceptLoop()
	defer runtime.stop()

	request := `{"id":1,"method":"initialize","params":{}}`
	response := `{"method":"thread/status/changed","params":{"status":{"type":"active","activeFlags":[]}}}`
	handshake := "HTTP/1.1 101 Switching Protocols\r\nConnection: Upgrade\r\nUpgrade: websocket\r\n\r\n"
	responseFrame := testWebSocketTextFrame(response)
	wireResponse := append([]byte(handshake), responseFrame...)
	serverErr := make(chan error, 1)
	go func() {
		conn, err := serverListener.Accept()
		if err != nil {
			serverErr <- err
			return
		}
		defer conn.Close()
		got := make([]byte, len(request))
		if _, err := io.ReadFull(conn, got); err != nil {
			serverErr <- err
			return
		}
		if string(got) != request {
			serverErr <- &proxyTestError{got: string(got), want: request}
			return
		}
		_, err = conn.Write(wireResponse)
		serverErr <- err
	}()

	client, err := net.Dial("unix", proxySocket)
	if err != nil {
		t.Fatal(err)
	}
	defer client.Close()
	if _, err := client.Write([]byte(request)); err != nil {
		t.Fatal(err)
	}
	_ = client.SetReadDeadline(time.Now().Add(time.Second))
	got := make([]byte, len(wireResponse))
	if _, err := io.ReadFull(client, got); err != nil {
		t.Fatalf("read proxied response: %v", err)
	}
	if string(got) != string(wireResponse) {
		t.Fatalf("proxied response = %q, want %q", got, wireResponse)
	}
	if err := <-serverErr; err != nil {
		t.Fatal(err)
	}
	statusDeadline := time.Now().Add(time.Second)
	for {
		entry, ok := getAiStatusEntry(sessionID)
		if ok && entry.Status == "working" && entry.Authoritative {
			break
		}
		if time.Now().After(statusDeadline) {
			t.Fatalf("proxied event status = %#v, present=%v", entry, ok)
		}
		time.Sleep(time.Millisecond)
	}
}

func TestCodexObserverResynchronizesAfterOversizedFrame(t *testing.T) {
	const sessionID = "pty_codex_oversized_frame_test"
	clearAiStatusForTest(sessionID)
	t.Cleanup(func() { clearAiStatusForTest(sessionID) })

	observer := &codexWebSocketObserver{
		sessionID:         sessionID,
		handshakeComplete: true,
	}
	payloadLength := uint64(maxCodexObservedMessage + 1)
	header := make([]byte, 10)
	header[0] = 0x81
	header[1] = 127
	binary.BigEndian.PutUint64(header[2:], payloadLength)
	if _, err := observer.Write(header); err != nil {
		t.Fatal(err)
	}

	chunk := make([]byte, 64<<10)
	for remaining := payloadLength; remaining > 0; {
		amount := uint64(len(chunk))
		if amount > remaining {
			amount = remaining
		}
		if _, err := observer.Write(chunk[:amount]); err != nil {
			t.Fatal(err)
		}
		remaining -= amount
	}

	status := `{"method":"turn/started","params":{"threadId":"main"}}`
	if _, err := observer.Write(testWebSocketTextFrame(status)); err != nil {
		t.Fatal(err)
	}
	entry, ok := getAiStatusEntry(sessionID)
	if !ok || !entry.Authoritative || entry.Status != "working" {
		t.Fatalf("status after oversized frame = %#v, present=%v", entry, ok)
	}
}

func testWebSocketTextFrame(payload string) []byte {
	if len(payload) < 126 {
		return append([]byte{0x81, byte(len(payload))}, payload...)
	}
	frame := []byte{0x81, 126, 0, 0}
	binary.BigEndian.PutUint16(frame[2:4], uint16(len(payload)))
	return append(frame, payload...)
}

type proxyTestError struct {
	got  string
	want string
}

func (err *proxyTestError) Error() string {
	return "proxied request mismatch: got " + err.got + ", want " + err.want
}

func assertEventStatus(t *testing.T, sessionID, event, want string) {
	t.Helper()
	handleCodexAppServerMessage(sessionID, []byte(event+"\n"))
	entry, ok := getAiStatusEntry(sessionID)
	if !ok {
		t.Fatal("status event did not create an AI status entry")
	}
	if !entry.Authoritative {
		t.Fatal("app-server status was not marked authoritative")
	}
	if entry.Status != want {
		t.Fatalf("event status = %q, want %q", entry.Status, want)
	}
}

func clearAiStatusForTest(sessionID string) {
	clearCodexActivity(sessionID)
	aiStatusMu.Lock()
	delete(aiStatuses, sessionID)
	aiStatusMu.Unlock()
}
