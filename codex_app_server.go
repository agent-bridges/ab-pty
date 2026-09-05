package main

import (
	"bytes"
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"log"
	"net"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"sync"
	"syscall"
	"time"
)

// codexAppServerRuntime owns one app-server and one transparent Unix socket
// proxy. Keeping it per PTY makes every status event unambiguously attributable
// to that PTY, even when several Codex sessions share the same working tree.
type codexAppServerRuntime struct {
	sessionID    string
	serverCmd    *exec.Cmd
	serverSocket string
	proxySocket  string
	runtimeDir   string
	listener     net.Listener
	stopOnce     sync.Once
}

var (
	codexRuntimesMu     sync.Mutex
	codexRuntimes       = map[string]*codexAppServerRuntime{}
	codexRuntimeStartMu sync.Mutex

	// One Codex app-server may own several threads at once (the visible
	// conversation plus sub-agents). Status notifications are scoped to a
	// thread, not to the app-server connection. Keep that scope here so a
	// completed child turn cannot paint the whole PTY idle while another
	// thread is still working.
	codexActivityMu sync.Mutex
	codexActivities = map[string]map[string]bool{}
)

const anonymousCodexThread = "_anonymous"

func shouldUseCodexAppServer(customCmd []string) bool {
	if len(customCmd) == 0 {
		return false
	}
	binary := filepath.Base(customCmd[0])
	if binary != "codex" && binary != "codexs" {
		return false
	}
	for _, arg := range customCmd[1:] {
		if arg == "app-server" || arg == "--remote" || strings.HasPrefix(arg, "--remote=") {
			return false
		}
	}
	return true
}

// preferCodexResumeLast makes app-created bare Codex terminals continue the
// newest session associated with their working directory. Pass the directory
// explicitly instead of relying on the process cwd: in remote app-server mode
// the TUI and server are separate processes, and an interactive login profile
// may also change cwd before Codex parses `resume --last`. Explicit arguments
// are left alone so callers can still request a new prompted session or a
// specific Codex subcommand.
func preferCodexResumeLast(customCmd []string, projectPath string) []string {
	if len(customCmd) != 1 || filepath.Base(customCmd[0]) != "codex" {
		return customCmd
	}
	return []string{customCmd[0], "-C", projectPath, "resume", "--last"}
}

func codexRuntimeRoot() string {
	if dbPath := os.Getenv("AB_PTY_DATABASE"); dbPath != "" {
		return filepath.Join(filepath.Dir(dbPath), "codex-app-server")
	}
	return "/opt/ab/data/codex-app-server"
}

func codexRuntimeName(sessionID string) string {
	sum := sha256.Sum256([]byte(sessionID))
	return hex.EncodeToString(sum[:8])
}

// loginExecCommand gives app-created Codex sessions the same login profile as
// an ordinary AB shell. Positional parameters preserve every argument without
// shell interpolation, and exec makes Codex the process supervised by Cmd.
func loginExecCommand(args []string) *exec.Cmd {
	commandArgs := []string{"--login", "-i", "-c", `exec "$@"`, "ab-codex"}
	commandArgs = append(commandArgs, args...)
	return exec.Command("bash", commandArgs...)
}

func stringSliceFromJSON(value interface{}) []string {
	switch values := value.(type) {
	case []string:
		return append([]string(nil), values...)
	case []interface{}:
		result := make([]string, 0, len(values))
		for _, value := range values {
			text, ok := value.(string)
			if !ok {
				return nil
			}
			result = append(result, text)
		}
		return result
	default:
		return nil
	}
}

// startCodexAppServer starts the app-server and a proxy that tees server
// notifications into handleCodexAppServerMessage without changing the wire
// protocol seen by the Codex TUI. It returns the rewritten TUI command.
func startCodexAppServer(sessionID, projectPath string, env, customCmd []string) ([]string, error) {
	if !shouldUseCodexAppServer(customCmd) {
		return customCmd, nil
	}

	runtimeDir := filepath.Join(codexRuntimeRoot(), codexRuntimeName(sessionID))
	if err := os.MkdirAll(runtimeDir, 0700); err != nil {
		return customCmd, fmt.Errorf("create Codex app-server runtime dir: %w", err)
	}

	runtime := &codexAppServerRuntime{
		sessionID:    sessionID,
		serverSocket: filepath.Join(runtimeDir, "server.sock"),
		proxySocket:  filepath.Join(runtimeDir, "client.sock"),
		runtimeDir:   runtimeDir,
	}
	_ = os.Remove(runtime.serverSocket)
	_ = os.Remove(runtime.proxySocket)

	runtime.serverCmd = loginExecCommand([]string{customCmd[0], "app-server", "--listen", "unix://" + runtime.serverSocket})
	runtime.serverCmd.Dir = projectPath
	runtime.serverCmd.Env = env
	runtime.serverCmd.Stdout = io.Discard
	runtime.serverCmd.Stderr = log.Writer()
	runtime.serverCmd.SysProcAttr = &syscall.SysProcAttr{Pdeathsig: syscall.SIGTERM}
	if err := runtime.serverCmd.Start(); err != nil {
		runtime.cleanupFiles()
		return customCmd, fmt.Errorf("start Codex app-server: %w", err)
	}

	serverExited := make(chan error, 1)
	go func() { serverExited <- runtime.serverCmd.Wait() }()

	deadline := time.Now().Add(5 * time.Second)
	for {
		if _, err := os.Stat(runtime.serverSocket); err == nil {
			break
		}
		select {
		case err := <-serverExited:
			runtime.cleanupFiles()
			if err == nil {
				err = errors.New("exited before creating its socket")
			}
			return customCmd, fmt.Errorf("Codex app-server: %w", err)
		default:
		}
		if time.Now().After(deadline) {
			_ = runtime.serverCmd.Process.Kill()
			runtime.cleanupFiles()
			return customCmd, errors.New("Codex app-server socket timeout")
		}
		time.Sleep(25 * time.Millisecond)
	}

	listener, err := net.Listen("unix", runtime.proxySocket)
	if err != nil {
		_ = runtime.serverCmd.Process.Kill()
		runtime.cleanupFiles()
		return customCmd, fmt.Errorf("listen on Codex proxy socket: %w", err)
	}
	runtime.listener = listener

	codexRuntimesMu.Lock()
	codexRuntimes[sessionID] = runtime
	codexRuntimesMu.Unlock()

	resetCodexActivity(sessionID)
	go runtime.acceptLoop()
	go func() {
		err := <-serverExited
		if err != nil && !errors.Is(err, os.ErrProcessDone) {
			log.Printf("Codex app-server for %s exited: %v", sessionID, err)
		}
		runtime.stop()
	}()

	rewritten := []string{customCmd[0], "--remote", "unix://" + runtime.proxySocket}
	rewritten = append(rewritten, customCmd[1:]...)
	return rewritten, nil
}

// ensureCodexAppServer gives both app-created Codex terminals and a manual
// `codexs` launched from an existing shell the same daemon-owned runtime. A
// PTY has at most one app-server; later Codex launches reuse its proxy socket.
func ensureCodexAppServer(sessionID, projectPath string, env, customCmd []string) ([]string, error) {
	if !shouldUseCodexAppServer(customCmd) {
		return customCmd, nil
	}

	codexRuntimeStartMu.Lock()
	defer codexRuntimeStartMu.Unlock()

	codexRuntimesMu.Lock()
	runtime := codexRuntimes[sessionID]
	codexRuntimesMu.Unlock()
	if runtime != nil {
		rewritten := []string{customCmd[0], "--remote", "unix://" + runtime.proxySocket}
		return append(rewritten, customCmd[1:]...), nil
	}

	return startCodexAppServer(sessionID, projectPath, env, customCmd)
}

func (runtime *codexAppServerRuntime) acceptLoop() {
	for {
		client, err := runtime.listener.Accept()
		if err != nil {
			return
		}
		go runtime.proxy(client)
	}
}

func (runtime *codexAppServerRuntime) proxy(client net.Conn) {
	server, err := net.Dial("unix", runtime.serverSocket)
	if err != nil {
		_ = client.Close()
		return
	}
	defer client.Close()
	defer server.Close()

	go func() {
		observer := &codexWebSocketObserver{sessionID: runtime.sessionID, clientMessages: true}
		_, _ = io.Copy(io.MultiWriter(server, observer), client)
		if unixConn, ok := server.(*net.UnixConn); ok {
			_ = unixConn.CloseWrite()
		}
	}()

	observer := &codexWebSocketObserver{sessionID: runtime.sessionID}
	_, _ = io.Copy(io.MultiWriter(client, observer), server)
}

const maxCodexObservedMessage = 16 << 20

// codexWebSocketObserver passively decodes server-to-TUI WebSocket text
// frames. The actual bytes are forwarded by MultiWriter before this observer
// sees them, so a parser bug cannot alter the terminal protocol.
type codexWebSocketObserver struct {
	sessionID         string
	clientMessages    bool
	buffer            []byte
	handshakeComplete bool
	fragmentedMessage []byte
	skippedPayload    uint64
	skippingFragment  bool
	tracedFrames      int
}

func codexAppServerTraceEnabled(sessionID string) bool {
	if os.Getenv("AB_PTY_CODEX_APP_SERVER_TRACE") != "1" {
		return false
	}
	target := strings.TrimSpace(os.Getenv("AB_PTY_CODEX_APP_SERVER_TRACE_PTY"))
	return target == "" || target == sessionID
}

func (observer *codexWebSocketObserver) Write(data []byte) (int, error) {
	written := len(data)
	observer.buffer = append(observer.buffer, data...)

	if !observer.handshakeComplete {
		headerEnd := bytes.Index(observer.buffer, []byte("\r\n\r\n"))
		if headerEnd < 0 {
			if len(observer.buffer) > 64<<10 {
				observer.buffer = nil
			}
			return written, nil
		}
		observer.buffer = append([]byte(nil), observer.buffer[headerEnd+4:]...)
		observer.handshakeComplete = true
		if codexAppServerTraceEnabled(observer.sessionID) {
			log.Printf("Codex app-server websocket ready pty=%s", observer.sessionID)
		}
	}

	for {
		if observer.skippedPayload > 0 {
			available := uint64(len(observer.buffer))
			if available > observer.skippedPayload {
				available = observer.skippedPayload
			}
			observer.buffer = observer.buffer[available:]
			observer.skippedPayload -= available
			if observer.skippedPayload > 0 {
				break
			}
		}
		if !observer.consumeFrame() {
			break
		}
	}
	return written, nil
}

func (observer *codexWebSocketObserver) consumeFrame() bool {
	if len(observer.buffer) < 2 {
		return false
	}

	first, second := observer.buffer[0], observer.buffer[1]
	final := first&0x80 != 0
	opcode := first & 0x0f
	masked := second&0x80 != 0
	payloadLength := uint64(second & 0x7f)
	headerLength := 2

	switch payloadLength {
	case 126:
		if len(observer.buffer) < 4 {
			return false
		}
		payloadLength = uint64(binary.BigEndian.Uint16(observer.buffer[2:4]))
		headerLength = 4
	case 127:
		if len(observer.buffer) < 10 {
			return false
		}
		payloadLength = binary.BigEndian.Uint64(observer.buffer[2:10])
		headerLength = 10
	}
	if masked {
		headerLength += 4
	}
	if codexAppServerTraceEnabled(observer.sessionID) && observer.tracedFrames < 32 {
		observer.tracedFrames++
		log.Printf(
			"Codex app-server frame pty=%s number=%d opcode=%d final=%t masked=%t payload=%d buffered=%d",
			observer.sessionID, observer.tracedFrames, opcode, final, masked, payloadLength, len(observer.buffer),
		)
	}

	if payloadLength > maxCodexObservedMessage {
		if len(observer.buffer) < headerLength {
			return false
		}
		// App-server startup responses can be tens of megabytes (for example,
		// config/tool metadata). We do not need their payload, but we must skip
		// it by its declared frame length. Dropping the current read buffer here
		// loses WebSocket frame alignment whenever the payload spans reads, which
		// also hides every later turn/started and turn/completed notification.
		observer.buffer = observer.buffer[headerLength:]
		observer.skippedPayload = payloadLength
		observer.fragmentedMessage = nil
		observer.skippingFragment = !final
		return true
	}
	frameLength := uint64(headerLength) + payloadLength
	if frameLength > uint64(len(observer.buffer)) {
		return false
	}

	payload := append([]byte(nil), observer.buffer[headerLength:int(frameLength)]...)
	if masked {
		mask := observer.buffer[headerLength-4 : headerLength]
		for index := range payload {
			payload[index] ^= mask[index%4]
		}
	}
	observer.buffer = append([]byte(nil), observer.buffer[frameLength:]...)

	switch opcode {
	case 0x1: // text
		if observer.skippingFragment {
			if final {
				observer.skippingFragment = false
			}
		} else if final {
			observer.observeMessage(payload)
		} else {
			observer.fragmentedMessage = append(observer.fragmentedMessage[:0], payload...)
		}
	case 0x0: // continuation
		if observer.skippingFragment {
			if final {
				observer.skippingFragment = false
			}
		} else {
			observer.fragmentedMessage = append(observer.fragmentedMessage, payload...)
			if len(observer.fragmentedMessage) > maxCodexObservedMessage {
				observer.fragmentedMessage = nil
				observer.skippingFragment = !final
			} else if final {
				observer.observeMessage(observer.fragmentedMessage)
				observer.fragmentedMessage = nil
			}
		}
	}
	return len(observer.buffer) > 0
}

func (observer *codexWebSocketObserver) observeMessage(payload []byte) {
	if observer.clientMessages {
		handleCodexClientMessage(observer.sessionID, payload)
	} else {
		handleCodexAppServerMessage(observer.sessionID, payload)
	}
}

// The TUI explicitly names its visible thread when resuming or sending input.
// Observe that tiny request, so even a huge skipped resume-history response
// cannot leave push ownership unknown. A thread/read response is NOT selection.
func handleCodexClientMessage(sessionID string, payload []byte) {
	var message struct {
		Method string `json:"method"`
		Params struct {
			ThreadID string `json:"threadId"`
		} `json:"params"`
	}
	if json.Unmarshal(payload, &message) != nil || message.Params.ThreadID == "" {
		return
	}
	switch message.Method {
	case "thread/resume", "turn/start", "turn/steer":
		selectCodexPushThreadID(sessionID, message.Params.ThreadID)
	}
}

func handleCodexAppServerMessage(sessionID string, line []byte) {
	var message struct {
		Method string          `json:"method"`
		Params json.RawMessage `json:"params"`
	}
	if err := json.Unmarshal(line, &message); err != nil {
		return
	}
	if message.Method == "" {
		return
	}
	if codexAppServerTraceEnabled(sessionID) {
		log.Printf("Codex app-server event pty=%s: %s", sessionID, string(line))
	}

	switch message.Method {
	case "item/completed":
		var params struct {
			ThreadID string `json:"threadId"`
			TurnID   string `json:"turnId"`
			Item     struct {
				Type  string `json:"type"`
				Text  string `json:"text"`
				Phase string `json:"phase"`
			} `json:"item"`
		}
		if json.Unmarshal(message.Params, &params) == nil &&
			params.Item.Type == "agentMessage" && params.Item.Phase == "final_answer" {
			recordCodexPushMessage(sessionID, params.ThreadID, params.TurnID, params.Item.Text)
		}
	case "thread/status/changed":
		var params struct {
			ThreadID string            `json:"threadId"`
			Status   codexThreadStatus `json:"status"`
		}
		if json.Unmarshal(message.Params, &params) != nil {
			return
		}
		applyCodexThreadStatus(sessionID, params.ThreadID, params.Status)
	case "thread/started":
		var raw struct {
			Thread json.RawMessage `json:"thread"`
		}
		if json.Unmarshal(message.Params, &raw) == nil {
			selectCodexPushThread(sessionID, raw.Thread)
		}
		var params struct {
			Thread struct {
				ID     string            `json:"id"`
				Status codexThreadStatus `json:"status"`
			} `json:"thread"`
		}
		if json.Unmarshal(message.Params, &params) == nil {
			applyCodexThreadStatus(sessionID, params.Thread.ID, params.Thread.Status)
		}
	case "turn/started":
		var params struct {
			ThreadID string `json:"threadId"`
			Turn     struct {
				ID string `json:"id"`
			} `json:"turn"`
		}
		if json.Unmarshal(message.Params, &params) == nil {
			beginCodexPushTurn(sessionID, params.ThreadID, params.Turn.ID)
		}
		setCodexThreadActivity(sessionID, codexThreadID(message.Params), true)
	case "turn/completed":
		setCodexThreadActivity(sessionID, codexThreadID(message.Params), false)
		var params struct {
			ThreadID string `json:"threadId"`
			Turn     struct {
				ID     string `json:"id"`
				Status string `json:"status"`
			} `json:"turn"`
		}
		if json.Unmarshal(message.Params, &params) == nil {
			completeCodexPushTurn(sessionID, params.ThreadID, params.Turn.ID, params.Turn.Status)
		}
	}
}

type codexThreadStatus struct {
	Type        string   `json:"type"`
	ActiveFlags []string `json:"activeFlags"`
}

func codexThreadID(raw json.RawMessage) string {
	var params struct {
		ThreadID string `json:"threadId"`
	}
	_ = json.Unmarshal(raw, &params)
	return params.ThreadID
}

func applyCodexThreadStatus(sessionID, threadID string, status codexThreadStatus) {
	switch status.Type {
	case "active":
		// Waiting for an approval is waiting for the operator, not active work.
		for _, flag := range status.ActiveFlags {
			if flag == "waitingOnApproval" {
				setCodexThreadActivity(sessionID, threadID, false)
				return
			}
		}
		setCodexThreadActivity(sessionID, threadID, true)
	case "idle", "notLoaded", "systemError":
		setCodexThreadActivity(sessionID, threadID, false)
	}
}

func setCodexThreadActivity(sessionID, threadID string, active bool) {
	if threadID == "" {
		// Older app-server builds omitted threadId. Preserve their original
		// single-thread behaviour without letting that anonymous slot collide
		// with a real thread ID.
		threadID = anonymousCodexThread
	}

	codexActivityMu.Lock()
	threads := codexActivities[sessionID]
	if threads == nil && active {
		threads = map[string]bool{}
		codexActivities[sessionID] = threads
	}
	if active {
		threads[threadID] = true
	} else if threads != nil {
		delete(threads, threadID)
		if len(threads) == 0 {
			delete(codexActivities, sessionID)
		}
	}
	working := len(threads) > 0
	codexActivityMu.Unlock()

	if working {
		setAiStatusAuthoritative(sessionID, "working", "")
	} else {
		setAiStatusAuthoritative(sessionID, "idle", "")
	}
}

func resetCodexActivity(sessionID string) {
	codexActivityMu.Lock()
	delete(codexActivities, sessionID)
	codexActivityMu.Unlock()
	clearPushCompletionMessage(sessionID)
	setAiStatusAuthoritative(sessionID, "idle", "")
}

func clearCodexActivity(sessionID string) {
	codexActivityMu.Lock()
	delete(codexActivities, sessionID)
	codexActivityMu.Unlock()
}

func stopCodexAppServer(sessionID string) {
	codexRuntimesMu.Lock()
	runtime := codexRuntimes[sessionID]
	codexRuntimesMu.Unlock()
	if runtime != nil {
		runtime.stop()
	}
}

func (runtime *codexAppServerRuntime) stop() {
	runtime.stopOnce.Do(func() {
		if runtime.listener != nil {
			_ = runtime.listener.Close()
		}
		if runtime.serverCmd != nil && runtime.serverCmd.Process != nil {
			_ = runtime.serverCmd.Process.Signal(syscall.SIGTERM)
		}
		runtime.cleanupFiles()
		codexRuntimesMu.Lock()
		if codexRuntimes[runtime.sessionID] == runtime {
			delete(codexRuntimes, runtime.sessionID)
		}
		codexRuntimesMu.Unlock()
		clearCodexActivity(runtime.sessionID)
		clearAiStatus(runtime.sessionID)
	})
}

func (runtime *codexAppServerRuntime) cleanupFiles() {
	_ = os.Remove(runtime.proxySocket)
	_ = os.Remove(runtime.serverSocket)
	_ = os.Remove(runtime.runtimeDir)
}
