package main

import (
	"encoding/binary"
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"os"
	"strings"
	"testing"
	"time"

	"github.com/gorilla/websocket"
	"github.com/klauspost/compress/zstd"
)

func addTerminalCodecTestSession(t *testing.T, id string, scrollback []string, projectPath string) *Session {
	t.Helper()
	ptyFile, err := os.OpenFile(os.DevNull, os.O_RDWR, 0)
	if err != nil {
		t.Fatal(err)
	}
	session := &Session{
		ID:          id,
		Name:        id,
		ProjectPath: projectPath,
		Alive:       true,
		Pty:         ptyFile,
		Clients:     make(map[*SafeConn]bool),
		Scrollback:  append([]string(nil), scrollback...),
		OutputSeq:   uint64(len(scrollback)),
		LastRows:    24,
		LastCols:    80,
	}
	sessionsMu.Lock()
	sessions[id] = session
	sessionsMu.Unlock()
	t.Cleanup(func() {
		sessionsMu.Lock()
		delete(sessions, id)
		sessionsMu.Unlock()
		ptyFile.Close()
	})
	return session
}

func dialTerminalCodecTest(t *testing.T) (*websocket.Conn, func()) {
	t.Helper()
	server := httptest.NewServer(http.HandlerFunc(handleWebSocket))
	ws, _, err := websocket.DefaultDialer.Dial("ws"+strings.TrimPrefix(server.URL, "http"), nil)
	if err != nil {
		server.Close()
		t.Fatal(err)
	}
	ws.SetReadDeadline(time.Now().Add(3 * time.Second))
	return ws, func() {
		ws.Close()
		server.Close()
	}
}

func readTerminalJSONFrame(t *testing.T, ws *websocket.Conn, wantMessageType int) map[string]interface{} {
	t.Helper()
	messageType, data, err := ws.ReadMessage()
	if err != nil {
		t.Fatal(err)
	}
	if messageType != wantMessageType {
		t.Fatalf("websocket message type=%d, want %d; payload prefix=%q", messageType, wantMessageType, data[:min(len(data), 32)])
	}
	var frame map[string]interface{}
	if err := json.Unmarshal(data, &frame); err != nil {
		t.Fatalf("decode JSON frame: %v", err)
	}
	return frame
}

func readTerminalZstdFrame(t *testing.T, ws *websocket.Conn, decoder *zstd.Decoder) map[string]interface{} {
	t.Helper()
	messageType, data, err := ws.ReadMessage()
	if err != nil {
		t.Fatal(err)
	}
	if messageType != websocket.BinaryMessage {
		t.Fatalf("websocket message type=%d, want Binary; payload prefix=%q", messageType, data[:min(len(data), 32)])
	}
	if len(data) < 8 || string(data[:4]) != string(terminalZstdMagic[:]) {
		t.Fatalf("invalid ABZ1 header: %x", data[:min(len(data), 8)])
	}
	wantLen := binary.BigEndian.Uint32(data[4:8])
	if wantLen > terminalMaxUncompressed {
		t.Fatalf("advertised uncompressed length=%d exceeds limit", wantLen)
	}
	decoded, err := decoder.DecodeAll(data[8:], nil)
	if err != nil {
		t.Fatalf("decode zstd payload: %v", err)
	}
	if len(decoded) != int(wantLen) {
		t.Fatalf("decoded length=%d, ABZ1 length=%d", len(decoded), wantLen)
	}
	var frame map[string]interface{}
	if err := json.Unmarshal(decoded, &frame); err != nil {
		t.Fatalf("decode compressed JSON frame: %v", err)
	}
	return frame
}

func TestWebSocketRejectsUnknownOutputCodec(t *testing.T) {
	ws, closeTest := dialTerminalCodecTest(t)
	defer closeTest()

	if err := ws.WriteJSON(map[string]interface{}{
		"action":       "attach",
		"pty_id":       "unused",
		"output_codec": "unknown-v1",
	}); err != nil {
		t.Fatal(err)
	}
	frame := readTerminalJSONFrame(t, ws, websocket.TextMessage)
	if frame["type"] != "error" || !strings.Contains(frame["message"].(string), "unsupported output_codec") {
		t.Fatalf("unexpected negotiation error: %v", frame)
	}
	if _, _, err := ws.ReadMessage(); err == nil {
		t.Fatal("connection remained open after unsupported output codec")
	}
}

func TestWebSocketZstdOutputNegotiationAndReplayOrdering(t *testing.T) {
	largeReplay := strings.Repeat("R", terminalZstdThreshold*2)
	// A deliberately large non-output ready frame proves that frame type, not
	// size alone, decides whether a message is compressed.
	session := addTerminalCodecTestSession(
		t,
		"pty_zstd_replay_test",
		[]string{largeReplay},
		strings.Repeat("/project", 200),
	)
	ws, closeTest := dialTerminalCodecTest(t)
	defer closeTest()
	decoder, err := zstd.NewReader(nil)
	if err != nil {
		t.Fatal(err)
	}
	defer decoder.Close()

	if err := ws.WriteJSON(map[string]interface{}{
		"action":             "attach",
		"pty_id":             session.ID,
		"rows":               24,
		"cols":               80,
		"request_scrollback": false,
		"scrollback_limit":   1,
		"output_codec":       terminalOutputCodecZstdV1,
	}); err != nil {
		t.Fatal(err)
	}

	// Negotiated clients receive confirmation before any replay output.
	ready := readTerminalJSONFrame(t, ws, websocket.TextMessage)
	if ready["type"] != "ready" || ready["output_codec"] != terminalOutputCodecZstdV1 {
		t.Fatalf("unexpected ready frame: %v", ready)
	}
	if clear := readTerminalJSONFrame(t, ws, websocket.TextMessage); clear["type"] != "clear" {
		t.Fatalf("frame after ready=%v, want clear", clear)
	}
	output := readTerminalZstdFrame(t, ws, decoder)
	if output["type"] != "output" || output["data"] != largeReplay {
		t.Fatalf("unexpected compressed replay output: type=%v data-len=%d", output["type"], len(output["data"].(string)))
	}
	info := readTerminalJSONFrame(t, ws, websocket.TextMessage)
	if info["type"] != "scrollback_info" || info["returned_chunks"] != float64(1) {
		t.Fatalf("unexpected replay metadata: %v", info)
	}

	// The replay watermark still suppresses a delayed broadcast of the chunk
	// already included in the atomic ready-following replay batch.
	broadcastPtyOutput(session, 1, map[string]interface{}{"type": "output", "data": largeReplay})
	if err := ws.WriteJSON(map[string]string{"type": "ping"}); err != nil {
		t.Fatal(err)
	}
	if pong := readTerminalJSONFrame(t, ws, websocket.TextMessage); pong["type"] != "pong" {
		t.Fatalf("delayed replay duplicate was not suppressed; next frame=%v", pong)
	}

	// Below the threshold output stays Text.
	session.mu.Lock()
	smallSeq := appendScrollbackChunkLocked(session, "small")
	session.mu.Unlock()
	broadcastPtyOutput(session, smallSeq, map[string]interface{}{"type": "output", "data": "small"})
	if small := readTerminalJSONFrame(t, ws, websocket.TextMessage); small["type"] != "output" || small["data"] != "small" {
		t.Fatalf("unexpected small output: %v", small)
	}

	// The threshold is inclusive and applies to serialized JSON length.
	emptyJSON, err := json.Marshal(map[string]interface{}{"type": "output", "data": ""})
	if err != nil {
		t.Fatal(err)
	}
	exactData := strings.Repeat("T", terminalZstdThreshold-len(emptyJSON))
	exactJSON, err := json.Marshal(map[string]interface{}{"type": "output", "data": exactData})
	if err != nil {
		t.Fatal(err)
	}
	if len(exactJSON) != terminalZstdThreshold {
		t.Fatalf("test setup serialized length=%d, want %d", len(exactJSON), terminalZstdThreshold)
	}
	session.mu.Lock()
	exactSeq := appendScrollbackChunkLocked(session, exactData)
	session.mu.Unlock()
	broadcastPtyOutput(session, exactSeq, map[string]interface{}{"type": "output", "data": exactData})
	if exact := readTerminalZstdFrame(t, ws, decoder); exact["data"] != exactData {
		t.Fatalf("threshold output did not round-trip")
	}
}

func TestWebSocketWithoutOutputCodecPreservesLegacyReplayProtocol(t *testing.T) {
	largeReplay := strings.Repeat("L", terminalZstdThreshold*2)
	session := addTerminalCodecTestSession(
		t,
		"pty_legacy_replay_test",
		[]string{largeReplay},
		"/tmp",
	)
	ws, closeTest := dialTerminalCodecTest(t)
	defer closeTest()

	if err := ws.WriteJSON(map[string]interface{}{
		"action":             "attach",
		"pty_id":             session.ID,
		"request_scrollback": false,
		"scrollback_limit":   1,
	}); err != nil {
		t.Fatal(err)
	}

	if clear := readTerminalJSONFrame(t, ws, websocket.TextMessage); clear["type"] != "clear" {
		t.Fatalf("first legacy frame=%v, want clear", clear)
	}
	if output := readTerminalJSONFrame(t, ws, websocket.TextMessage); output["type"] != "output" || output["data"] != largeReplay {
		t.Fatalf("unexpected legacy output: %v", output)
	}
	if info := readTerminalJSONFrame(t, ws, websocket.TextMessage); info["type"] != "scrollback_info" {
		t.Fatalf("unexpected legacy metadata: %v", info)
	}
	ready := readTerminalJSONFrame(t, ws, websocket.TextMessage)
	if ready["type"] != "ready" {
		t.Fatalf("last legacy frame=%v, want ready", ready)
	}
	if _, present := ready["output_codec"]; present {
		t.Fatalf("legacy ready unexpectedly advertises output codec: %v", ready)
	}
}
