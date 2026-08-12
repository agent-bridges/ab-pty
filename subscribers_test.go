package main

import (
	"net/http"
	"net/http/httptest"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/gorilla/websocket"
)

// blockingWriter models the client that is gone but whose socket has not
// failed yet: every write parks until the test releases it. Before the
// per-subscriber write pump, a single one of these froze live state for every
// other client, because the broadcast wrote to subscribers sequentially in
// the producer's goroutine with no write deadline.
type blockingWriter struct {
	release chan struct{}
	mu      sync.Mutex
	closed  bool
}

func newBlockingWriter() *blockingWriter {
	return &blockingWriter{release: make(chan struct{})}
}

func (b *blockingWriter) WriteMessage(int, []byte) error {
	<-b.release
	return nil
}

func (b *blockingWriter) Close() error {
	b.mu.Lock()
	defer b.mu.Unlock()
	if !b.closed {
		b.closed = true
		close(b.release)
	}
	return nil
}

func (b *blockingWriter) isClosed() bool {
	b.mu.Lock()
	defer b.mu.Unlock()
	return b.closed
}

type recordingWriter struct {
	got chan []byte
}

func newRecordingWriter() *recordingWriter {
	return &recordingWriter{got: make(chan []byte, 256)}
}

func (r *recordingWriter) WriteMessage(_ int, data []byte) error {
	cp := append([]byte(nil), data...)
	select {
	case r.got <- cp:
	default:
	}
	return nil
}

func (r *recordingWriter) Close() error { return nil }

func resetStateSubs() {
	subsMu.Lock()
	ptySubscribers = make(map[*stateSub]bool)
	subsMu.Unlock()
}

func TestSlowSubscriberDoesNotStallOthers(t *testing.T) {
	resetStateSubs()
	defer resetStateSubs()

	slowConn := newBlockingWriter()
	slow := newStateSub(slowConn)
	registerStateSub(slow)
	defer slow.stop("test cleanup")

	fastConn := newRecordingWriter()
	fast := newStateSub(fastConn)
	registerStateSub(fast)
	defer fast.stop("test cleanup")

	// More frames than one subscriber's buffer can hold, so the stalled peer
	// is not merely slow but hopeless.
	frames := stateSubBuffer + 10
	done := make(chan struct{})
	go func() {
		for i := 0; i < frames; i++ {
			broadcastBoardItemsChanged()
		}
		close(done)
	}()

	select {
	case <-done:
	case <-time.After(5 * time.Second):
		t.Fatal("broadcast blocked on the stalled subscriber")
	}

	// The healthy subscriber must have received every frame.
	for i := 0; i < frames; i++ {
		select {
		case <-fastConn.got:
		case <-time.After(5 * time.Second):
			t.Fatalf("fast subscriber only received %d of %d frames", i, frames)
		}
	}

	// And the stalled one must have been dropped and closed, so it stops
	// counting as a live subscriber.
	deadline := time.Now().Add(5 * time.Second)
	for {
		subsMu.RLock()
		_, still := ptySubscribers[slow]
		n := len(ptySubscribers)
		subsMu.RUnlock()
		if !still {
			if n != 1 {
				t.Fatalf("expected exactly the healthy subscriber to remain, got %d", n)
			}
			break
		}
		if time.Now().After(deadline) {
			t.Fatal("stalled subscriber was never dropped")
		}
		time.Sleep(10 * time.Millisecond)
	}

	if !slowConn.isClosed() {
		t.Fatal("stalled subscriber's connection was not closed")
	}
}

// withFastLiveness compresses the keepalive timings so liveness tests run in
// well under a second.
func withFastLiveness(t *testing.T, ping, pong time.Duration) {
	t.Helper()
	oldPing, oldPong := wsPingPeriod, wsPongWait
	wsPingPeriod, wsPongWait = ping, pong
	t.Cleanup(func() { wsPingPeriod, wsPongWait = oldPing, oldPong })
}

func countStateSubs() int {
	subsMu.RLock()
	defer subsMu.RUnlock()
	return len(ptySubscribers)
}

// A peer that stops answering must be torn down by the server. Before the
// server-side ping and read deadline, nothing on the daemon side ever noticed
// — the subscription lived until the client closed it, which a relay endpoint
// holding a socket for a phone that is long gone never does.
func TestServerDropsSilentClient(t *testing.T) {
	initTestDB()
	resetStateSubs()
	defer resetStateSubs()
	withFastLiveness(t, 50*time.Millisecond, 200*time.Millisecond)

	srv := httptest.NewServer(http.HandlerFunc(handlePtyState))
	defer srv.Close()

	ws, _, err := websocket.DefaultDialer.Dial("ws"+strings.TrimPrefix(srv.URL, "http"), nil)
	if err != nil {
		t.Fatalf("dial: %v", err)
	}
	defer ws.Close()
	// Play dead: never answer a ping, never send anything.
	ws.SetPingHandler(func(string) error { return nil })

	closed := make(chan struct{})
	go func() {
		for {
			if _, _, err := ws.ReadMessage(); err != nil {
				close(closed)
				return
			}
		}
	}()

	select {
	case <-closed:
	case <-time.After(5 * time.Second):
		t.Fatal("server never closed the connection of a client that stopped answering")
	}

	deadline := time.Now().Add(5 * time.Second)
	for countStateSubs() != 0 {
		if time.Now().After(deadline) {
			t.Fatal("subscriber leaked after the connection died")
		}
		time.Sleep(10 * time.Millisecond)
	}
}

// The documented contract is that an honest client is never disconnected by
// the server. This is the client the spec describes: it pings on its own
// schedule and knows nothing about websocket control frames.
func TestServerKeepsClientThatOnlySendsAppPings(t *testing.T) {
	initTestDB()
	resetStateSubs()
	defer resetStateSubs()
	withFastLiveness(t, 50*time.Millisecond, 200*time.Millisecond)

	srv := httptest.NewServer(http.HandlerFunc(handlePtyState))
	defer srv.Close()

	ws, _, err := websocket.DefaultDialer.Dial("ws"+strings.TrimPrefix(srv.URL, "http"), nil)
	if err != nil {
		t.Fatalf("dial: %v", err)
	}
	defer ws.Close()
	// Deliberately ignore server pings: only the app-level ping keeps this
	// client alive, which is exactly what the spec promises is enough.
	ws.SetPingHandler(func(string) error { return nil })

	readErr := make(chan error, 1)
	go func() {
		for {
			if _, _, err := ws.ReadMessage(); err != nil {
				readErr <- err
				return
			}
		}
	}()

	// Five app-level pings, one per read-deadline period — well past the
	// point where a silent client would have been dropped.
	for i := 0; i < 5; i++ {
		if err := ws.WriteJSON(map[string]string{"type": "ping"}); err != nil {
			t.Fatalf("write %d: %v", i, err)
		}
		select {
		case err := <-readErr:
			t.Fatalf("server disconnected a client that pings: %v", err)
		case <-time.After(150 * time.Millisecond):
		}
	}

	if n := countStateSubs(); n != 1 {
		t.Fatalf("expected the subscriber to still be registered, got %d", n)
	}
}
