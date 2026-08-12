package main

import (
	"sync"
	"testing"
	"time"
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
