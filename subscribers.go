package main

import (
	"log"
	"sync"
	"time"

	"github.com/gorilla/websocket"
)

// Live-state fan-out.
//
// The daemon pushes pty_state / board_items_changed frames to every
// /ws/pty-state subscriber. That used to be a plain loop that called
// WriteMessage on each subscriber in turn, from the goroutine that produced
// the event (the 3s ticker, an input handler, a board mutation). With no
// write deadline anywhere, gorilla/websocket blocks until the kernel send
// buffer drains, so a single client that stopped reading — a phone whose
// screen went off behind a relay, a laptop that suspended mid-frame — froze
// live state for *everyone* and pinned the producing goroutine forever.
//
// Each subscriber now owns a buffered channel and a writer goroutine. The
// producer only ever does a non-blocking send, so one stuck peer costs
// exactly one dropped subscriber and nothing else. A subscriber whose buffer
// overflows, or whose write exceeds the deadline, is unregistered and its
// connection closed — which also unblocks the reader goroutine parked in
// handlePtyState, so the subscriber set stops leaking entries that no longer
// correspond to a live client.
const (
	// wsWriteWait bounds a single websocket write. Without it a write can
	// block for the lifetime of the process.
	wsWriteWait = 10 * time.Second

	// stateSubBuffer is how many frames may queue up for one subscriber
	// before we call it hopeless. At one frame per 3s of ticker plus event
	// frames, 64 is many seconds of slack for a merely slow link and still
	// nothing for a dead one.
	stateSubBuffer = 64
)

// wsWriter is the slice of *SafeConn the fan-out actually needs. Having it as
// an interface keeps the fan-out testable without a real socket.
type wsWriter interface {
	WriteMessage(messageType int, data []byte) error
	Close() error
}

// stateSub is one /ws/pty-state subscriber plus its private write pump.
type stateSub struct {
	conn wsWriter
	send chan []byte
	done chan struct{}
	once sync.Once
}

func newStateSub(conn wsWriter) *stateSub {
	s := &stateSub{
		conn: conn,
		send: make(chan []byte, stateSubBuffer),
		done: make(chan struct{}),
	}
	go s.writeLoop()
	return s
}

func (s *stateSub) writeLoop() {
	for {
		select {
		case <-s.done:
			return
		case msg := <-s.send:
			if err := s.conn.WriteMessage(websocket.TextMessage, msg); err != nil {
				s.stop("write failed: " + err.Error())
				return
			}
		}
	}
}

// enqueue never blocks. That is the whole point: the caller is a shared
// producer goroutine and must not be able to inherit one client's stall.
func (s *stateSub) enqueue(msg []byte) {
	select {
	case <-s.done:
	case s.send <- msg:
	default:
		s.stop("buffer full (slow client)")
	}
}

// stop unregisters the subscriber and closes its connection. Idempotent: it
// is reached from the write pump, from the reader goroutine on disconnect,
// and from shutdown.
func (s *stateSub) stop(reason string) {
	s.once.Do(func() {
		close(s.done)
		unregisterStateSub(s)
		s.conn.Close()
		log.Printf("pty-state: subscriber dropped — %s", reason)
	})
}

func registerStateSub(s *stateSub) {
	subsMu.Lock()
	ptySubscribers[s] = true
	subsMu.Unlock()
}

func unregisterStateSub(s *stateSub) {
	subsMu.Lock()
	delete(ptySubscribers, s)
	subsMu.Unlock()
}

// snapshotStateSubs copies the subscriber set so writes happen outside the
// lock (a write pump that drops itself takes the same lock).
func snapshotStateSubs() []*stateSub {
	subsMu.RLock()
	subs := make([]*stateSub, 0, len(ptySubscribers))
	for s := range ptySubscribers {
		subs = append(subs, s)
	}
	subsMu.RUnlock()
	return subs
}

func fanoutStateFrame(msg []byte) {
	for _, s := range snapshotStateSubs() {
		s.enqueue(msg)
	}
}
