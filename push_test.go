package main

import (
	"strings"
	"testing"
	"unicode/utf8"
)

func TestAuthoritativeCompletionRequiresWorkingToIdleEdge(t *testing.T) {
	tests := []struct {
		name string
		prev aiStatusEntry
		had  bool
		next string
		want bool
	}{
		{"real completion", aiStatusEntry{Status: "working", Authoritative: true}, true, "idle", true},
		{"initial idle", aiStatusEntry{}, false, "idle", false},
		{"repeated idle", aiStatusEntry{Status: "idle", Authoritative: true}, true, "idle", false},
		{"heuristic status", aiStatusEntry{Status: "working"}, true, "idle", false},
		{"still working", aiStatusEntry{Status: "working", Authoritative: true}, true, "working", false},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			if got := authoritativeCompletion(test.prev, test.had, test.next); got != test.want {
				t.Fatalf("got %v, want %v", got, test.want)
			}
		})
	}
}

func TestPushCompletionMessageIsWhitespaceNormalizedAndUTF8Safe(t *testing.T) {
	const sessionID = "pty_push_message_test"
	t.Cleanup(func() { clearPushCompletionMessage(sessionID) })
	rememberPushCompletionMessage(sessionID, " one\n\n two\tthree ")
	if got := pushCompletionMessage(sessionID); got != "one two three" {
		t.Fatalf("normalized message = %q", got)
	}

	rememberPushCompletionMessage(sessionID, strings.Repeat("я", maxPushMessageBytes))
	got := pushCompletionMessage(sessionID)
	if !utf8.ValidString(got) || len(got) > maxPushMessageBytes {
		t.Fatalf("truncated message is invalid: bytes=%d valid=%v", len(got), utf8.ValidString(got))
	}
}
