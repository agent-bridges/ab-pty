package main

import "testing"

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
