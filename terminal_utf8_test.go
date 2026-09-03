package main

import (
	"errors"
	"io"
	"strings"
	"testing"
	"unicode/utf8"
)

func TestTerminalUTF8StreamDecoderReassemblesEverySplitBoundary(t *testing.T) {
	tests := []string{
		"паролями",
		"до и после: пароль",
		"emoji: 😀🚀🧑‍💻",
		"\x1b[35mкириллица 😀\x1b[0m\r\n",
	}
	for _, text := range tests {
		bytes := []byte(text)
		for split := 0; split <= len(bytes); split++ {
			t.Run(text+"/split-"+itoa(split), func(t *testing.T) {
				decoder := terminalUTF8StreamDecoder{}
				got := decoder.Push(bytes[:split], false) + decoder.Push(bytes[split:], true)
				if got != text {
					t.Fatalf("split %d: got %q, want %q", split, got, text)
				}
				if !utf8.ValidString(got) {
					t.Fatalf("split %d produced invalid UTF-8: %x", split, []byte(got))
				}
			})
		}
	}
}

func TestTerminalUTF8StreamDecoderReassemblesByteByByte(t *testing.T) {
	const text = "паролями 😀🧑‍💻"
	decoder := terminalUTF8StreamDecoder{}
	var out strings.Builder
	for _, b := range []byte(text) {
		out.WriteString(decoder.Push([]byte{b}, false))
	}
	out.WriteString(decoder.Push(nil, true))
	if got := out.String(); got != text {
		t.Fatalf("got %q, want %q", got, text)
	}
}

func TestTerminalUTF8StreamDecoderWaitsForIncompleteRune(t *testing.T) {
	bytes := []byte("😀")
	decoder := terminalUTF8StreamDecoder{}
	for index := 0; index < len(bytes)-1; index++ {
		if got := decoder.Push(bytes[index:index+1], false); got != "" {
			t.Fatalf("byte %d was emitted before the rune completed: %q", index, got)
		}
	}
	if got := decoder.Push(bytes[len(bytes)-1:], false); got != "😀" {
		t.Fatalf("completed rune = %q, want emoji", got)
	}
}

func TestTerminalUTF8StreamDecoderReplacesOnlyMalformedInput(t *testing.T) {
	tests := []struct {
		name   string
		chunks [][]byte
		want   string
	}{
		{
			name:   "invalid lead byte",
			chunks: [][]byte{{'a', 0xff, 'b'}},
			want:   "a\ufffdb",
		},
		{
			name:   "invalid continuation across chunks",
			chunks: [][]byte{{0xe2}, {'x'}},
			want:   "\ufffdx",
		},
		{
			name:   "truncated sequence at eof",
			chunks: [][]byte{{'a', 0xf0, 0x9f, 0x98}},
			want:   "a\ufffd",
		},
		{
			name:   "stray continuation bytes",
			chunks: [][]byte{{0x80}, {0xbf}},
			want:   "\ufffd\ufffd",
		},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			decoder := terminalUTF8StreamDecoder{}
			var out strings.Builder
			for _, chunk := range test.chunks {
				out.WriteString(decoder.Push(chunk, false))
			}
			out.WriteString(decoder.Push(nil, true))
			if got := out.String(); got != test.want {
				t.Fatalf("got %q (%x), want %q (%x)", got, []byte(got), test.want, []byte(test.want))
			}
		})
	}
}

func TestTerminalUTF8StreamDecoderStateIsPerPtyLifetime(t *testing.T) {
	oldPty := terminalUTF8StreamDecoder{}
	if got := oldPty.Push([]byte{0xf0, 0x9f}, false); got != "" {
		t.Fatalf("old PTY prematurely emitted %q", got)
	}

	// A recreated PTY gets a fresh decoder; pending bytes from the old PTY do
	// not contaminate its output. Finalising the old stream is deterministic.
	newPty := terminalUTF8StreamDecoder{}
	if got := newPty.Push([]byte("ok"), true); got != "ok" {
		t.Fatalf("new PTY output = %q, want ok", got)
	}
	if got := oldPty.Push(nil, true); got != "\ufffd" {
		t.Fatalf("old PTY final output = %q, want replacement", got)
	}
}

func TestReadPtyUTF8OutputConsumesBytesReturnedWithEOF(t *testing.T) {
	reader := &bytesAndErrorReader{
		data: []byte("паролями 😀"),
		err:  io.EOF,
	}
	var chunks []string
	readPtyUTF8Output(reader, func() bool { return true }, func(text string) {
		chunks = append(chunks, text)
	})
	if got := strings.Join(chunks, ""); got != "паролями 😀" {
		t.Fatalf("got %q, want complete final read", got)
	}
}

func TestReadPtyUTF8OutputConsumesBytesReturnedWithErrorAndFlushesTail(t *testing.T) {
	reader := &bytesAndErrorReader{
		data: []byte{'o', 'k', ' ', 0xe2, 0x82},
		err:  errors.New("device gone"),
	}
	var chunks []string
	readPtyUTF8Output(reader, func() bool { return true }, func(text string) {
		chunks = append(chunks, text)
	})
	if got := strings.Join(chunks, ""); got != "ok \ufffd" {
		t.Fatalf("got %q, want final bytes plus deterministic replacement", got)
	}
}

type bytesAndErrorReader struct {
	data []byte
	err  error
	done bool
}

func (r *bytesAndErrorReader) Read(target []byte) (int, error) {
	if r.done {
		return 0, io.EOF
	}
	r.done = true
	return copy(target, r.data), r.err
}

func itoa(value int) string {
	if value == 0 {
		return "0"
	}
	var digits [20]byte
	index := len(digits)
	for value != 0 {
		index--
		digits[index] = byte('0' + value%10)
		value /= 10
	}
	return string(digits[index:])
}
