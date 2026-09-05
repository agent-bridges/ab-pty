package main

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

func TestCodexWrapperDerivesAndAcceptsSessionLabel(t *testing.T) {
	repoDir, err := os.Getwd()
	if err != nil {
		t.Fatal(err)
	}
	projectDir := filepath.Join(t.TempDir(), "payments-api")
	binDir := filepath.Join(t.TempDir(), "bin")
	if err := os.MkdirAll(projectDir, 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.MkdirAll(binDir, 0o755); err != nil {
		t.Fatal(err)
	}
	abCapture := filepath.Join(t.TempDir(), "ab.args")
	codexCapture := filepath.Join(t.TempDir(), "codex.args")
	writeExecutable := func(name, body string) {
		t.Helper()
		if err := os.WriteFile(filepath.Join(binDir, name), []byte("#!/bin/sh\n"+body+"\n"), 0o755); err != nil {
			t.Fatal(err)
		}
	}
	writeExecutable("ab", `printf '%s\n' "$@" > "$AB_CAPTURE"`)
	writeExecutable("codex", `printf '%s\n' "$@" > "$CODEX_CAPTURE"`)

	run := func(extraArgs ...string) []string {
		t.Helper()
		_ = os.Remove(abCapture)
		args := append([]string{filepath.Join(repoDir, "codexs")}, extraArgs...)
		cmd := exec.Command("bash", args...)
		cmd.Dir = projectDir
		cmd.Env = append(os.Environ(),
			"PATH="+binDir+":/usr/bin:/bin",
			"AB_PTY_SESSION_ID=pty-test",
			"AB_CAPTURE="+abCapture,
			"CODEX_CAPTURE="+codexCapture,
		)
		if out, err := cmd.CombinedOutput(); err != nil {
			t.Fatalf("codexs failed: %v: %s", err, out)
		}
		data, err := os.ReadFile(abCapture)
		if err != nil {
			t.Fatal(err)
		}
		return strings.Fields(string(data))
	}

	if got := run("resume", "--last"); strings.Join(got, " ") != "sessions label pty-test payments-api" {
		t.Fatalf("derived label args = %q", got)
	}
	if got := run("--remote", "unix:///tmp/codex.sock", "--ab-label", "mobile-name"); strings.Join(got, " ") != "sessions label pty-test mobile-name" {
		t.Fatalf("explicit label args = %q", got)
	}
	codexArgs, err := os.ReadFile(codexCapture)
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(string(codexArgs), "--ab-label") {
		t.Fatalf("wrapper-only argument leaked to Codex: %s", codexArgs)
	}
}
