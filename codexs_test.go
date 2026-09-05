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

	run := func(extraArgs ...string) ([]string, []string) {
		t.Helper()
		_ = os.Remove(abCapture)
		_ = os.Remove(codexCapture)
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
		abData, err := os.ReadFile(abCapture)
		if err != nil {
			t.Fatal(err)
		}
		codexData, err := os.ReadFile(codexCapture)
		if err != nil {
			t.Fatal(err)
		}
		return strings.Fields(string(abData)), strings.Split(strings.TrimSpace(string(codexData)), "\n")
	}

	abArgs, codexArgs := run()
	if strings.Join(abArgs, " ") != "sessions label pty-test payments-api" {
		t.Fatalf("derived label args = %q", abArgs)
	}
	wantDefault := []string{
		"--dangerously-bypass-approvals-and-sandbox",
		"-C", projectDir,
		"resume", "--last",
	}
	if strings.Join(codexArgs, "\x00") != strings.Join(wantDefault, "\x00") {
		t.Fatalf("default Codex args = %q, want %q", codexArgs, wantDefault)
	}

	abArgs, codexArgs = run("--remote", "unix:///tmp/codex.sock", "--ab-label", "mobile-name")
	if strings.Join(abArgs, " ") != "sessions label pty-test mobile-name" {
		t.Fatalf("explicit label args = %q", abArgs)
	}
	if strings.Contains(strings.Join(codexArgs, " "), "--ab-label") {
		t.Fatalf("wrapper-only argument leaked to Codex: %q", codexArgs)
	}
	if len(codexArgs) == 0 || codexArgs[0] != "--dangerously-bypass-approvals-and-sandbox" {
		t.Fatalf("full-access flag missing from Codex args: %q", codexArgs)
	}

	cmd := exec.Command("bash", filepath.Join(repoDir, "codexs"), "--sandbox", "read-only")
	cmd.Dir = projectDir
	cmd.Env = append(os.Environ(), "PATH="+binDir+":/usr/bin:/bin")
	out, err := cmd.CombinedOutput()
	if err == nil || !strings.Contains(string(out), "permission flags are fixed to full access") {
		t.Fatalf("reduced permissions were not rejected: err=%v output=%q", err, out)
	}
}
