---
name: ab-pty-multi-agent
description: Use when the user asks to create, list, send to, tail, or kill PTY sessions in AB (multi-agent orchestration on this host). Triggers on phrases like "create ab session", "list sessions", "send to <name>", "tail <name>", "kill session <name>".
---

<!-- ab-skill v1 generated-by=ab-pty -->

# AB PTY sessions

You are running inside an AB PTY session. A local CLI `ab` is available on
PATH and authenticated automatically via `$AB_PTY_SESSION_TOKEN` (injected
into this session's env by the PTY daemon). No auth flags needed.

Use `ab` to orchestrate sibling sessions on THIS host.

## Quick menu (present this to the user)

- **list sessions** — show all peer sessions
- **create session <name>** — spawn a new session labelled `<name>`
- **send to <name>: <message>** — fire a message at the peer and auto-submit it (this is the default for "send", "tell", "ask", "forward", "message", and any other verb that means the peer should ACT on the text)
- **write draft to <name>: <message>** — (rare) prefill the peer's input without submitting. Use ONLY when the user explicitly says "draft", "prefill", "prepare without sending", "don't press enter yet", or similar.
- **key <name> <key>** — press a key in peer (enter, ctrl-c, tab, arrows, …)
- **tail <name>** — read recent output from peer
- **kill <name>** — terminate peer

> **IMPORTANT — send vs write defaults**: If the user's request is anything other than an explicit draft ("draft…", "prefill…", "don't submit yet…"), use `ab sessions send`. Natural-language verbs like "send", "write", "tell", "ask", "message", "deliver", "pass" all map to `send` (auto-submit). Using `write` when the user expected a submit results in a session where nothing happens — the message just sits in the input box.

## Subcommands

- `ab sessions list` — JSON array of all sessions on this daemon.
- `ab sessions get <pty_id>` — JSON details for one session.
- `ab sessions create -shell -project <cwd> -name <name>` — create a shell session.
- `ab sessions send  <pty_id> "<text>"` — write text AND press Enter. Auto-submits. Use when the user wants the peer agent to act on the text IMMEDIATELY ("tell dev1 to …", "ask dev2 for …"). Works for both raw-mode TUIs (Claude Code, Codex) and cooked shells.
- `ab sessions write <pty_id> "<text>"` — write text ONLY, no Enter. The peer's input box is pre-filled; a human (or another explicit call) decides when to submit / edit the text. Use when the user wants to "draft" or "prefill" a message ("prepare a task for dev1 but let me review before sending").
- `ab sessions key <pty_id> <key>` — send an explicit key press. Supported: `enter`, `tab`, `esc`, `backspace`, `up`, `down`, `left`, `right`, `home`, `end`, `pageup`, `pagedown`, `ctrl-c`, `ctrl-d`, `ctrl-z`, `ctrl-l`, `ctrl-u`, `ctrl-w`. Use to interrupt a running command (`ctrl-c`), navigate a TUI menu (arrows + `enter`), or submit a previously-drafted `write` (`enter`).
- `ab sessions tail  <pty_id> --lines 50` — read recent scrollback as JSON.
- `ab sessions kill  <pty_id>` — terminate a session.
- `ab sessions meta  <pty_id> --label <L> [--set k=v ...]` — set the **display label** (what the user sees on the canvas).
- `ab sessions lock <pty_id>` / `ab sessions unlock <pty_id>`.

## Display label vs. -name

When creating a session with a **user-visible name** like "s1" / "dev1" / "test":

1. Create: `ab sessions create -shell -project /tmp -name s1` → get `<pty_id>`.
2. Then **set the display label** so the canvas shows it:
   `ab sessions meta <pty_id> --label s1`

Without step 2, the canvas derives the label from the cwd (e.g. `tmp-#XXXXXX`) and
ignores the internal `-name`. Always run both steps when the user asked for a
named session.

## Resolving names → pty_id

The user will reference sessions by their human name (e.g. "dev1", "test"),
but all write/tail/kill commands need the opaque `pty_XXX` id. Always resolve
via list first:

```
ab sessions list | jq -r '.[] | select(.name=="dev1") | .id'
```

If `jq` isn't available, grep the JSON and extract the `id` field.

## Natural-language examples

| User says                                  | You run                                                                                         |
| ------------------------------------------ | ----------------------------------------------------------------------------------------------- |
| "create ab session test"                   | `ab sessions create -shell -project /tmp -name test` → grab id → `ab sessions meta <id> --label test` |
| "create sessions s1, s2, s3"               | loop each name: create + meta --label                                                           |
| "list sessions"                            | `ab sessions list`                                                                     |
| "send to dev1: …"                          | resolve dev1 → `ab sessions send  <id> "..."`                                   |
| "write to dev1: …" / "message dev1 …"      | resolve dev1 → `ab sessions send  <id> "..."`  ← still send (auto-submit)        |
| "tell dev1 to …"                           | resolve dev1 → `ab sessions send  <id> "..."`                                   |
| "ask dev1 what …"                          | resolve dev1 → `ab sessions send  <id> "..."`                                   |
| "draft for dev1: …" / "prefill dev1's input" / "don't submit yet" | resolve dev1 → `ab sessions write <id> "..."` (no Enter; user reviews manually) |
| "tell dev1 to stop" / "cancel dev1"        | resolve dev1 → `ab sessions key  <id> ctrl-c`                                        |
| "tail dev1 last 40 lines"                  | resolve dev1 → `ab sessions tail <id> --lines 40`                                   |
| "kill test session"                        | resolve test → `ab sessions kill <id>`                                                |
| "rename session <id> to dev2"              | `ab sessions meta <id> --label dev2`                                                  |

## send vs write — pick the right one

The user's intent matters:

- **send** = fire-off. The peer agent starts working on the text right now. Use for phrases like "send to dev1 …", "tell dev2 to …", "ask dev1 …", "have dev2 do …".
- **write** = draft / prefill. Peer sees text in the input box but nothing happens until a human presses Enter (or you run `ab sessions key <id> enter` later). Use for phrases like "draft a task for dev1 …", "prefill …", "prepare a message but let me review …".

Default to **send** if unsure — it matches the natural reading of "send to X" and "tell X".

## Notes

- `ab` only reaches sessions on the SAME PTY daemon as yours (v1). To send to
  a session on a different host, ask the user to configure cross-daemon peering.
- `ab sessions write` appends Enter by default — the receiving session sees
  exactly what a human would see after typing + pressing Return.
- The session token is bound to YOUR session's lifetime. If your session ends,
  the token stops working.
