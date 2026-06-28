---
name: ab
description: Use when the user asks to (a) create/list/send/tail/kill PTY sessions in AB via the local `ab` CLI, OR (b) set up/spawn/brief a multi-agent team for a project (front + back + qa, plus optional design/ops). Triggers on phrases like "create ab session", "list sessions", "send to <name>", "tail <name>", "kill session <name>", "set up a team", "spawn the team", "create front/back/qa sessions", "заведи команду", "оркестратор", "teamlead", "team up", or any request to orchestrate sibling PTY workers on this host.
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

---

# Team Protocol — orchestrator-facing recipe

Canonical multi-agent orchestration spec for this host. The orchestrator (teamlead) reads this and executes the recipe end-to-end. Workers are heterogeneous CLI agents (Claude Code, OpenAI Codex CLI, Gemini CLI, or any other PTY-driven agent) — the **wire protocol is shared**, only the launch incantation per agent type differs.

---

## When to use

The user asks to set up a multi-agent team for a project (front + back + qa, plus optional design/ops). Phrases: "заведи команду", "set up a team", "create front/back/qa sessions", "spawn the team".

## Recipe (orchestrator runs autonomously)

Given the project root (`$PROJECT_ROOT` = `$CWD` at the moment the user invokes the team), a short prefix the user picks (or you derive from cwd, e.g. `vt` for `/lxd-exch/vestlite`), and the **agent flavour** the user wants per worker (default: `claudes` for everyone unless the user specifies otherwise):

1. **Read this file in full** — recipe + wire protocol + per-client launch matrix. Don't re-derive the rules.

2. **Make per-role session directories** under `$PROJECT_ROOT/_team/<prefix>-<role>/` and append `_team/` to `.gitignore` if it isn't already there. Many CLI agents bind their conversation history / settings to the cwd, so each worker MUST get its own dedicated dir; they all share the same project root one level up:
   ```
   mkdir -p $PROJECT_ROOT/_team/<prefix>-front $PROJECT_ROOT/_team/<prefix>-back $PROJECT_ROOT/_team/<prefix>-qa
   grep -qxF '_team/' $PROJECT_ROOT/.gitignore 2>/dev/null || echo '_team/' >> $PROJECT_ROOT/.gitignore
   ```

3. **Spawn N sessions** in parallel via `Bash`. Each session's `-project` is its own role-dir, NOT the project root:
   ```
   ab sessions create -shell -project $PROJECT_ROOT/_team/<prefix>-front -name front
   ab sessions create -shell -project $PROJECT_ROOT/_team/<prefix>-back  -name back
   ab sessions create -shell -project $PROJECT_ROOT/_team/<prefix>-qa    -name qa
   ```
   Capture each `pty_id`.

4. **Set namespaced labels** so multiple projects can coexist on one host:
   ```
   ab sessions meta <front_pty>  --label <prefix>-front
   ab sessions meta <back_pty>   --label <prefix>-back
   ab sessions meta <qa_pty>     --label <prefix>-qa
   ```

5. **Launch the worker agent** in each session per the **launch matrix** below. **Never launch a vanilla "low-permissions" CLI** — workers run in dangerous/full-access mode because the orchestrator is the trust boundary, not them. If the user specifies a flavour for a role (e.g. "front=codex, qa=gemini"), use the matching row.

6. **Wait ~6 s** for the welcome banner, verify with `ab sessions tail <pty> --lines 5`.

7. **Drop `TEAM_PROTOCOL.md`** at the project root (`$PROJECT_ROOT/TEAM_PROTOCOL.md`) by copying the "Worker protocol" section below with placeholders filled. Use the `Write` tool, not bash heredoc.

8. **Brief each worker** (one-shot `ab sessions send`). EVERY brief MUST include both the role-dir (their cwd) AND the project root, so they don't confuse the two:
   - "You are <ROLE> in the `<prefix>` team. Your session cwd is `<PROJECT_ROOT>/_team/<prefix>-<role>/` (your scratch / conversation home). The actual project root is `<PROJECT_ROOT>` — that's where source lives, where you read/write code. Read `<PROJECT_ROOT>/TEAM_PROTOCOL.md` (full), send a STARTED status, then sit silent until a task arrives. Teamlead pty_id is `<TEAMLEAD_PTY_ID>`. No heartbeats."

9. **Do not schedule wakeups** unless an actual task is in flight. Idle workers stay silent; teamlead stays silent until the user dispatches real work.

---

## Per-client launch matrix

When sending the launch line via `ab sessions send <pty> "<command>"`, use the matching row. **Always launch in full-access / no-confirmation mode** — the orchestrator approved the work, the worker shouldn't second-guess.

| Agent | Local wrapper on this host | Underlying command | Notes |
|---|---|---|---|
| **Claude Code** | `claudes` (preferred) | `CLAUDE_CODE_DISABLE_ALTERNATE_SCREEN=1 IS_SANDBOX=1 claude --dangerously-skip-permissions` | Always use the wrapper, not raw `claude`. ⚠️ The wrapper MUST set `CLAUDE_CODE_DISABLE_ALTERNATE_SCREEN=1` — without it Claude Code renders into the terminal alternate-screen buffer and **scroll + copy/paste break in the AB web terminal**. Canonical wrapper: `ab/scripts/claudes`. |
| **OpenAI Codex CLI** | `codexs` (if present) or raw | `codex --full-auto` (alias `codex --yolo` in newer builds; use `codex exec --dangerously-bypass-approvals-and-sandbox` for non-TUI) | If `codexs` wrapper exists, prefer it (it'll set `CODEX_SANDBOX=danger-full-access` or equivalent). Verify with `which codexs`. |
| **Gemini CLI** | `geminis` (if present) or raw | `gemini --yolo` (auto-approves all prompts; alternatively `--approval-mode yolo`) | If `geminis` wrapper exists, prefer it. Verify with `which geminis`. |
| **Other / unknown** | — | Ask user for the launch line | Don't guess; ask "какой бинарь и флаг полного доступа?" |

**Verification before launching:** `which <wrapper>` first. If a wrapper exists at `/lxd-exch/system/<name>` or on PATH, use it. If not, fall back to the raw command with the dangerous flag and surface this fact to the user. **Never silently downgrade to confirmation mode** — that hangs the worker on every prompt.

To check what a wrapper actually does: `cat $(which <wrapper>)` — they're typically thin one-liners like `claudes` (`IS_SANDBOX=1 claude --dangerously-skip-permissions "$@"`).

---

## Pause vs kill (orchestrator behaviour, agent-agnostic)

User says "stop / pause / приостановить" → `ab sessions key <pty> esc` (interrupts the current LLM turn; conversation context survives).
User says "kill / убить / ёбнуть" → `ab sessions kill <pty>` (destroys session and conversation history; only on explicit instruction).
**Never kill to "pause".** A kill forces a re-brief that loses per-session conversation context, and on Codex / Gemini may lose chat history depending on how their CLI persists state.

## Tail hygiene

`ab sessions tail` returns ANSI-coded JSON. Strip control bytes before reading (works for any agent's TUI):
```
ab sessions tail <pty> --lines N | python3 -c "
import json,sys,re
d=json.load(sys.stdin); s=''.join(d['lines'])
s=re.sub(r'\x1b\[[0-9;?]*[a-zA-Z]','',s); s=re.sub(r'\x1b\][^\x07]*\x07','',s); s=re.sub(r'[\x00-\x08\x0e-\x1f]','',s)
print(s[-1500:])"
```

---

## Worker protocol (drop this section as `TEAM_PROTOCOL.md` at project root)

> Replace placeholders before saving.

# Team Communication Protocol

This protocol is **agent-agnostic** — every worker (Claude Code, Codex CLI, Gemini CLI, or other) follows the same wire format. The only thing that differs per agent type is the launch incantation, which the orchestrator handles outside the protocol.

## Roster

| Role | Label | pty_id | Agent flavour |
|---|---|---|---|
| **Teamlead** (orchestrator) | `teamlead` | `<TEAMLEAD_PTY_ID>` | <TEAMLEAD_FLAVOUR> |
| **Frontend** | `<PREFIX>-front` | `<FRONT_PTY_ID>` | <FRONT_FLAVOUR> |
| **Backend** | `<PREFIX>-back` | `<BACK_PTY_ID>` | <BACK_FLAVOUR> |
| **QA** | `<PREFIX>-qa` | `<QA_PTY_ID>` | <QA_FLAVOUR> |

Resolve labels → ids via `ab sessions list`.

## Status format (universal — all agents follow this)

Send a single line via:
```
ab sessions send <TEAMLEAD_PTY_ID> "[ROLE] STATUS: <one-line summary> | files: <paths> | next: ask|done"
```

- `ROLE` — `FRONT` / `BACK` / `QA` (your role, all-caps).
- `STATUS` — one of: `STARTED` / `DONE` / `QUESTION` / `BLOCKED`. **No HEARTBEAT.**
- `files:` — comma-separated paths created or modified (may be empty).
- `next:` — `ask` (need teamlead input) or `done` (task fully closed).

Examples:
```
[FRONT] STARTED: scaffolding project | files: package.json, src/main.tsx | next: ask
[BACK] DONE: 12 vitest passing | files: workers/contact.ts, contact.spec.ts | next: done
[QA] BLOCKED: chrome missing on host | files: | next: ask
[FRONT] QUESTION: motion.css or styles.css for fallback? | next: ask
```

## Cadence — event-driven, NO heartbeats

- Send a status line ONLY on events: STARTED / DONE / QUESTION / BLOCKED.
- When idle with no active task — stay silent. Do not ping.
- Teamlead handles timeouts: when dispatching a task, teamlead schedules its own check (~270 s); if no DONE/QUESTION arrives in time, teamlead tails your session.

## Receiving tasks

Tasks arrive as plain text starting with `[TASK <id>]`. Acknowledge with STARTED, do the work, send DONE (or QUESTION / BLOCKED).

## Cross-role coordination

Don't message peers directly. Send a `QUESTION` to teamlead and let teamlead route it. Same rule regardless of which CLI agent each peer is running.

## Working agreements

- **Project root**: `<PROJECT_PATH>` — that's where source code lives. Read/write code there. NOT in your session cwd.
- **Your session cwd**: `<PROJECT_PATH>/_team/<PREFIX>-<ROLE>/` — this is your scratch / conversation home. Many CLI agents bind history and config to the cwd; this dir keeps your state isolated from the project tree and out of git (`_team/` is gitignored). Use it freely for notes, intermediate files, scratchpads.
- When you need to operate on project files: use absolute paths from `<PROJECT_PATH>` or `cd <PROJECT_PATH>` for shell ops. Don't dump artefacts into your session cwd unless they're truly per-role and not part of the deliverable.
- Each worker runs in **full-access / no-confirmation mode** — the orchestrator is the trust boundary. Don't fight your CLI's prompts; the launch flag should already have suppressed them.
- Labels namespaced per project (`<PREFIX>-front` etc.).
- Refer to `<PROJECT_PATH>/_src_data/` (or equivalent project-specified path) for canonical reference assets, never the editable copy in `src/`.
