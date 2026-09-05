package main

import (
	"crypto/rand"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"net/http"
	"strconv"
	"strings"
	"sync"
	"time"
	"unicode/utf8"
)

const (
	maxPushTokenBytes  = 4096
	maxPushJobsPerRead = 5
	// FCM data messages are limited to 4 KiB. Keep enough room for routing,
	// names and fingerprints while still carrying a useful final answer.
	maxPushMessageBytes = 2048
)

var (
	pushMessagesMu sync.RWMutex
	pushMessages   = map[string]string{}
	codexPushTurns = map[string]codexPushTurn{}
)

type codexPushTurn struct{ threadID, turnID string }

type pushJob struct {
	ID                int64  `json:"id"`
	EventKey          string `json:"event_key"`
	LeaseToken        string `json:"lease_token"`
	Attempt           int    `json:"attempt"`
	RelayFingerprint  string `json:"relay_fingerprint"`
	Token             string `json:"token"`
	DaemonFingerprint string `json:"daemon_fingerprint"`
	DaemonName        string `json:"daemon_name"`
	SessionID         string `json:"session_id"`
	SessionName       string `json:"session_name"`
	SessionLabel      string `json:"session_label"`
	LastMessage       string `json:"last_message"`
	CreatedAt         string `json:"created_at"`
}

func initPushTables() error {
	if _, err := db.Exec(`
		CREATE TABLE IF NOT EXISTS push_subscriptions (
			client_fingerprint TEXT PRIMARY KEY,
			client_name        TEXT NOT NULL DEFAULT '',
			token              TEXT NOT NULL,
			updated_at         DATETIME DEFAULT CURRENT_TIMESTAMP
		)
	`); err != nil {
		return fmt.Errorf("create push subscriptions: %w", err)
	}
	if _, err := db.Exec(`
		CREATE TABLE IF NOT EXISTS push_jobs (
			id                 INTEGER PRIMARY KEY AUTOINCREMENT,
			event_key          TEXT NOT NULL,
			client_fingerprint TEXT NOT NULL,
			token              TEXT NOT NULL,
			daemon_fingerprint TEXT NOT NULL,
			daemon_name        TEXT NOT NULL,
			 session_id         TEXT NOT NULL,
			 session_name       TEXT NOT NULL,
			 session_label      TEXT NOT NULL,
			 last_message       TEXT NOT NULL DEFAULT '',
			 created_at         DATETIME DEFAULT CURRENT_TIMESTAMP,
			 UNIQUE(event_key, client_fingerprint)
		)
	`); err != nil {
		return fmt.Errorf("create push jobs: %w", err)
	}
	if err := ensurePushJobsLastMessageColumn(); err != nil {
		return err
	}
	for _, column := range []struct{ table, name, definition string }{
		{"push_subscriptions", "relay_fingerprint", "TEXT NOT NULL DEFAULT ''"},
		{"push_jobs", "relay_fingerprint", "TEXT NOT NULL DEFAULT ''"},
		{"push_jobs", "lease_token", "TEXT NOT NULL DEFAULT ''"},
		{"push_jobs", "available_at", "INTEGER NOT NULL DEFAULT 0"},
		{"push_jobs", "attempt", "INTEGER NOT NULL DEFAULT 0"},
	} {
		if err := ensurePushColumn(column.table, column.name, column.definition); err != nil {
			return err
		}
	}
	// Revocation and unsubscribe must also cancel queued plaintext replies.
	// SQLite triggers cover the CLI as well as HTTP administration, atomically.
	if _, err := db.Exec(`
		CREATE TRIGGER IF NOT EXISTS push_revoke_client AFTER DELETE ON tls_clients BEGIN
			DELETE FROM push_subscriptions WHERE client_fingerprint = OLD.fingerprint;
			DELETE FROM push_jobs WHERE client_fingerprint = OLD.fingerprint;
		END;
		CREATE TRIGGER IF NOT EXISTS push_unsubscribe AFTER DELETE ON push_subscriptions BEGIN
			DELETE FROM push_jobs WHERE client_fingerprint = OLD.client_fingerprint;
		END;
	`); err != nil {
		return err
	}
	_, err := db.Exec(`CREATE INDEX IF NOT EXISTS push_jobs_created_idx ON push_jobs(created_at, id)`)
	return err
}

func ensurePushJobsLastMessageColumn() error {
	return ensurePushColumn("push_jobs", "last_message", "TEXT NOT NULL DEFAULT ''")
}

func ensurePushColumn(table, column, definition string) error {
	rows, err := db.Query(`PRAGMA table_info(` + table + `)`)
	if err != nil {
		return fmt.Errorf("inspect push_jobs schema: %w", err)
	}
	defer rows.Close()
	hasColumn := false
	for rows.Next() {
		var cid int
		var name, columnType string
		var notNull int
		var defaultValue interface{}
		var primaryKey int
		if err := rows.Scan(&cid, &name, &columnType, &notNull, &defaultValue, &primaryKey); err != nil {
			return fmt.Errorf("read push_jobs schema: %w", err)
		}
		if name == column {
			hasColumn = true
		}
	}
	if err := rows.Err(); err != nil {
		return fmt.Errorf("read push_jobs schema: %w", err)
	}
	if hasColumn {
		return nil
	}
	if _, err := db.Exec(`ALTER TABLE ` + table + ` ADD COLUMN ` + column + ` ` + definition); err != nil {
		return fmt.Errorf("add %s.%s: %w", table, column, err)
	}
	return nil
}

// handlePushSubscription is intentionally certificate-bound. A token never
// grants daemon access; it only tells this already-authorised device where to
// receive completion notices. In-session sess.* credentials cannot register.
func handlePushSubscription(w http.ResponseWriter, r *http.Request) {
	setJSONHeaders(w)
	principal, ok := principalFromRequest(r)
	if !ok || principal.Client.Fingerprint == "" {
		writeError(w, http.StatusForbidden, "push subscriptions require an external device certificate")
		return
	}
	switch r.Method {
	case http.MethodPut:
		var body struct {
			Token            string `json:"token"`
			RelayFingerprint string `json:"relay_fingerprint"`
		}
		decoder := json.NewDecoder(http.MaxBytesReader(w, r.Body, maxPushTokenBytes+1024))
		decoder.DisallowUnknownFields()
		if err := decoder.Decode(&body); err != nil {
			writeError(w, http.StatusBadRequest, "invalid push subscription")
			return
		}
		body.Token = strings.TrimSpace(body.Token)
		if body.Token == "" || len(body.Token) > maxPushTokenBytes {
			writeError(w, http.StatusBadRequest, "invalid FCM token")
			return
		}
		relayFingerprint, err := normalizeFingerprint(body.RelayFingerprint)
		if err != nil {
			writeError(w, http.StatusBadRequest, "push subscription requires an explicit relay fingerprint")
			return
		}
		tx, err := db.Begin()
		if err != nil {
			writeError(w, http.StatusInternalServerError, "failed to store push subscription")
			return
		}
		defer tx.Rollback()
		_, err = tx.Exec(`
			INSERT INTO push_subscriptions(client_fingerprint, client_name, token, relay_fingerprint, updated_at)
			VALUES (?, ?, ?, ?, CURRENT_TIMESTAMP)
			ON CONFLICT(client_fingerprint) DO UPDATE SET
				client_name = excluded.client_name,
				token = excluded.token,
				relay_fingerprint = excluded.relay_fingerprint,
				updated_at = CURRENT_TIMESTAMP
		`, principal.Client.Fingerprint, principal.Client.Name, body.Token, relayFingerprint)
		if err != nil {
			writeError(w, http.StatusInternalServerError, "failed to store push subscription")
			return
		}
		// Pending work follows this device's current token and explicit route.
		if _, err = tx.Exec(`UPDATE push_jobs SET token = ?, relay_fingerprint = ? WHERE client_fingerprint = ?`, body.Token, relayFingerprint, principal.Client.Fingerprint); err != nil {
			writeError(w, http.StatusInternalServerError, "failed to update push subscription")
			return
		}
		if err = tx.Commit(); err != nil {
			writeError(w, http.StatusInternalServerError, "failed to store push subscription")
			return
		}
		writeJSON(w, 0, map[string]bool{"ok": true})
	case http.MethodDelete:
		if _, err := db.Exec(`DELETE FROM push_subscriptions WHERE client_fingerprint = ?`, principal.Client.Fingerprint); err != nil {
			writeError(w, http.StatusInternalServerError, "failed to remove push subscription")
			return
		}
		writeJSON(w, 0, map[string]bool{"ok": true})
	default:
		writeError(w, http.StatusMethodNotAllowed, "Method not allowed")
	}
}

// handlePushJobs is consumed by the always-on ab-core notifier over the same
// pinned mTLS route used for every other daemon operation. Jobs are durable;
// POST claims a bounded batch for two minutes. DELETE acknowledges a claimed
// job; PATCH releases it with a retry delay. All mutations require its lease.
// Old unleased GET consumers fail explicitly instead of racing new consumers.
func handlePushJobs(w http.ResponseWriter, r *http.Request) {
	setJSONHeaders(w)
	w.Header().Set("Cache-Control", "no-store")
	principal, ok := principalFromRequest(r)
	if !ok || principal.Client.Fingerprint == "" {
		writeError(w, http.StatusForbidden, "push jobs require an external client certificate")
		return
	}
	if r.URL.Path != "/api/push/jobs" {
		if r.Method != http.MethodDelete && r.Method != http.MethodPatch {
			writeError(w, http.StatusMethodNotAllowed, "Method not allowed")
			return
		}
		idText := strings.TrimPrefix(r.URL.Path, "/api/push/jobs/")
		id, err := strconv.ParseInt(idText, 10, 64)
		if err != nil || id < 1 {
			writeError(w, http.StatusBadRequest, "invalid push job id")
			return
		}
		lease := r.URL.Query().Get("lease_token")
		if len(lease) != 32 {
			writeError(w, http.StatusBadRequest, "push job requires its lease token")
			return
		}
		query := `DELETE FROM push_jobs WHERE id = ? AND lease_token = ? AND available_at > unixepoch()`
		args := []interface{}{id, lease}
		if r.Method == http.MethodDelete && r.URL.Query().Get("invalid_token") == "1" {
			query = `DELETE FROM push_subscriptions WHERE (client_fingerprint, token) IN
				(SELECT client_fingerprint, token FROM push_jobs WHERE id = ? AND lease_token = ? AND available_at > unixepoch())`
		}
		if r.Method == http.MethodPatch {
			delay, err := strconv.Atoi(r.URL.Query().Get("retry_seconds"))
			if err != nil || delay < 60 || delay > 86400 {
				writeError(w, http.StatusBadRequest, "retry_seconds must be 60..86400")
				return
			}
			query = `UPDATE push_jobs SET lease_token = '', available_at = unixepoch() + ? WHERE id = ? AND lease_token = ? AND available_at > unixepoch()`
			args = []interface{}{delay, id, lease}
		}
		res, err := db.Exec(query, args...)
		if err != nil {
			writeError(w, http.StatusInternalServerError, "failed to acknowledge push job")
			return
		}
		if n, _ := res.RowsAffected(); n != 1 {
			writeError(w, http.StatusConflict, "push job lease expired or job was cancelled")
			return
		}
		writeJSON(w, 0, map[string]bool{"ok": true})
		return
	}
	if r.Method == http.MethodGet {
		writeError(w, http.StatusConflict, "push queue protocol changed: upgrade ab-core to leased POST claims")
		return
	}
	if r.Method != http.MethodPost {
		writeError(w, http.StatusMethodNotAllowed, "Method not allowed")
		return
	}
	// Recheck the recipient at delivery time as well as enqueue time. This
	// cleans up subscriptions created before revocation triggers were installed.
	if _, err := db.Exec(`DELETE FROM push_jobs WHERE created_at < datetime('now', '-7 days')
		OR NOT EXISTS (SELECT 1 FROM tls_clients c JOIN push_subscriptions s ON s.client_fingerprint = c.fingerprint
			WHERE c.fingerprint = push_jobs.client_fingerprint AND s.token = push_jobs.token)`); err != nil {
		writeError(w, http.StatusInternalServerError, "failed to expire push jobs")
		return
	}
	leaseBytes := make([]byte, 16)
	if _, err := rand.Read(leaseBytes); err != nil {
		writeError(w, http.StatusInternalServerError, "failed to create push lease")
		return
	}
	// The single SQLite statement is atomic across connections and processes.
	rows, err := db.Query(`UPDATE push_jobs SET lease_token = ?, available_at = unixepoch() + 120, attempt = attempt + 1
		WHERE id IN (SELECT id FROM push_jobs WHERE available_at <= unixepoch() AND relay_fingerprint <> ''
			ORDER BY available_at, id LIMIT ?)
		RETURNING id, event_key, lease_token, attempt, relay_fingerprint, token, daemon_fingerprint,
			daemon_name, session_id, session_name, session_label, last_message, created_at
	`, hex.EncodeToString(leaseBytes), maxPushJobsPerRead)
	if err != nil {
		writeError(w, http.StatusInternalServerError, "failed to read push jobs")
		return
	}
	defer rows.Close()
	jobs := make([]pushJob, 0)
	for rows.Next() {
		var job pushJob
		if err := rows.Scan(&job.ID, &job.EventKey, &job.LeaseToken, &job.Attempt, &job.RelayFingerprint, &job.Token, &job.DaemonFingerprint, &job.DaemonName, &job.SessionID, &job.SessionName, &job.SessionLabel, &job.LastMessage, &job.CreatedAt); err != nil {
			writeError(w, http.StatusInternalServerError, "failed to read push job")
			return
		}
		jobs = append(jobs, job)
	}
	if err := rows.Err(); err != nil {
		writeError(w, http.StatusInternalServerError, "failed to claim push jobs")
		return
	}
	writeJSON(w, 0, jobs)
}

func rememberPushCompletionMessage(ptyID, message string) {
	message = boundedPushMessage(message)
	pushMessagesMu.Lock()
	pushMessages[ptyID] = message
	pushMessagesMu.Unlock()
}

func boundedPushMessage(message string) string {
	message = strings.Join(strings.Fields(message), " ")
	if len(message) > maxPushMessageBytes {
		message = message[:maxPushMessageBytes-len("…")]
		for !utf8.ValidString(message) {
			message = message[:len(message)-1]
		}
		if space := strings.LastIndexByte(message, ' '); space >= 0 {
			message = message[:space]
		}
		message += "…"
	}
	return message
}

func pushCompletionMessage(ptyID string) string {
	pushMessagesMu.RLock()
	defer pushMessagesMu.RUnlock()
	return pushMessages[ptyID]
}

func clearPushCompletionMessage(ptyID string) {
	pushMessagesMu.Lock()
	delete(pushMessages, ptyID)
	delete(codexPushTurns, ptyID)
	pushMessagesMu.Unlock()
}

// Only explicit top-level thread metadata establishes the notification owner.
// Never infer it from whichever parent/child event happens to arrive first.
func selectCodexPushThread(ptyID string, raw json.RawMessage) {
	var thread struct {
		ID             string          `json:"id"`
		ParentThreadID string          `json:"parentThreadId"`
		Source         json.RawMessage `json:"source"`
	}
	if json.Unmarshal(raw, &thread) != nil || thread.ID == "" || thread.ParentThreadID != "" {
		return
	}
	var source string
	if json.Unmarshal(thread.Source, &source) != nil {
		return
	} // subAgent is an object
	if source != "cli" && source != "appServer" && source != "vscode" && source != "exec" {
		return
	}
	selectCodexPushThreadID(ptyID, thread.ID)
}

func selectCodexPushThreadID(ptyID, threadID string) {
	pushMessagesMu.Lock()
	defer pushMessagesMu.Unlock()
	if codexPushTurns[ptyID].threadID != threadID {
		codexPushTurns[ptyID] = codexPushTurn{threadID: threadID}
		delete(pushMessages, ptyID)
	}
}

func beginCodexPushTurn(ptyID, threadID, turnID string) {
	pushMessagesMu.Lock()
	defer pushMessagesMu.Unlock()
	current := codexPushTurns[ptyID]
	if current.threadID != threadID || threadID == "" || turnID == "" {
		return
	}
	if current.turnID != turnID {
		codexPushTurns[ptyID] = codexPushTurn{threadID: threadID, turnID: turnID}
		delete(pushMessages, ptyID)
	}
}

func recordCodexPushMessage(ptyID, threadID, turnID, message string) {
	pushMessagesMu.Lock()
	defer pushMessagesMu.Unlock()
	current := codexPushTurns[ptyID]
	if threadID != "" && turnID != "" && current.threadID == threadID && current.turnID == turnID {
		pushMessages[ptyID] = boundedPushMessage(message)
	}
}

func completeCodexPushTurn(ptyID, threadID, turnID, status string) {
	pushMessagesMu.Lock()
	current := codexPushTurns[ptyID]
	if threadID == "" || turnID == "" || current.threadID != threadID || current.turnID != turnID {
		pushMessagesMu.Unlock()
		return
	}
	message := pushMessages[ptyID]
	codexPushTurns[ptyID] = codexPushTurn{threadID: threadID}
	delete(pushMessages, ptyID)
	pushMessagesMu.Unlock()
	if status != "completed" {
		return
	}
	if err := queuePushCompletionEvent(ptyID, "codex:"+threadID+":"+turnID, message); err != nil {
		logPushFailure(ptyID, err)
	}
}

func queuePushCompletion(ptyID string, transitionAt time.Time) error {
	return queuePushCompletionEvent(ptyID, ptyID+":"+strconv.FormatInt(transitionAt.UnixNano(), 10), pushCompletionMessage(ptyID))
}

func queuePushCompletionEvent(ptyID, eventKey, lastMessage string) error {
	meta := getSessionMeta(ptyID)
	if meta == nil {
		return nil
	}
	fingerprint, err := daemonFingerprint()
	if err != nil {
		return fmt.Errorf("read daemon fingerprint: %w", err)
	}
	_, err = db.Exec(`
		INSERT OR IGNORE INTO push_jobs(
			event_key, client_fingerprint, token, relay_fingerprint, daemon_fingerprint, daemon_name,
			session_id, session_name, session_label, last_message, created_at
		)
		SELECT ?, s.client_fingerprint, s.token, s.relay_fingerprint, ?, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP
		FROM push_subscriptions s JOIN tls_clients c ON c.fingerprint = s.client_fingerprint
		WHERE s.relay_fingerprint <> ''
	`, eventKey, fingerprint, daemonName(), ptyID, meta.Name, meta.Label, lastMessage)
	if err != nil {
		return err
	}
	// A phone that stayed offline for weeks does not need a flood of obsolete
	// completions when it returns. This also bounds disk use if FCM is disabled.
	_, _ = db.Exec(`DELETE FROM push_jobs WHERE created_at < datetime('now', '-7 days')`)
	return nil
}

func logPushFailure(ptyID string, err error) {
	// Keep token values out of logs by construction: queue errors contain only
	// schema/IO information and the PTY id.
	fmt.Printf("push: cannot queue completion for %s: %v\n", ptyID, err)
}
