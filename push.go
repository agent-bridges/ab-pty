package main

import (
	"encoding/json"
	"fmt"
	"net/http"
	"strconv"
	"strings"
	"time"
)

const (
	pushCompletionDebounce = 3 * time.Second
	maxPushTokenBytes      = 4096
	maxPushJobsPerRead     = 100
)

type pushJob struct {
	ID                int64  `json:"id"`
	Token             string `json:"token"`
	DaemonFingerprint string `json:"daemon_fingerprint"`
	DaemonName        string `json:"daemon_name"`
	SessionID         string `json:"session_id"`
	SessionName       string `json:"session_name"`
	SessionLabel      string `json:"session_label"`
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
			created_at         DATETIME DEFAULT CURRENT_TIMESTAMP,
			UNIQUE(event_key, client_fingerprint)
		)
	`); err != nil {
		return fmt.Errorf("create push jobs: %w", err)
	}
	_, err := db.Exec(`CREATE INDEX IF NOT EXISTS push_jobs_created_idx ON push_jobs(created_at, id)`)
	return err
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
			Token string `json:"token"`
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
		tx, err := db.Begin()
		if err != nil {
			writeError(w, http.StatusInternalServerError, "failed to store push subscription")
			return
		}
		defer tx.Rollback()
		_, err = tx.Exec(`
			INSERT INTO push_subscriptions(client_fingerprint, client_name, token, updated_at)
			VALUES (?, ?, ?, CURRENT_TIMESTAMP)
			ON CONFLICT(client_fingerprint) DO UPDATE SET
				client_name = excluded.client_name,
				token = excluded.token,
				updated_at = CURRENT_TIMESTAMP
		`, principal.Client.Fingerprint, principal.Client.Name, body.Token)
		if err != nil {
			writeError(w, http.StatusInternalServerError, "failed to store push subscription")
			return
		}
		// Jobs copied the old token when they were created. Once Firebase rotates
		// it, those jobs can no longer be delivered and must not block newer ones.
		if _, err = tx.Exec(`DELETE FROM push_jobs WHERE client_fingerprint = ? AND token <> ?`, principal.Client.Fingerprint, body.Token); err != nil {
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
// DELETE is the acknowledgement after FCM accepted (or permanently rejected)
// a message.
func handlePushJobs(w http.ResponseWriter, r *http.Request) {
	setJSONHeaders(w)
	principal, ok := principalFromRequest(r)
	if !ok || principal.Client.Fingerprint == "" {
		writeError(w, http.StatusForbidden, "push jobs require an external client certificate")
		return
	}
	if r.URL.Path != "/api/push/jobs" {
		if r.Method != http.MethodDelete {
			writeError(w, http.StatusMethodNotAllowed, "Method not allowed")
			return
		}
		idText := strings.TrimPrefix(r.URL.Path, "/api/push/jobs/")
		id, err := strconv.ParseInt(idText, 10, 64)
		if err != nil || id < 1 {
			writeError(w, http.StatusBadRequest, "invalid push job id")
			return
		}
		if _, err := db.Exec(`DELETE FROM push_jobs WHERE id = ?`, id); err != nil {
			writeError(w, http.StatusInternalServerError, "failed to acknowledge push job")
			return
		}
		writeJSON(w, 0, map[string]bool{"ok": true})
		return
	}
	if r.Method != http.MethodGet {
		writeError(w, http.StatusMethodNotAllowed, "Method not allowed")
		return
	}
	rows, err := db.Query(`
		SELECT id, token, daemon_fingerprint, daemon_name, session_id, session_name, session_label, created_at
		FROM push_jobs ORDER BY id LIMIT ?
	`, maxPushJobsPerRead)
	if err != nil {
		writeError(w, http.StatusInternalServerError, "failed to read push jobs")
		return
	}
	defer rows.Close()
	jobs := make([]pushJob, 0)
	for rows.Next() {
		var job pushJob
		if err := rows.Scan(&job.ID, &job.Token, &job.DaemonFingerprint, &job.DaemonName, &job.SessionID, &job.SessionName, &job.SessionLabel, &job.CreatedAt); err != nil {
			writeError(w, http.StatusInternalServerError, "failed to read push job")
			return
		}
		jobs = append(jobs, job)
	}
	writeJSON(w, 0, jobs)
}

func authoritativeCompletion(previous aiStatusEntry, hadPrevious bool, next string) bool {
	return hadPrevious && previous.Authoritative && previous.Status == "working" && next == "idle"
}

func schedulePushCompletion(ptyID string, transitionAt time.Time) {
	go func() {
		timer := time.NewTimer(pushCompletionDebounce)
		defer timer.Stop()
		<-timer.C
		entry, ok := getAiStatusEntry(ptyID)
		if !ok || !entry.Authoritative || entry.Status != "idle" || !entry.UpdatedAt.Equal(transitionAt) {
			return
		}
		if err := queuePushCompletion(ptyID, transitionAt); err != nil {
			logPushFailure(ptyID, err)
		}
	}()
}

func queuePushCompletion(ptyID string, transitionAt time.Time) error {
	meta := getSessionMeta(ptyID)
	if meta == nil {
		return nil
	}
	fingerprint, err := daemonFingerprint()
	if err != nil {
		return fmt.Errorf("read daemon fingerprint: %w", err)
	}
	eventKey := ptyID + ":" + strconv.FormatInt(transitionAt.UnixNano(), 10)
	_, err = db.Exec(`
		INSERT OR IGNORE INTO push_jobs(
			event_key, client_fingerprint, token, daemon_fingerprint, daemon_name,
			session_id, session_name, session_label, created_at
		)
		SELECT ?, client_fingerprint, token, ?, ?, ?, ?, ?, CURRENT_TIMESTAMP
		FROM push_subscriptions
	`, eventKey, fingerprint, daemonName(), ptyID, meta.Name, meta.Label)
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
