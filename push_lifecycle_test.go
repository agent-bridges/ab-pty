package main

import (
	"context"
	"encoding/json"
	"fmt"
	"net/http"
	"net/http/httptest"
	"strings"
	"testing"
	"time"
)

func preparePushTest(t *testing.T) string {
	t.Helper()
	prepareLinkTest(t)
	if err := initPushTables(); err != nil {
		t.Fatal(err)
	}
	if err := initPushTables(); err != nil {
		t.Fatal("non-idempotent migration", err)
	}
	for _, table := range []string{"push_jobs", "push_subscriptions"} {
		if _, err := db.Exec("DELETE FROM " + table); err != nil {
			t.Fatal(err)
		}
	}
	fp := strings.Repeat("ab", 32)
	if err := addAuthorizedClient("push-phone", fp, ClientRoleOperator); err != nil {
		t.Fatal(err)
	}
	if _, err := db.Exec(`INSERT INTO push_subscriptions(client_fingerprint, token, relay_fingerprint) VALUES (?, 'synthetic-token', ?)`, fp, strings.Repeat("ef", 32)); err != nil {
		t.Fatal(err)
	}
	return fp
}

func pushTestSession(t *testing.T, id string) {
	t.Helper()
	if _, err := db.Exec(`INSERT INTO session_meta(id, name) VALUES (?, ?)`, id, id); err != nil {
		t.Fatal(err)
	}
	clearAiStatusForTest(id)
	t.Cleanup(func() { clearAiStatusForTest(id) })
}

func pushTestRequest(method, path, body, fingerprint string) *httptest.ResponseRecorder {
	r := httptest.NewRequest(method, path, strings.NewReader(body))
	r = r.WithContext(context.WithValue(r.Context(), authPrincipalContextKey{}, authPrincipal{Client: AuthorizedClient{Fingerprint: fingerprint, Role: ClientRoleOperator}}))
	w := httptest.NewRecorder()
	if strings.HasPrefix(path, "/api/push/subscription") {
		handlePushSubscription(w, r)
	} else {
		handlePushJobs(w, r)
	}
	return w
}

func claimPushTestJobs(t *testing.T) []pushJob {
	t.Helper()
	w := pushTestRequest(http.MethodPost, "/api/push/jobs", "", strings.Repeat("cd", 32))
	if w.Code != 200 {
		t.Fatalf("claim: %d %s", w.Code, w.Body.String())
	}
	var jobs []pushJob
	if err := json.Unmarshal(w.Body.Bytes(), &jobs); err != nil {
		t.Fatal(err)
	}
	return jobs
}

func queuePushTest(t *testing.T, id string) {
	t.Helper()
	if err := queuePushCompletion(id, time.Now()); err != nil {
		t.Fatal(err)
	}
}

func TestPushRevocationCancelsOldAndNewJobs(t *testing.T) {
	fp := preparePushTest(t)
	pushTestSession(t, "revoke")
	queuePushTest(t, "revoke")
	if _, err := revokeAuthorizedClient(fp); err != nil {
		t.Fatal(err)
	}
	queuePushTest(t, "revoke")
	if jobs := claimPushTestJobs(t); len(jobs) != 0 {
		t.Fatal("revoked recipient receives jobs", jobs)
	}
	var n int
	if err := db.QueryRow(`SELECT COUNT(*) FROM push_subscriptions`).Scan(&n); err != nil || n != 0 {
		t.Fatal(n, err)
	}
}

func TestPushUnsubscribeCancelsPendingJobs(t *testing.T) {
	fp := preparePushTest(t)
	pushTestSession(t, "unsubscribe")
	queuePushTest(t, "unsubscribe")
	w := pushTestRequest(http.MethodDelete, "/api/push/subscription", "", fp)
	if w.Code != 200 {
		t.Fatal(w.Code)
	}
	if jobs := claimPushTestJobs(t); len(jobs) != 0 {
		t.Fatal("unsubscribe left jobs")
	}
}

func TestPushCompletionUsesOnlySuccessfulRootTurn(t *testing.T) {
	preparePushTest(t)
	pushTestSession(t, "completion")
	event := func(raw string) { handleCodexAppServerMessage("completion", []byte(raw)) }
	// The explicit resume request establishes the root, without replaying history.
	handleCodexClientMessage("completion", []byte(`{"method":"thread/resume","params":{"threadId":"main"}}`))
	event(`{"id":1,"result":{"thread":{"id":"main","source":"cli","turns":[{"id":"historical","status":"completed"}]}}}`)
	event(`{"id":2,"result":{"thread":{"id":"unrelated-read","source":"cli"}}}`)
	for _, status := range []string{"failed", "interrupted"} {
		event(`{"method":"turn/started","params":{"threadId":"main","turn":{"id":"bad"}}}`)
		event(fmt.Sprintf(`{"method":"turn/completed","params":{"threadId":"main","turn":{"id":"bad","status":%q}}}`, status))
	}
	event(`{"method":"turn/started","params":{"threadId":"main","turn":{"id":"good"}}}`)
	for _, status := range []string{`{"type":"active","activeFlags":["waitingOnApproval"]}`, `{"type":"systemError"}`, `{"type":"idle"}`} {
		event(`{"method":"thread/status/changed","params":{"threadId":"main","status":` + status + `}}`)
	}
	if len(claimPushTestJobs(t)) != 0 {
		t.Fatal("non-completion queued Finished")
	}
	event(`{"method":"item/completed","params":{"threadId":"main","turnId":"good","item":{"type":"agentMessage","phase":"final_answer","text":"Parent final"}}}`)
	event(`{"method":"thread/started","params":{"thread":{"id":"child","source":{"subAgent":"review"},"parentThreadId":"main"}}}`)
	event(`{"method":"turn/started","params":{"threadId":"child","turn":{"id":"child-turn"}}}`)
	event(`{"method":"item/completed","params":{"threadId":"child","turnId":"child-turn","item":{"type":"agentMessage","phase":"final_answer","text":"Child final"}}}`)
	event(`{"method":"turn/completed","params":{"threadId":"child","turn":{"id":"child-turn","status":"completed"}}}`)
	if got := pushCompletionMessage("completion"); got != "Parent final" {
		t.Fatal("child overwrote parent", got)
	}
	if len(claimPushTestJobs(t)) != 0 {
		t.Fatal("child queued Finished")
	}
	for i := 0; i < 2; i++ {
		event(`{"method":"turn/completed","params":{"threadId":"main","turn":{"id":"good","status":"completed"}}}`)
	}
	jobs := claimPushTestJobs(t)
	if len(jobs) != 1 || jobs[0].LastMessage != "Parent final" || jobs[0].EventKey != "codex:main:good" {
		t.Fatal(jobs)
	}
}

func TestPushLeaseRetryExpiryAndAcknowledgement(t *testing.T) {
	preparePushTest(t)
	pushTestSession(t, "leases")
	queuePushTest(t, "leases")
	jobs := claimPushTestJobs(t)
	if len(jobs) != 1 {
		t.Fatal(jobs)
	}
	job := jobs[0]
	if len(claimPushTestJobs(t)) != 0 {
		t.Fatal("two consumers claim one job")
	}
	path := fmt.Sprintf("/api/push/jobs/%d?lease_token=%s", job.ID, job.LeaseToken)
	if w := pushTestRequest(http.MethodPatch, path+"&retry_seconds=60", "", "core"); w.Code != 200 {
		t.Fatal(w.Code, w.Body.String())
	}
	if len(claimPushTestJobs(t)) != 0 {
		t.Fatal("retry delay ignored")
	}
	queuePushTest(t, "leases")
	if len(claimPushTestJobs(t)) != 1 {
		t.Fatal("retry blocks fresh jobs")
	}
	if _, err := db.Exec(`UPDATE push_jobs SET available_at=0 WHERE id=?`, job.ID); err != nil {
		t.Fatal(err)
	}
	reclaimed := claimPushTestJobs(t)
	if len(reclaimed) != 1 || reclaimed[0].LeaseToken == job.LeaseToken || reclaimed[0].Attempt != 2 {
		t.Fatal(reclaimed)
	}
	if w := pushTestRequest(http.MethodDelete, path, "", "core"); w.Code != 409 {
		t.Fatal("old lease accepted", w.Code)
	}
	path = fmt.Sprintf("/api/push/jobs/%d?lease_token=%s", job.ID, reclaimed[0].LeaseToken)
	if w := pushTestRequest(http.MethodDelete, path, "", "core"); w.Code != 200 {
		t.Fatal(w.Code, w.Body.String())
	}
}

func TestPushExpiredJobsAreNeverClaimed(t *testing.T) {
	preparePushTest(t)
	pushTestSession(t, "expired")
	queuePushTest(t, "expired")
	if _, err := db.Exec(`UPDATE push_jobs SET created_at=datetime('now','-8 days')`); err != nil {
		t.Fatal(err)
	}
	if len(claimPushTestJobs(t)) != 0 {
		t.Fatal("expired jobs delivered")
	}
}

func TestPushRegistrationCarriesRouteAndRotatesPendingToken(t *testing.T) {
	fp := preparePushTest(t)
	pushTestSession(t, "route")
	queuePushTest(t, "route")
	if w := pushTestRequest(http.MethodPut, "/api/push/subscription", `{"token":"new"}`, fp); w.Code != 400 {
		t.Fatal("missing route accepted", w.Code)
	}
	body := `{"token":"new","relay_fingerprint":"` + strings.Repeat("12", 32) + `"}`
	if w := pushTestRequest(http.MethodPut, "/api/push/subscription", body, fp); w.Code != 200 {
		t.Fatal(w.Code, w.Body.String())
	}
	jobs := claimPushTestJobs(t)
	if len(jobs) != 1 || jobs[0].Token != "new" || jobs[0].RelayFingerprint != strings.Repeat("12", 32) {
		t.Fatal(jobs)
	}
	path := fmt.Sprintf("/api/push/jobs/%d?lease_token=%s&invalid_token=1", jobs[0].ID, jobs[0].LeaseToken)
	if w := pushTestRequest(http.MethodDelete, path, "", "core"); w.Code != 200 {
		t.Fatal(w.Code, w.Body.String())
	}
	queuePushTest(t, "route")
	if len(claimPushTestJobs(t)) != 0 {
		t.Fatal("invalid token still subscribed")
	}
	if w := pushTestRequest(http.MethodGet, "/api/push/jobs", "", "core"); w.Code != 409 {
		t.Fatal("legacy unleased consumer accepted")
	}
}

func TestPushByteTruncationIsVisibleAndWordBounded(t *testing.T) {
	got := boundedPushMessage(strings.Repeat("длинноесловосочетание ", 100))
	if !strings.HasSuffix(got, "длинноесловосочетание…") || len(got) > maxPushMessageBytes {
		t.Fatal(got)
	}
}
