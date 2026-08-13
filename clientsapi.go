package main

// The one door only the machine itself can open.
//
// ### Why this endpoint exists
//
// Enrolling a phone on a machine used to mean an SSH session to that machine
// and `ab-pty client add <name> <sha256>`. For a person with several machines
// behind a relay that is the single most tedious thing left, and it is the
// step that cannot be moved to the relay — because the moment the relay can
// admit anybody to a machine, a compromised relay owns every machine behind
// it, and the whole design falls over.
//
// So the grant is made by the machine, to a caller the machine has already
// admitted. The device asking is holding a TLS session that only got past the
// handshake because its certificate is in this daemon's own allow-list. That
// is the authority: not the relay's word, not a token the relay could mint —
// a certificate this machine itself decided to trust, presented on the
// connection carrying the request.
//
// ### The three conditions, and why each one is separate
//
//  1. **The request arrived over TLS with a client certificate this daemon
//     authorises.** Not "some certificate" — the same lookup the handshake
//     does, repeated per request against the live table, so a device revoked a
//     second ago cannot enrol anything with a connection it already had.
//
//  2. **The connection required that certificate.** Not the process: the
//     daemon serves two listeners that disagree, and the one that matters is
//     the one this request came in on (see effectiveTLSMode). In `optional`
//     every stranger's certificate is tolerated, so "the caller is
//     authorised" would be a statement about an allow-list that the mode has
//     already stopped enforcing. Refusing here rather than trusting the check
//     is the difference between a rule and a habit.
//
//  3. **A valid key** (the daemon JWT or an in-session token), because the
//     wrapper this is registered under demands one. Enrolment is durable
//     access to a whole machine; it should cost at least as much as reading
//     the session list.
//
// The loopback exemption (AB_PTY_TLS_ALLOW_LOOPBACK) is deliberately no help
// here. It lets a local caller through the handshake without a certificate; it
// gives that caller no certificate to be authorised by, so condition 1 fails
// and the request is refused. A machine's allow-list is not editable by
// anything that merely runs on the machine over HTTP — that is what the CLI,
// with its own file permissions, is for.

import (
	"encoding/json"
	"fmt"
	"log"
	"net/http"
	"strings"
)

// tlsCallerFingerprint returns the fingerprint of the certificate on this
// request, or "" when there is none.
func tlsCallerFingerprint(r *http.Request) string {
	if r.TLS == nil || len(r.TLS.PeerCertificates) == 0 {
		return ""
	}
	return certFingerprint(r.TLS.PeerCertificates[0].Raw)
}

// requireEnrolledClient enforces conditions 1 and 2 above.
//
// The refusals are worded and separated on purpose: an app that cannot tell
// "this daemon is not locked down" from "you are not on its list" tells its
// user to fix the wrong machine.
func requireEnrolledClient(next func(http.ResponseWriter, *http.Request, AuthorizedClient)) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		setJSONHeaders(w)
		if mode := effectiveTLSMode(r); mode != TLSModeRequired {
			// In "optional" the allow-list is not being enforced, so a
			// caller being on it proves nothing about anybody else's
			// ability to reach this endpoint.
			writeJSON(w, http.StatusForbidden, map[string]string{
				"error":     "the client allow-list may only be changed over a connection where a client certificate was mandatory",
				"code":      "tls_mode",
				"tls_mode":  mode,
				"remediate": "start the daemon with AB_PTY_TLS_MODE=required",
			})
			return
		}
		fp := tlsCallerFingerprint(r)
		if fp == "" {
			// No certificate at all: a plain connection, or the loopback
			// exemption. Either way there is nobody here this daemon has
			// decided to trust.
			writeJSON(w, http.StatusForbidden, map[string]string{
				"error":     "this request presented no client certificate",
				"code":      "no_client_certificate",
				"remediate": "ab-pty client add <name> <sha256>, on this machine",
			})
			return
		}
		name, ok := lookupAuthorizedClient(fp)
		if !ok {
			log.Printf("tls: REJECT allow-list change from an unauthorized certificate (sha256 %s)", prettyFingerprint(fp))
			writeJSON(w, http.StatusForbidden, map[string]string{
				"error":       "this certificate is not on this machine's allow-list",
				"code":        "not_authorized",
				"fingerprint": fp,
				"remediate":   fmt.Sprintf("ab-pty client add <name> %s, on this machine", fp),
			})
			return
		}
		next(w, r, AuthorizedClient{Name: name, Fingerprint: fp})
	}
}

// handleTLSClients serves the machine's own allow-list: read it, add to it,
// and (via /api/tls/clients/<name|fingerprint>) remove from it.
func handleTLSClients(w http.ResponseWriter, r *http.Request, caller AuthorizedClient) {
	if allowOptions(w, r, "GET, POST, DELETE, OPTIONS") {
		return
	}
	target := strings.Trim(strings.TrimPrefix(r.URL.Path, "/api/tls/clients"), "/")

	switch {
	case r.Method == http.MethodGet && target == "":
		listTLSClients(w, caller)
	case r.Method == http.MethodPost && target == "":
		addTLSClient(w, r, caller)
	case r.Method == http.MethodDelete && target != "":
		revokeTLSClient(w, caller, target)
	default:
		writeError(w, http.StatusMethodNotAllowed, "Method not allowed")
	}
}

func listTLSClients(w http.ResponseWriter, caller AuthorizedClient) {
	clients, err := listAuthorizedClients()
	if err != nil {
		writeError(w, http.StatusInternalServerError, err.Error())
		return
	}
	rows := make([]map[string]interface{}, 0, len(clients))
	for _, c := range clients {
		rows = append(rows, map[string]interface{}{
			"name":        c.Name,
			"fingerprint": c.Fingerprint,
			"added_at":    c.AddedAt,
			"last_seen":   c.LastSeen,
			// Which of these is the caller. A phone has no other way to
			// recognise itself here, and that is what decides whether a
			// revoke button is ordinary or the last thing this phone
			// ever does to this machine.
			"self": strings.EqualFold(c.Fingerprint, caller.Fingerprint),
		})
	}
	writeJSON(w, 0, map[string]interface{}{"clients": rows, "caller": caller.Name})
}

func addTLSClient(w http.ResponseWriter, r *http.Request, caller AuthorizedClient) {
	var body struct {
		Name        string `json:"name"`
		Fingerprint string `json:"fingerprint"`
	}
	if err := json.NewDecoder(http.MaxBytesReader(w, r.Body, 8<<10)).Decode(&body); err != nil {
		writeError(w, http.StatusBadRequest, "expected {\"name\":…, \"fingerprint\":…}")
		return
	}
	fp, err := normalizeFingerprint(body.Fingerprint)
	if err != nil {
		writeError(w, http.StatusBadRequest, err.Error())
		return
	}
	name := strings.TrimSpace(body.Name)
	if name == "" {
		writeError(w, http.StatusBadRequest, "a name is required — it is what a later revocation is aimed at")
		return
	}
	if err := addAuthorizedClient(name, fp); err != nil {
		writeError(w, http.StatusInternalServerError, err.Error())
		return
	}
	// Logged with both parties: an allow-list gaining an entry is the one
	// event on this daemon that a person may later need to account for, and
	// "who let this in" has to be answerable from the journal alone.
	log.Printf("tls: client %q (sha256 %s) authorized client %q (sha256 %s) over mutual TLS",
		caller.Name, prettyFingerprint(caller.Fingerprint), name, prettyFingerprint(fp))
	writeJSON(w, http.StatusCreated, map[string]interface{}{
		"name":        name,
		"fingerprint": fp,
		"added_by":    caller.Name,
	})
}

func revokeTLSClient(w http.ResponseWriter, caller AuthorizedClient, target string) {
	// Revoking the certificate you are holding the connection open with is
	// never what somebody meant to do, and it is not undoable from the app:
	// the next request fails at the handshake. The CLI on the machine can
	// still do it, where the consequence is obvious.
	if strings.EqualFold(target, caller.Name) || strings.EqualFold(target, caller.Fingerprint) {
		writeJSON(w, http.StatusForbidden, map[string]string{
			"error":     "this is the certificate this request arrived on — revoking it would lock this device out with no way back",
			"code":      "self_revoke",
			"remediate": "ab-pty client revoke " + caller.Name + ", on this machine",
		})
		return
	}
	n, err := revokeAuthorizedClient(target)
	if err != nil {
		writeError(w, http.StatusInternalServerError, err.Error())
		return
	}
	if n == 0 {
		writeError(w, http.StatusNotFound, fmt.Sprintf("no authorized client matched %q", target))
		return
	}
	log.Printf("tls: client %q revoked %d client certificate(s) matching %q over mutual TLS — effective immediately",
		caller.Name, n, target)
	writeJSON(w, 0, map[string]interface{}{"revoked": n, "revoked_by": caller.Name})
}
