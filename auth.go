package main

import (
	"context"
	"net/http"
	"strings"
)

type daemonAccess int

const (
	accessRead daemonAccess = iota
	accessOperate
	accessAdmin
)

type authPrincipal struct {
	Client    AuthorizedClient
	SessionID string
}

type authPrincipalContextKey struct{}

func principalFromRequest(r *http.Request) (authPrincipal, bool) {
	p, ok := r.Context().Value(authPrincipalContextKey{}).(authPrincipal)
	return p, ok
}

func clientRoleAllows(role string, access daemonAccess) bool {
	switch role {
	case ClientRoleAdmin:
		return true
	case ClientRoleOperator:
		return access != accessAdmin
	case ClientRoleReadOnly:
		return access == accessRead
	default:
		return false
	}
}

// requireDaemonAccess is the only authentication door for protected HTTP and
// WebSocket routes.
//
// An Authorization header selects the internal session-token path. That path
// is loopback-only and accepts only sess.* tokens tied to a currently-live PTY.
// It never falls through to certificate auth on failure.
//
// With no Authorization header, the request is external: the connection must
// have required mutual TLS and the presented certificate must still exist in
// the live allow-list. Its stored role is checked for every request, so revoke
// and role changes affect already-open keep-alive connections immediately.
func requireDaemonAccess(access daemonAccess, next http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		if auth := strings.TrimSpace(r.Header.Get("Authorization")); auth != "" {
			if !isLoopbackAddr(r.RemoteAddr) {
				http.Error(w, "authorization headers are only accepted from daemon-owned loopback sessions", http.StatusUnauthorized)
				return
			}
			parts := strings.SplitN(auth, " ", 2)
			if len(parts) != 2 || parts[0] != "Bearer" || !strings.HasPrefix(parts[1], "sess.") {
				http.Error(w, "invalid in-session authorization", http.StatusUnauthorized)
				return
			}
			sessionID, ok := validateSessionToken(parts[1])
			if !ok {
				http.Error(w, "invalid or expired session token", http.StatusUnauthorized)
				return
			}
			if access == accessAdmin {
				http.Error(w, "in-session credentials cannot manage client certificates", http.StatusForbidden)
				return
			}
			ctx := context.WithValue(r.Context(), authPrincipalContextKey{}, authPrincipal{SessionID: sessionID})
			next(w, r.WithContext(ctx))
			return
		}

		if effectiveTLSMode(r) != TLSModeRequired {
			http.Error(w, "protected external API requires mutual TLS", http.StatusForbidden)
			return
		}
		fp := tlsCallerFingerprint(r)
		if fp == "" {
			http.Error(w, "client certificate required", http.StatusUnauthorized)
			return
		}
		client, ok := lookupAuthorizedClient(fp)
		if !ok {
			http.Error(w, "client certificate is not authorized", http.StatusUnauthorized)
			return
		}
		if !clientRoleAllows(client.Role, access) {
			http.Error(w, "client certificate role does not allow this operation", http.StatusForbidden)
			return
		}
		ctx := context.WithValue(r.Context(), authPrincipalContextKey{}, authPrincipal{Client: client})
		next(w, r.WithContext(ctx))
	}
}

// accessByMethod gives read-only certificates only safe HTTP methods. OPTIONS
// is non-mutating; the actual requested method is still checked separately.
func accessByMethod(next http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		access := accessOperate
		switch r.Method {
		case http.MethodGet, http.MethodHead, http.MethodOptions:
			access = accessRead
		}
		requireDaemonAccess(access, next)(w, r)
	}
}
