# Daemon authentication

The daemon has no static JWT and no externally accepted bearer token.

Protected external HTTP and WebSocket requests require a connection on which
mutual TLS was mandatory. The leaf certificate fingerprint must be present in
the daemon's live `tls_clients` table. The role is read from SQLite on every
request, so role changes and revocation also affect existing keep-alive
connections:

- `read-only`: safe `GET`/`HEAD` API requests and `/ws/pty-state`; no mutations
  and no interactive `/ws` attach.
- `operator`: all normal PTY, board, project, filesystem, tunnel and WebSocket
  operations; no client allow-list access.
- `admin`: operator access plus `/api/tls/clients` list/add/role/revoke.

`/health` and `/info` remain public. A relay connection always requires mTLS.
When the network listener is configured `off` or `optional`, protected
external routes fail closed; those modes do not provide another auth method.

## Enrolment and roles

The local/offline CLI opens the daemon SQLite database directly, so initial
enrolment works even when no client can connect yet. Role is mandatory:

```text
ab-pty client add <name> <sha256-fingerprint> <read-only|operator|admin>
ab-pty client role <name|fingerprint> <read-only|operator|admin>
ab-pty client list
ab-pty client revoke <name|fingerprint>
```

The long spelling `ab-pty tls client ...` is equivalent. Rows created before
roles existed migrate to `operator`, never `admin`.

An admin certificate can use the HTTP API:

- `GET /api/tls/clients`
- `POST /api/tls/clients` with
  `{"name":"phone","fingerprint":"<64 hex>","role":"operator"}`
- `PATCH /api/tls/clients/<name-or-fingerprint>` with
  `{"role":"read-only|operator|admin"}`
- `DELETE /api/tls/clients/<name-or-fingerprint>`

## In-session CLI

Each daemon-created PTY receives `AB_PTY_SESSION_TOKEN=sess.…`. It is HMACed
with a random, in-memory daemon secret, accepted only from the real loopback
peer, tied to a live session, and operator-equivalent. It cannot manage client
certificates. A session end or daemon restart invalidates it.

An `Authorization` header selects this internal path. Invalid, remote or
non-`sess.*` authorization is rejected and never retried as certificate auth.

When the daemon runs in `required` mode without the relay-incompatible
loopback exemption, local CLI and Claude hook connections also use mTLS. The
daemon propagates these exact values into every child PTY:

- `AB_PTY_TLS_MODE=required`
- `AB_PTY_PORT` (the actual listener port, default `8421`)
- `AB_PTY_TLS_CERT` (the exact self-signed server certificate trusted for
  `localhost`; no system-root or insecure fallback)
- `AB_PTY_CLIENT_CERT` and `AB_PTY_CLIENT_KEY` (an allow-listed local client
  identity)

`claude-hook-forwarder.sh` refuses to run without this contract and posts to
`https://localhost:$AB_PTY_PORT/api/hook` using `curl --cert`, `--key`, and
`--cacert`; it never uses `-k`.
