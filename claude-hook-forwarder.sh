#!/usr/bin/env bash
set -eu

payload="$(cat)"

if [ -z "$payload" ]; then
  exit 0
fi

: "${AB_PTY_CLIENT_CERT:?AB_PTY_CLIENT_CERT is required for daemon mTLS}"
: "${AB_PTY_CLIENT_KEY:?AB_PTY_CLIENT_KEY is required for daemon mTLS}"
: "${AB_PTY_TLS_CERT:?AB_PTY_TLS_CERT is required to verify the daemon certificate}"

if [ "${AB_PTY_TLS_MODE:-}" != "required" ]; then
  printf '%s\n' 'AB_PTY_TLS_MODE=required is required for the hook forwarder' >&2
  exit 1
fi

if command -v python3 >/dev/null 2>&1; then
  payload="$(printf '%s' "$payload" | python3 -c "
import sys,json
d=json.load(sys.stdin)
ppid=int(sys.argv[1]) if len(sys.argv)>1 else 0
if ppid>0: d['caller_pid']=ppid
print(json.dumps(d))
" "${PPID:-0}")"
elif command -v jq >/dev/null 2>&1; then
  payload="$(printf '%s' "$payload" | jq -c --argjson caller_pid "${PPID:-0}" '. + {caller_pid: $caller_pid}')"
elif command -v node >/dev/null 2>&1; then
  payload="$(printf '%s' "$payload" | node -e '
const fs=require("fs");const d=JSON.parse(fs.readFileSync(0,"utf8"));
const p=Number(process.argv[1]||0);if(p>0)d.caller_pid=p;
process.stdout.write(JSON.stringify(d));
' "${PPID:-0}")"
fi

curl -sf \
  --proto '=https' \
  --tlsv1.2 \
  --cert "$AB_PTY_CLIENT_CERT" \
  --key "$AB_PTY_CLIENT_KEY" \
  --cacert "$AB_PTY_TLS_CERT" \
  -X POST \
  "https://localhost:${AB_PTY_PORT:-8421}/api/hook" \
  -H 'Content-Type: application/json' \
  --data-binary "$payload"
