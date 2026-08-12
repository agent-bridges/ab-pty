package main

import (
	"bufio"
	"context"
	"crypto/hmac"
	"crypto/rand"
	"crypto/sha256"
	"crypto/subtle"
	"crypto/tls"
	"database/sql"
	_ "embed"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"flag"
	"fmt"
	"io"
	"log"
	"net"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"os/signal"
	"os/user"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"
	"unsafe"

	"github.com/creack/pty"
	"github.com/fsnotify/fsnotify"
	"github.com/golang-jwt/jwt/v5"
	"github.com/gorilla/websocket"
	_ "github.com/mattn/go-sqlite3"
	"golang.org/x/sys/unix"
)

// SafeConn wraps websocket.Conn with a mutex for safe concurrent writes
type SafeConn struct {
	conn *websocket.Conn
	mu   sync.Mutex
}

// WriteMessage writes under a deadline. gorilla/websocket with no write
// deadline blocks until the TCP window opens, i.e. potentially forever if the
// peer is gone-but-not-closed; that is how one dead client used to pin a
// broadcast goroutine for the life of the process.
func (sc *SafeConn) WriteMessage(messageType int, data []byte) error {
	sc.mu.Lock()
	defer sc.mu.Unlock()
	sc.conn.SetWriteDeadline(time.Now().Add(wsWriteWait))
	return sc.conn.WriteMessage(messageType, data)
}

func (sc *SafeConn) WriteJSON(v interface{}) error {
	sc.mu.Lock()
	defer sc.mu.Unlock()
	sc.conn.SetWriteDeadline(time.Now().Add(wsWriteWait))
	return sc.conn.WriteJSON(v)
}

// ReadMessage extends the read deadline on every frame that arrives. Any
// traffic at all — an application-level {"type":"ping"}, terminal input, a
// pong — proves the peer is there, so a client that never learned about
// websocket control frames still keeps itself alive simply by talking.
func (sc *SafeConn) ReadMessage() (int, []byte, error) {
	t, data, err := sc.conn.ReadMessage()
	if err == nil {
		sc.conn.SetReadDeadline(time.Now().Add(wsPongWait))
	}
	return t, data, err
}

func (sc *SafeConn) Close() error {
	return sc.conn.Close()
}

// Session represents a PTY session
type Session struct {
	ID               string
	Name             string
	ProjectPath      string
	LastCwd          string
	LastInputAt      time.Time
	LastOutputAt     time.Time
	LastOutputDigest string
	CreatedAt        time.Time
	Alive            bool
	ShellOnly        bool
	Pty              *os.File
	Cmd              *exec.Cmd
	Clients          map[*SafeConn]bool
	Scrollback       []string
	LastRows         int
	LastCols         int
	// BracketedPaste is the foreground app's last known bracketed-paste
	// mode (CSI ?2004h enables, CSI ?2004l disables). Tracked by
	// readPtyLoop scanning output. When true, `send`/`write` must wrap
	// the payload in \x1b[200~ ... \x1b[201~ so the TUI treats the bytes
	// as a paste; the Enter then has to follow OUTSIDE the markers as a
	// real keypress, otherwise the \r is bundled into the paste and the
	// message never submits (observed in Codex 0.139+, Claude Code 2.x).
	BracketedPaste bool
	mu             sync.RWMutex
}

// IsAlive reports whether the PTY process is still running.
//
// Always use this instead of reading s.Alive directly. The flag is written
// from two goroutines that do not hold sessionsMu — readPtyLoop when the
// PTY hits EOF, and killSession on an explicit kill — while it is read
// from every HTTP handler and from all three per-session trackers
// (trackCwd, trackAICmd, trackClaudeSession). `go test -race` flagged the
// unguarded pair (killSession write vs trackCwd read) as a genuine data
// race; the accessors close it.
//
// Note this takes session.mu, NOT sessionsMu — the two are independent, so
// calling IsAlive while holding sessionsMu is safe. It is NOT safe to call
// it while already holding session.mu (RWMutex is not reentrant); read the
// field directly in that case.
func (s *Session) IsAlive() bool {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return s.Alive
}

// setAlive updates the liveness flag under session.mu. See IsAlive for why
// the direct assignment it replaces was unsafe.
func (s *Session) setAlive(v bool) {
	s.mu.Lock()
	s.Alive = v
	s.mu.Unlock()
}

// Winsize returns the terminal's last known rows and cols, and setWinsize
// stores them — both under session.mu. The resize path in handleWebSocket
// used to read-compare-write these fields bare, which the race detector
// caught against readers in other goroutines. Returning the pair together
// also means a caller can never observe a half-updated size.
func (s *Session) Winsize() (rows, cols int) {
	s.mu.RLock()
	defer s.mu.RUnlock()
	return s.LastRows, s.LastCols
}

func (s *Session) setWinsize(rows, cols int) {
	s.mu.Lock()
	s.LastRows = rows
	s.LastCols = cols
	s.mu.Unlock()
}

// SessionMeta from DB
type SessionMeta struct {
	ID        string
	Label     string
	Locked    bool
	Meta      map[string]interface{}
	CreatedAt time.Time
	UpdatedAt time.Time
}

var (
	sessions       = make(map[string]*Session)
	sessionsMu     sync.RWMutex
	ptySubscribers = make(map[*stateSub]bool)
	subsMu         sync.RWMutex
	db             *sql.DB
	upgrader       = websocket.Upgrader{
		CheckOrigin: isAllowedWebSocketOrigin,
	}
)

var ansiEscapePattern = regexp.MustCompile(`\x1b(?:\[[0-?]*[ -/]*[@-~]|\].*?(?:\x07|\x1b\\)|[@-Z\\-_])`)

const maxScrollback = 10000

// ProcessInfo describes a child process running inside a PTY session
type ProcessInfo struct {
	Pid  int    `json:"pid"`
	Cmd  string `json:"cmd"`
	Args string `json:"args"`
}

// shellNames are processes to skip when reporting child processes
var shellNames = map[string]bool{
	"bash": true, "sh": true, "zsh": true, "fish": true, "dash": true, "ash": true,
}

// getChildProcesses recursively collects non-shell child processes of a given PID
func getChildProcesses(pid int) []ProcessInfo {
	var result []ProcessInfo
	collectChildren(pid, &result, 0)
	return result
}

// knownPathPatterns maps path substrings to friendly command names.
// Used when filepath.Base gives an unhelpful name (e.g. version number).
var knownPathPatterns = []struct {
	substr string
	name   string
}{
	{"/claude/", "claude"},
	{"/codex", "codex"},
	{"/aider", "aider"},
	{"/cursor", "cursor"},
}

// resolveKnownCmd tries to resolve an unhelpful basename (like "2.1.69")
// to a known tool name by checking the binary path and /proc/pid/exe symlink.
func resolveKnownCmd(cmd string, pid int, binPath string) string {
	// If basename already looks like a known name, keep it
	if !shellNames[cmd] && !looksLikeVersion(cmd) {
		return cmd
	}

	// Check binary path first
	for _, p := range knownPathPatterns {
		if strings.Contains(binPath, p.substr) {
			return p.name
		}
	}

	// Try /proc/pid/exe symlink
	if target, err := os.Readlink(fmt.Sprintf("/proc/%d/exe", pid)); err == nil {
		for _, p := range knownPathPatterns {
			if strings.Contains(target, p.substr) {
				return p.name
			}
		}
		// Use basename of exe target as fallback
		resolved := filepath.Base(target)
		if resolved != "" && resolved != "." && !looksLikeVersion(resolved) {
			return resolved
		}
	}

	return cmd
}

func looksLikeVersion(s string) bool {
	// "2.1.69", "1.0.0-beta" etc — starts with digit, contains dots
	if len(s) == 0 {
		return false
	}
	return s[0] >= '0' && s[0] <= '9' && strings.Contains(s, ".")
}

func collectChildren(pid int, result *[]ProcessInfo, depth int) {
	if depth > 10 {
		return // prevent runaway recursion
	}
	childrenPath := fmt.Sprintf("/proc/%d/task/%d/children", pid, pid)
	data, err := os.ReadFile(childrenPath)
	if err != nil {
		return
	}
	fields := strings.Fields(string(data))
	for _, f := range fields {
		childPid, err := strconv.Atoi(f)
		if err != nil {
			continue
		}
		// Read cmdline
		cmdlineData, err := os.ReadFile(fmt.Sprintf("/proc/%d/cmdline", childPid))
		if err != nil {
			continue
		}
		// cmdline is NUL-separated
		args := strings.ReplaceAll(string(cmdlineData), "\x00", " ")
		args = strings.TrimSpace(args)
		if args == "" {
			continue
		}
		// Extract command basename
		parts := strings.SplitN(args, " ", 2)
		cmd := filepath.Base(parts[0])

		// Claude binary is a symlink like /root/.local/share/claude/versions/2.1.69
		// so filepath.Base gives "2.1.69" — detect via exe symlink or path patterns
		cmd = resolveKnownCmd(cmd, childPid, parts[0])

		if !shellNames[cmd] {
			*result = append(*result, ProcessInfo{
				Pid:  childPid,
				Cmd:  cmd,
				Args: args,
			})
		}
		// Recurse into children of this child
		collectChildren(childPid, result, depth+1)
	}
}

// Version injected at build time via: go build -ldflags "-X main.Version=1.2.3"
var Version = "dev"

// JWT authentication
//
// Canonical location: /opt/ab/.jwt-secret
// Legacy locations (still read, with warning — remove after migration):
//
//	/opt/agent-bridge/.jwt-secret  (v0.1.9+)
//	/opt/nag-daemons/.jwt-secret   (pre-v0.1.9)
//
// AB_PTY_JWT_SECRET_PATH (see jwtSecretPathEnv below) overrides all of the
// above: when set, the secret is read only from that exact path, with no
// canonical/legacy fallback. This is for installs that have no /opt access
// at all (e.g. a non-canonical dev stand under $HOME) rather than for a
// deployment migrating off a legacy path — those should keep using the
// canonical /opt/ab layout.
const jwtSecretFileCanonical = "/opt/ab/.jwt-secret"

var jwtSecretFileLegacy = []string{
	"/opt/agent-bridge/.jwt-secret",
	"/opt/nag-daemons/.jwt-secret",
}

// Reported as the canonical path in logs/errors — kept as a var for tests.
var jwtSecretFile = jwtSecretFileCanonical

const allowedOriginsEnv = "AB_PTY_ALLOWED_ORIGINS"
const jwtSecretPathEnv = "AB_PTY_JWT_SECRET_PATH"

// jwtSecretSearchPaths returns the ordered list of paths to try when loading
// the JWT secret. Shared by jwtSecretCache.get() (daemon) and getLocalJWT()
// (CLI helper) so the AB_PTY_JWT_SECRET_PATH override behaves identically
// in both places.
func jwtSecretSearchPaths() []string {
	if envPath := strings.TrimSpace(os.Getenv(jwtSecretPathEnv)); envPath != "" {
		return []string{envPath}
	}
	return append([]string{jwtSecretFileCanonical}, jwtSecretFileLegacy...)
}

type jwtSecretCache struct {
	mu       sync.RWMutex
	secret   string
	lastLoad time.Time
	ttl      time.Duration
}

var jwtCache = &jwtSecretCache{ttl: 5 * time.Second}

func isAllowedWebSocketOrigin(r *http.Request) bool {
	origin := strings.TrimSpace(r.Header.Get("Origin"))
	if origin == "" {
		// Non-browser clients (backend proxy/CLI) often don't send Origin.
		return true
	}

	parsedOrigin, err := url.Parse(origin)
	if err != nil || parsedOrigin.Host == "" {
		return false
	}

	// Allow same host by default.
	if strings.EqualFold(parsedOrigin.Host, r.Host) {
		return true
	}

	// Optional allow-list for browser origins.
	allowed := strings.TrimSpace(os.Getenv(allowedOriginsEnv))
	if allowed == "" {
		return false
	}
	for _, item := range strings.Split(allowed, ",") {
		if strings.EqualFold(strings.TrimSpace(item), origin) {
			return true
		}
	}
	return false
}

func (c *jwtSecretCache) get() string {
	c.mu.RLock()
	if time.Since(c.lastLoad) < c.ttl && c.secret != "" {
		defer c.mu.RUnlock()
		return c.secret
	}
	c.mu.RUnlock()

	c.mu.Lock()
	defer c.mu.Unlock()

	if time.Since(c.lastLoad) < c.ttl && c.secret != "" {
		return c.secret
	}

	// AB_PTY_JWT_SECRET_PATH pins the secret to one explicit path — no
	// canonical/legacy fallback — for non-canonical installs (no /opt
	// access). Otherwise: canonical path first, then each legacy path with
	// a deprecation warning.
	envPath := strings.TrimSpace(os.Getenv(jwtSecretPathEnv))
	paths := jwtSecretSearchPaths()
	for _, p := range paths {
		data, err := os.ReadFile(p)
		if err != nil {
			continue
		}
		secret := strings.TrimSpace(string(data))
		if len(secret) < 32 {
			continue
		}
		c.secret = secret
		c.lastLoad = time.Now()
		switch {
		case envPath != "":
			log.Printf("JWT secret loaded from %s (%s)", p, jwtSecretPathEnv)
		case p == jwtSecretFileCanonical:
			log.Printf("JWT secret loaded from %s", p)
		default:
			log.Printf("WARN: JWT secret loaded from legacy path %s — migrate to %s", p, jwtSecretFileCanonical)
		}
		return c.secret
	}
	return c.secret
}

func jwtMiddleware(next http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		secret := jwtCache.get()
		if secret == "" {
			http.Error(w, "jwt secret is not configured", http.StatusServiceUnavailable)
			return
		}

		// Require bearer token from Authorization header.
		authHeader := r.Header.Get("Authorization")

		if authHeader == "" {
			http.Error(w, "missing authorization", http.StatusUnauthorized)
			return
		}

		parts := strings.SplitN(authHeader, " ", 2)
		if len(parts) != 2 || parts[0] != "Bearer" {
			http.Error(w, "invalid authorization format", http.StatusUnauthorized)
			return
		}

		token, err := jwt.Parse(parts[1], func(t *jwt.Token) (interface{}, error) {
			if _, ok := t.Method.(*jwt.SigningMethodHMAC); !ok {
				return nil, jwt.ErrSignatureInvalid
			}
			return []byte(secret), nil
		})

		if err != nil || !token.Valid {
			http.Error(w, "invalid token", http.StatusUnauthorized)
			return
		}

		next(w, r)
	}
}

// deriveSessionToken mints the in-session bearer token for a given sessionID.
// Format: "sess.<session_id>.<hex(HMAC_SHA256(jwtSecret, "session:"+session_id))>"
// The token is injected into the PTY's env as AB_PTY_SESSION_TOKEN so the agent
// running inside the session can call /api/pty/* endpoints on 127.0.0.1.
func deriveSessionToken(sessionID string) string {
	secret := jwtCache.get()
	if secret == "" {
		return ""
	}
	mac := hmac.New(sha256.New, []byte(secret))
	mac.Write([]byte("session:" + sessionID))
	return "sess." + sessionID + "." + hex.EncodeToString(mac.Sum(nil))
}

// validateSessionToken verifies a "sess.<id>.<hex>" token and returns the
// session id on success. The caller's session must be alive.
func validateSessionToken(token string) (string, bool) {
	if !strings.HasPrefix(token, "sess.") {
		return "", false
	}
	rest := token[len("sess."):]
	// sessionID may contain dots in legacy data; split on the LAST dot so hmac
	// (hex, no dots) is always the suffix.
	idx := strings.LastIndex(rest, ".")
	if idx < 0 {
		return "", false
	}
	sessionID := rest[:idx]
	presented := rest[idx+1:]

	secret := jwtCache.get()
	if secret == "" {
		return "", false
	}
	mac := hmac.New(sha256.New, []byte(secret))
	mac.Write([]byte("session:" + sessionID))
	expected := hex.EncodeToString(mac.Sum(nil))
	if subtle.ConstantTimeCompare([]byte(presented), []byte(expected)) != 1 {
		return "", false
	}

	sessionsMu.RLock()
	s, ok := sessions[sessionID]
	sessionsMu.RUnlock()
	if !ok || !s.IsAlive() {
		return "", false
	}
	return sessionID, true
}

// sessionTokenOrJwt accepts either the existing daemon JWT or an in-session
// bearer token minted by deriveSessionToken. Session-token holders get the
// same privileges as JWT holders in v1 — this matches the "the agent inside
// a PTY can do what the AB UI user can do" spec.
// requireLoopback rejects requests that did not originate on this host.
//
// Used for /api/hook, which Claude Code's hook runner POSTs to from inside
// a PTY we spawned. Those hooks have no JWT and no session token, so the
// endpoint cannot use sessionTokenOrJwt — but the daemon binds 0.0.0.0
// (the AB back reaches it over the LAN or via the :8422 TLS proxy), which
// left the handler callable by anyone who could route to port 8421. The
// handler writes the claude_session_id→pty_id mapping that later hook
// calls trust, so an unauthenticated remote caller could aim a session's
// status at an arbitrary PTY. Binding the check to the peer address keeps
// the local hook path working unchanged while closing the remote one.
//
// Note this trusts r.RemoteAddr, i.e. the real TCP peer. It is deliberately
// NOT reading X-Forwarded-For: the nginx TLS terminator on :8422 forwards
// to 127.0.0.1:8421, so honouring that header would let a remote caller
// re-open exactly the hole this closes.
func requireLoopback(next http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		host, _, err := net.SplitHostPort(r.RemoteAddr)
		if err != nil {
			// No port in RemoteAddr (unix socket, or a test's httptest
			// transport) — treat the whole value as the host.
			host = r.RemoteAddr
		}
		ip := net.ParseIP(host)
		if ip == nil || !ip.IsLoopback() {
			log.Printf("[hook] rejected non-loopback request from %s", r.RemoteAddr)
			http.Error(w, "loopback only", http.StatusForbidden)
			return
		}
		next(w, r)
	}
}

func sessionTokenOrJwt(next http.HandlerFunc) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		secret := jwtCache.get()
		if secret == "" {
			http.Error(w, "jwt secret is not configured", http.StatusServiceUnavailable)
			return
		}

		authHeader := r.Header.Get("Authorization")
		if authHeader == "" {
			http.Error(w, "missing authorization", http.StatusUnauthorized)
			return
		}
		parts := strings.SplitN(authHeader, " ", 2)
		if len(parts) != 2 || parts[0] != "Bearer" {
			http.Error(w, "invalid authorization format", http.StatusUnauthorized)
			return
		}
		presented := parts[1]

		// Session-token path
		if strings.HasPrefix(presented, "sess.") {
			if _, ok := validateSessionToken(presented); ok {
				next(w, r)
				return
			}
			http.Error(w, "invalid or expired session token", http.StatusUnauthorized)
			return
		}

		// JWT path (unchanged behaviour)
		token, err := jwt.Parse(presented, func(t *jwt.Token) (interface{}, error) {
			if _, ok := t.Method.(*jwt.SigningMethodHMAC); !ok {
				return nil, jwt.ErrSignatureInvalid
			}
			return []byte(secret), nil
		})
		if err != nil || !token.Valid {
			http.Error(w, "invalid token", http.StatusUnauthorized)
			return
		}
		next(w, r)
	}
}

// runGenJWT handles the genjwt subcommand
func runGenJWT(args []string) {
	var (
		genSecret bool
		expiry    string
		secretDir string
	)

	fs := flag.NewFlagSet("genjwt", flag.ExitOnError)
	fs.BoolVar(&genSecret, "gen-secret", false, "Generate new secret and save to .jwt-secret")
	fs.StringVar(&expiry, "expiry", "1y", "Token expiry: 1y, 30d, 24h")
	fs.StringVar(&secretDir, "dir", "/opt/ab", "Directory for .jwt-secret file")
	fs.Parse(args)

	secretPath := filepath.Join(secretDir, ".jwt-secret")

	// When reading (not generating), fall back to legacy paths with a warning.
	if !genSecret {
		if _, err := os.Stat(secretPath); os.IsNotExist(err) {
			for _, legacy := range jwtSecretFileLegacy {
				if _, lerr := os.Stat(legacy); lerr == nil {
					fmt.Fprintf(os.Stderr, "WARN: reading secret from legacy path %s — migrate to %s\n", legacy, secretPath)
					secretPath = legacy
					break
				}
			}
		}
	}

	if genSecret {
		// Generate random 32-byte secret
		bytes := make([]byte, 32)
		if _, err := rand.Read(bytes); err != nil {
			fmt.Fprintf(os.Stderr, "Error: %v\n", err)
			os.Exit(1)
		}
		secret := hex.EncodeToString(bytes)

		// Ensure directory exists
		os.MkdirAll(secretDir, 0755)

		// Save to file
		if err := os.WriteFile(secretPath, []byte(secret), 0600); err != nil {
			fmt.Fprintf(os.Stderr, "Error writing secret: %v\n", err)
			os.Exit(1)
		}
		fmt.Printf("Secret saved to %s\n", secretPath)
		return
	}

	// Read secret from file
	data, err := os.ReadFile(secretPath)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error reading secret from %s: %v\n", secretPath, err)
		fmt.Fprintln(os.Stderr, "Run with -gen-secret first to generate")
		os.Exit(1)
	}
	secret := strings.TrimSpace(string(data))

	// Parse expiry
	exp := parseExpiry(expiry)

	// Generate token
	token := jwt.NewWithClaims(jwt.SigningMethodHS256, jwt.MapClaims{
		"sub": "ab-pty",
		"iat": time.Now().Unix(),
		"exp": time.Now().Add(exp).Unix(),
	})

	tokenString, err := token.SignedString([]byte(secret))
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error signing: %v\n", err)
		os.Exit(1)
	}
	fmt.Println(tokenString)
}

func parseExpiry(s string) time.Duration {
	if len(s) < 2 {
		return 365 * 24 * time.Hour
	}
	unit := s[len(s)-1]
	var num int
	fmt.Sscanf(s[:len(s)-1], "%d", &num)
	switch unit {
	case 'y':
		return time.Duration(num) * 365 * 24 * time.Hour
	case 'd':
		return time.Duration(num) * 24 * time.Hour
	case 'h':
		return time.Duration(num) * time.Hour
	}
	return 365 * 24 * time.Hour
}

// CLI helper: get local JWT token
func getLocalJWT() string {
	// Same search order (and AB_PTY_JWT_SECRET_PATH override) as the
	// daemon's own jwtSecretCache.get() — see jwtSecretSearchPaths.
	paths := jwtSecretSearchPaths()
	var secret string
	for _, p := range paths {
		data, err := os.ReadFile(p)
		if err != nil {
			continue
		}
		s := strings.TrimSpace(string(data))
		if len(s) >= 32 {
			secret = s
			break
		}
	}
	if secret == "" {
		return ""
	}
	token := jwt.NewWithClaims(jwt.SigningMethodHS256, jwt.MapClaims{
		"sub": "ab-pty-cli",
		"iat": time.Now().Unix(),
		"exp": time.Now().Add(time.Hour).Unix(),
	})
	tokenString, _ := token.SignedString([]byte(secret))
	return tokenString
}

// CLI helper: make HTTP request to local daemon
func cliRequest(method, path string, body []byte) ([]byte, error) {
	port := os.Getenv("AB_PTY_PORT")
	if port == "" {
		port = "8421"
	}
	// The daemon may be serving TLS (AB_PTY_TLS_MODE != off). Its certificate
	// is self-signed by design, so loopback calls skip verification — this is
	// a same-host call to a socket we already trust, and the real auth is the
	// bearer token below.
	scheme := "http"
	if tlsMode() != TLSModeOff {
		scheme = "https"
	}
	url := fmt.Sprintf("%s://localhost:%s%s", scheme, port, path)

	var req *http.Request
	var err error
	if body != nil {
		req, err = http.NewRequest(method, url, strings.NewReader(string(body)))
	} else {
		req, err = http.NewRequest(method, url, nil)
	}
	if err != nil {
		return nil, err
	}

	// Prefer an in-session bearer token (set when running INSIDE a PTY the daemon
	// spawned). Falls back to minting a short-lived admin JWT from the daemon
	// secret on disk (when run ON the daemon host, e.g. from cron or sysadmin shell).
	if tok := os.Getenv("AB_PTY_SESSION_TOKEN"); tok != "" {
		req.Header.Set("Authorization", "Bearer "+tok)
	} else if token := getLocalJWT(); token != "" {
		req.Header.Set("Authorization", "Bearer "+token)
	}
	req.Header.Set("Content-Type", "application/json")

	client := &http.Client{Timeout: 10 * time.Second}
	if scheme == "https" {
		client.Transport = &http.Transport{TLSClientConfig: &tls.Config{InsecureSkipVerify: true}}
	}
	resp, err := client.Do(req)
	if err != nil {
		return nil, fmt.Errorf("daemon not running? %v", err)
	}
	defer resp.Body.Close()

	data, _ := io.ReadAll(resp.Body)
	if resp.StatusCode >= 400 {
		return nil, fmt.Errorf("HTTP %d: %s", resp.StatusCode, string(data))
	}
	return data, nil
}

// runListSessions lists active PTY sessions
func runListSessions() {
	data, err := cliRequest("GET", "/api/pty", nil)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}

	var result struct {
		Sessions []struct {
			ID      string `json:"id"`
			Name    string `json:"name"`
			Project string `json:"project_path"`
			Alive   bool   `json:"alive"`
		} `json:"sessions"`
	}
	if err := json.Unmarshal(data, &result); err != nil {
		// Try array format
		var sessions []struct {
			ID      string `json:"id"`
			Name    string `json:"name"`
			Project string `json:"project_path"`
			Alive   bool   `json:"alive"`
		}
		if err := json.Unmarshal(data, &sessions); err != nil {
			fmt.Printf("%s\n", data)
			return
		}
		result.Sessions = sessions
	}

	if len(result.Sessions) == 0 {
		fmt.Println("No active sessions")
		return
	}

	fmt.Printf("%-30s %-15s %-6s %s\n", "ID", "NAME", "ALIVE", "PROJECT")
	fmt.Println(strings.Repeat("-", 80))
	for _, s := range result.Sessions {
		alive := "no"
		// Plain bool on the CLI's JSON-decoded struct, not a *Session —
		// no accessor here.
		if s.Alive {
			alive = "yes"
		}
		name := s.Name
		if name == "" {
			name = "-"
		}
		fmt.Printf("%-30s %-15s %-6s %s\n", s.ID, name, alive, s.Project)
	}
}

// runCreateSession creates a new PTY session
func runCreateSession(args []string) {
	var (
		project   string
		shell     bool
		sessionID string
		name      string
	)

	// Find -cmd position to split args
	cmdIdx := -1
	for i, arg := range args {
		if arg == "-cmd" || arg == "--cmd" {
			cmdIdx = i
			break
		}
	}

	var customCmd []string
	flagArgs := args
	if cmdIdx >= 0 {
		flagArgs = args[:cmdIdx]
		if cmdIdx+1 < len(args) {
			customCmd = args[cmdIdx+1:]
		}
	}

	fs := flag.NewFlagSet("create", flag.ExitOnError)
	fs.StringVar(&project, "project", "", "Project path (required)")
	fs.StringVar(&project, "p", "", "Project path (short)")
	fs.BoolVar(&shell, "shell", false, "Create shell-only session (no claude)")
	fs.StringVar(&sessionID, "session", "", "Claude session ID to resume")
	fs.StringVar(&name, "name", "", "Session name")
	fs.StringVar(&name, "n", "", "Session name (short)")
	fs.Parse(flagArgs)

	if project == "" {
		fmt.Fprintln(os.Stderr, "Usage: ab-pty create -p /path [-shell] [-session ID] [-name NAME] [-cmd command args...]")
		fmt.Fprintln(os.Stderr, "\nExamples:")
		fmt.Fprintln(os.Stderr, "  ab-pty create -p /root -cmd vim /etc/hosts")
		fmt.Fprintln(os.Stderr, "  ab-pty create -p /project -cmd htop")
		fmt.Fprintln(os.Stderr, "  ab-pty create -p /project -shell")
		os.Exit(1)
	}

	body := map[string]interface{}{
		"project_path": project,
	}
	if shell {
		body["shell_only"] = true
	}
	if sessionID != "" {
		body["continue_session"] = sessionID
	}
	if name != "" {
		body["name"] = name
	}
	if len(customCmd) > 0 {
		body["cmd"] = customCmd
	}

	jsonBody, _ := json.Marshal(body)
	data, err := cliRequest("POST", "/api/pty", jsonBody)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}

	var result struct {
		OK        bool   `json:"ok"`
		SessionID string `json:"session_id"`
		Error     string `json:"error"`
	}
	json.Unmarshal(data, &result)

	if result.OK {
		fmt.Printf("Created session: %s\n", result.SessionID)
	} else {
		fmt.Fprintf(os.Stderr, "Failed: %s\n", result.Error)
		os.Exit(1)
	}
}

// runKillSession kills session(s) by ID or name
func runKillSession(target string) {
	// First get list of sessions
	data, err := cliRequest("GET", "/api/pty", nil)
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error: %v\n", err)
		os.Exit(1)
	}

	var sessions []struct {
		ID   string `json:"id"`
		Name string `json:"name"`
	}

	// Try to parse response
	var result struct {
		Sessions []struct {
			ID   string `json:"id"`
			Name string `json:"name"`
		} `json:"sessions"`
	}
	if err := json.Unmarshal(data, &result); err == nil {
		sessions = result.Sessions
	} else {
		json.Unmarshal(data, &sessions)
	}

	// Find matching sessions
	var toKill []string
	for _, s := range sessions {
		if s.ID == target || s.Name == target {
			toKill = append(toKill, s.ID)
		}
	}

	if len(toKill) == 0 {
		fmt.Fprintf(os.Stderr, "No sessions matching '%s'\n", target)
		os.Exit(1)
	}

	// Kill each matching session
	killed := 0
	for _, id := range toKill {
		_, err := cliRequest("DELETE", "/api/pty/"+id, nil)
		if err != nil {
			fmt.Fprintf(os.Stderr, "Failed to kill %s: %v\n", id, err)
		} else {
			fmt.Printf("Killed: %s\n", id)
			killed++
		}
	}

	if killed == 0 {
		os.Exit(1)
	}
}

// --- In-session client CLI ------------------------------------------------

func clientHelp() {
	fmt.Print(`ab — full UI-parity API client (for use inside a PTY session)

Authenticates via $AB_PTY_SESSION_TOKEN (injected by the daemon into every
session). Target defaults to http://127.0.0.1:${AB_PTY_PORT:-8421}.

Usage:
  ab sessions list [--table|-t]                       # default JSON; --table = human-scan format
  ab sessions get    <pty_id|name>
  ab sessions create --shell|--claude [--cwd PATH] [--name NAME] [--rows N] [--cols N]
  ab sessions kill   <pty_id|name>
  ab sessions send   <pty_id|name> "text"             # write + auto-submit (appends Enter)
  ab sessions write  <pty_id|name> "text"             # write only, DO NOT submit — user confirms
  ab sessions key    <pty_id|name> <key>              # enter|tab|esc|backspace|up|down|left|right|ctrl-c|ctrl-d|…
  ab sessions tail   <pty_id|name> [--lines N]        # alias: peek
  ab sessions meta   <pty_id|name> [--name N] [--label L] [--set k=v ...]   # --name renames the session
  ab sessions lock   <pty_id|name>
  ab sessions unlock <pty_id|name>

  ab notes list
  ab notes get    <id>
  ab notes create [-name "title"] [-content "body"|-]   # -content - reads stdin
  ab notes set    <id> "<content>" [--label NAME]       # content "-" reads stdin
  ab notes delete <id>

Behaviour of send vs write:
  send  — you want the peer agent to ACT on the text immediately (fire off a task).
  write — you want the peer's input buffer PRE-FILLED but leave the human / the
          next call in control of when to submit. User can edit before pressing
          Enter. To submit later: 'ab sessions key <id> enter'.

Either command accepts explicit --enter / --no-enter to override the default.

Examples (inside a PTY session, with $AB_PTY_SESSION_TOKEN preset):
  ab sessions list
  ab sessions send  pty_123 "please write the login form"   # auto-submit
  ab sessions write pty_123 "/refactor-component Button"    # draft; user edits & presses Enter
  ab sessions key   pty_123 enter                           # explicit Enter keypress
  ab sessions tail  pty_123 --lines 40
  ab notes create -name plan -content "Step 1: …"
  cat plan.md | ab notes create -name plan -content -      # pipe big bodies in
  ab notes set    note-1234-ab "new body" --label "renamed"

Note: the 'ab' command is a wrapper for 'ab-pty client'. If the wrapper
isn't installed, run 'ab-pty client sessions list' directly.
`)
}

func runClient(args []string) {
	if len(args) == 0 || args[0] == "-h" || args[0] == "--help" || args[0] == "help" {
		clientHelp()
		return
	}
	switch args[0] {
	case "sessions":
		runClientSessions(args[1:])
	case "notes":
		runClientNotes(args[1:])
	case "add", "list", "revoke":
		// mTLS client allow-list. `ab-pty client add|list|revoke` is the
		// documented spelling (it reads as "manage clients"); it shares the
		// `client` namespace with the in-session API CLI above, which only
		// ever uses the `sessions` / `notes` verbs, so there is no clash.
		// `ab-pty tls client ...` is the equivalent long form.
		runTLSClient(args)
	default:
		fmt.Fprintf(os.Stderr, "unknown client subcommand: %s\n", args[0])
		clientHelp()
		os.Exit(2)
	}
}

// runClientNotes — `ab notes ...` CLI. Notes are board_items of type "notes"
// stored in the daemon's SQLite (canonical canvas-component source of truth).
// Subcommands:
//
//	ab notes list                    — JSON array of all notes-type items
//	ab notes get <id>                — JSON for one note
//	ab notes create [-name "title"] [-content "body"]  — new note, prints id
//	ab notes set <id> "<content>"    — overwrite the note's content (and
//	                                   optional --label "x" to rename)
//	ab notes delete <id>             — remove
func runClientNotes(args []string) {
	if len(args) == 0 {
		fmt.Fprintln(os.Stderr, "usage: ab notes <list|get|create|set|delete> ...")
		os.Exit(2)
	}
	sub := args[0]
	rest := args[1:]
	switch sub {
	case "list":
		out, err := cliRequest("GET", "/api/board/items", nil)
		requireOK(err)
		// Filter to type=="notes". Server returns the full board mix; agents
		// usually only care about notes for this CLI.
		var items []map[string]interface{}
		if err := json.Unmarshal(out, &items); err != nil {
			fmt.Println(string(out))
			return
		}
		notes := items[:0]
		for _, it := range items {
			if t, _ := it["type"].(string); t == "notes" {
				notes = append(notes, it)
			}
		}
		buf, _ := json.MarshalIndent(notes, "", "  ")
		fmt.Println(string(buf))

	case "get":
		requireArg(rest, 0, "get", "<id>")
		out, err := cliRequest("GET", "/api/board/items", nil)
		requireOK(err)
		var items []map[string]interface{}
		if err := json.Unmarshal(out, &items); err != nil {
			fmt.Println(string(out))
			return
		}
		for _, it := range items {
			if id, _ := it["id"].(string); id == rest[0] {
				buf, _ := json.MarshalIndent(it, "", "  ")
				fmt.Println(string(buf))
				return
			}
		}
		fmt.Fprintf(os.Stderr, "note not found: %s\n", rest[0])
		os.Exit(1)

	case "create":
		// Flags: -name <label>, -content <body>. If body is "-" read stdin.
		// Stdin lets you pipe big notes: `cat plan.md | ab notes create -name plan -content -`.
		label := ""
		content := ""
		for i := 0; i < len(rest); i++ {
			switch rest[i] {
			case "-name", "--name":
				if i+1 < len(rest) {
					label = rest[i+1]
					i++
				}
			case "-content", "--content":
				if i+1 < len(rest) {
					content = rest[i+1]
					i++
				}
			}
		}
		if content == "-" {
			b, err := io.ReadAll(os.Stdin)
			requireOK(err)
			content = string(b)
		}
		// Random suffix from crypto/rand keeps ids collision-resistant even if
		// two CLI calls land in the same Unix second.
		var randB [4]byte
		_, _ = rand.Read(randB[:])
		id := fmt.Sprintf("note-%d-%s", time.Now().Unix(), hex.EncodeToString(randB[:]))
		if label == "" {
			label = "Note"
		}
		body, _ := json.Marshal(map[string]interface{}{
			"type":        "notes",
			"label":       label,
			"noteContent": content,
		})
		_, err := cliRequest("PUT", "/api/board/items/"+url.PathEscape(id), body)
		requireOK(err)
		fmt.Println(`{"ok":true,"id":"` + id + `"}`)

	case "set":
		requireArg(rest, 1, "set", "<id> \"<content>\" [--label NAME]")
		id := rest[0]
		content := rest[1]
		if content == "-" {
			b, err := io.ReadAll(os.Stdin)
			requireOK(err)
			content = string(b)
		}
		// Pull the existing item so we don't trash unrelated fields (label).
		listOut, err := cliRequest("GET", "/api/board/items", nil)
		requireOK(err)
		var items []map[string]interface{}
		json.Unmarshal(listOut, &items)
		var current map[string]interface{}
		for _, it := range items {
			if iid, _ := it["id"].(string); iid == id {
				current = it
				break
			}
		}
		if current == nil {
			fmt.Fprintf(os.Stderr, "note not found: %s\n", id)
			os.Exit(1)
		}
		label, _ := current["label"].(string)
		for i := 2; i < len(rest); i++ {
			if (rest[i] == "--label" || rest[i] == "-label") && i+1 < len(rest) {
				label = rest[i+1]
				i++
			}
		}
		body, _ := json.Marshal(map[string]interface{}{
			"type":        "notes",
			"label":       label,
			"noteContent": content,
		})
		_, err = cliRequest("PUT", "/api/board/items/"+url.PathEscape(id), body)
		requireOK(err)
		fmt.Println(`{"ok":true,"id":"` + id + `"}`)

	case "delete":
		requireArg(rest, 0, "delete", "<id>")
		_, err := cliRequest("DELETE", "/api/board/items/"+url.PathEscape(rest[0]), nil)
		requireOK(err)
		fmt.Println(`{"ok":true}`)

	default:
		fmt.Fprintf(os.Stderr, "unknown notes subcommand: %s\n", sub)
		os.Exit(2)
	}
}

// printSessionsTable renders `ab sessions list` output as a fixed-width
// table. Columns: NAME, ID, ALIVE, CWD, AI. Sorted by (alive desc, name)
// so alive sessions cluster at the top and same-prefix teams sit
// together. NAME comes first because that's what agents pass to
// send/write/tail. Meant for eyeballing; the JSON view (default) is
// still the machine-readable form.
func printSessionsTable(raw []byte) {
	var sessions []map[string]interface{}
	if err := json.Unmarshal(raw, &sessions); err != nil {
		fmt.Fprintf(os.Stderr, "Error parsing sessions JSON: %v\n", err)
		fmt.Println(string(raw))
		return
	}
	if len(sessions) == 0 {
		fmt.Println("(no sessions)")
		return
	}
	type row struct {
		name, id, cwd, ai string
		alive             bool
	}
	rows := make([]row, 0, len(sessions))
	for _, s := range sessions {
		name, _ := s["name"].(string)
		id, _ := s["id"].(string)
		alive, _ := s["alive"].(bool)
		cwd, _ := s["project_path"].(string)
		ai := ""
		if meta, ok := s["meta"].(map[string]interface{}); ok {
			if lc, ok := meta["last_ai_cmd"].(string); ok && lc != "" {
				ai = lc
				// Trim long node/absolute paths so column fits.
				if slash := strings.LastIndex(ai, "/"); slash >= 0 && slash < len(ai)-1 {
					ai = ai[slash+1:]
				}
			}
		}
		rows = append(rows, row{name: name, id: id, cwd: cwd, ai: ai, alive: alive})
	}
	sort.Slice(rows, func(i, j int) bool {
		if rows[i].alive != rows[j].alive {
			return rows[i].alive
		}
		return rows[i].name < rows[j].name
	})

	// Compute per-column widths against the actual data, capped so a long
	// path can't wreck alignment.
	max := func(a, b int) int {
		if a > b {
			return a
		}
		return b
	}
	nameW, idW, cwdW, aiW := len("NAME"), len("ID"), len("CWD"), len("AI")
	for _, r := range rows {
		nameW = max(nameW, len(r.name))
		idW = max(idW, len(r.id))
		cwdW = max(cwdW, len(r.cwd))
		aiW = max(aiW, len(r.ai))
	}
	if cwdW > 50 {
		cwdW = 50
	}
	if aiW > 20 {
		aiW = 20
	}
	trunc := func(s string, w int) string {
		if len(s) <= w {
			return s
		}
		return s[:w-1] + "…"
	}
	fmt.Printf("%-*s  %-*s  %-5s  %-*s  %-*s\n", nameW, "NAME", idW, "ID", "ALIVE", cwdW, "CWD", aiW, "AI")
	for _, r := range rows {
		state := "dead"
		if r.alive {
			state = "alive"
		}
		fmt.Printf("%-*s  %-*s  %-5s  %-*s  %-*s\n",
			nameW, r.name,
			idW, r.id,
			state,
			cwdW, trunc(r.cwd, cwdW),
			aiW, trunc(r.ai, aiW),
		)
	}
	fmt.Printf("\n%d session(s)\n", len(rows))
}

func runClientSessions(args []string) {
	if len(args) == 0 {
		clientHelp()
		os.Exit(2)
	}
	sub := args[0]
	rest := args[1:]
	switch sub {
	case "list":
		out, err := cliRequest("GET", "/api/pty", nil)
		requireOK(err)
		// Default output stays JSON so existing agent pipelines (`jq
		// '.[] | select(.name=="…")'`) keep working. `--table` gives a
		// scan-friendly view when a human or an LLM eyeballs the list:
		// id, name, alive, cwd, and the last AI cmd if the daemon knows
		// one (from meta.last_ai_cmd) — enough to distinguish sessions
		// at a glance without a second `sessions get` round-trip.
		wantTable := false
		for _, a := range rest {
			if a == "--table" || a == "-t" {
				wantTable = true
				break
			}
		}
		if wantTable {
			printSessionsTable(out)
		} else {
			fmt.Println(string(out))
		}
	case "get":
		requireArg(rest, 0, "get", "<pty_id>")
		out, err := cliRequest("GET", "/api/pty/"+rest[0], nil)
		requireOK(err)
		fmt.Println(string(out))
	case "create":
		// Delegate to existing runCreateSession's HTTP body builder — but we
		// want the CLI flags for `client sessions create` consistent with the
		// top-level `create` command. Easier: just reuse runCreateSession.
		runCreateSession(rest)
	case "kill":
		requireArg(rest, 0, "kill", "<pty_id>")
		_, err := cliRequest("DELETE", "/api/pty/"+rest[0], nil)
		requireOK(err)
		fmt.Println(`{"ok":true}`)
	case "write", "send":
		requireArg(rest, 1, sub, "<pty_id> <text>")
		target := rest[0]
		text := rest[1]
		// Different defaults:
		//   send  — auto-submit (append Enter). Use "fire-off task" semantics.
		//   write — NO submit. Peer sees text in input box; human/agent
		//           decides when to press Enter. Use "draft" semantics.
		// --enter / --no-enter override the default either way.
		enter := sub == "send"
		for _, a := range rest[2:] {
			switch a {
			case "--no-enter":
				enter = false
			case "--enter":
				enter = true
			}
		}
		body, _ := json.Marshal(map[string]interface{}{"text": text, "enter": enter})
		out, err := cliRequest("POST", "/api/pty/"+target+"/stdin", body)
		requireOK(err)
		fmt.Println(string(out))
	case "tail", "peek":
		requireArg(rest, 0, sub, "<pty_id> [--lines N]")
		target := rest[0]
		lines := 50
		for i := 1; i < len(rest); i++ {
			if rest[i] == "--lines" && i+1 < len(rest) {
				if n, err := strconv.Atoi(rest[i+1]); err == nil && n > 0 {
					lines = n
				}
				i++
			}
		}
		out, err := cliRequest("GET", fmt.Sprintf("/api/pty/%s/scrollback?lines=%d", target, lines), nil)
		requireOK(err)
		// Pretty-print lines one per row if the caller asked for --raw? v1: just
		// print the JSON so it stays machine-parseable.
		fmt.Println(string(out))
	case "meta":
		requireArg(rest, 0, "meta", "<pty_id|name> [--name N] [--label L] [--set k=v ...]")
		target := rest[0]
		payload := map[string]interface{}{}
		metaSet := map[string]interface{}{}
		for i := 1; i < len(rest); i++ {
			switch rest[i] {
			case "--name":
				if i+1 < len(rest) {
					payload["name"] = rest[i+1]
					i++
				}
			case "--label":
				if i+1 < len(rest) {
					payload["label"] = rest[i+1]
					i++
				}
			case "--set":
				if i+1 < len(rest) {
					kv := strings.SplitN(rest[i+1], "=", 2)
					if len(kv) == 2 {
						metaSet[kv[0]] = kv[1]
					}
					i++
				}
			}
		}
		if len(metaSet) > 0 {
			payload["meta"] = metaSet
		}
		body, _ := json.Marshal(payload)
		out, err := cliRequest("PATCH", "/api/pty/"+target+"/meta", body)
		requireOK(err)
		fmt.Println(string(out))
	case "key":
		requireArg(rest, 1, "key", "<pty_id> <key>  (enter|tab|esc|backspace|up|down|left|right|ctrl-c|ctrl-d|...)")
		target := rest[0]
		keyName := rest[1]
		body, _ := json.Marshal(map[string]interface{}{"key": keyName})
		out, err := cliRequest("POST", "/api/pty/"+target+"/key", body)
		requireOK(err)
		fmt.Println(string(out))
	case "lock":
		requireArg(rest, 0, "lock", "<pty_id>")
		out, err := cliRequest("POST", "/api/pty/"+rest[0]+"/lock", nil)
		requireOK(err)
		fmt.Println(string(out))
	case "unlock":
		requireArg(rest, 0, "unlock", "<pty_id>")
		out, err := cliRequest("DELETE", "/api/pty/"+rest[0]+"/lock", nil)
		requireOK(err)
		fmt.Println(string(out))
	default:
		fmt.Fprintf(os.Stderr, "unknown sessions subcommand: %s\n", sub)
		clientHelp()
		os.Exit(2)
	}
}

func requireArg(args []string, idx int, cmd, usage string) {
	if len(args) <= idx {
		fmt.Fprintf(os.Stderr, "Usage: ab-pty client sessions %s %s\n", cmd, usage)
		os.Exit(2)
	}
}

func requireOK(err error) {
	if err != nil {
		fmt.Fprintf(os.Stderr, "error: %v\n", err)
		os.Exit(1)
	}
}

// Projects indexer
var (
	claudeProjectsDir string
	indexMu           sync.RWMutex
)

// Project represents a Claude project
type Project struct {
	Hash         string `json:"hash"`
	Path         string `json:"path"`
	Name         string `json:"name"`
	SessionCount int    `json:"session_count"`
	LatestMtime  int64  `json:"latest_mtime"`
}

// ClaudeSession represents a session file
type ClaudeSession struct {
	ID           string `json:"id"`
	ProjectHash  string `json:"project_hash"`
	Created      string `json:"created"`
	Size         int64  `json:"size"`
	HasContent   bool   `json:"has_content"`
	MessageCount int    `json:"message_count"`
}

// getProjectHashByPath finds project hash by path
func getProjectHashByPath(path string) string {
	// Claude uses path with slashes replaced by dashes
	hash := strings.ReplaceAll(path, "/", "-")

	// Check if project exists
	var count int
	err := db.QueryRow("SELECT COUNT(*) FROM projects WHERE hash = ?", hash).Scan(&count)
	if err != nil || count == 0 {
		// Try to find by path field
		err = db.QueryRow("SELECT hash FROM projects WHERE path = ?", path).Scan(&hash)
		if err != nil {
			return ""
		}
	}
	return hash
}

// buildMux is the complete, reviewable route table of the daemon. It is a
// function rather than inline setup in main so that every listener — the
// network one and the relay one (relay.go) — provably serves the same routes,
// and so tests can drive the real handler set.
func buildMux() *http.ServeMux {
	// Routes live on a private mux rather than http.DefaultServeMux. The
	// default mux is process-global: any package linked into the binary
	// (net/http/pprof being the classic example) can register a handler on
	// it and silently expose an endpoint we never audited. A private mux
	// means the route table below is the complete, reviewable surface.
	mux := http.NewServeMux()

	// Public endpoints (no auth)
	mux.HandleFunc("/info", handleInfo)
	mux.HandleFunc("/health", handleHealth)

	// Protected endpoints — accept either the daemon JWT (AB UI, admin CLI)
	// or an in-session bearer token injected into PTY env (agent-to-daemon).
	mux.HandleFunc("/api/pty", sessionTokenOrJwt(handleListPty))
	mux.HandleFunc("/api/pty/", sessionTokenOrJwt(handlePtyAPI))
	mux.HandleFunc("/api/board/items", sessionTokenOrJwt(handleBoardItems))
	mux.HandleFunc("/api/board/items/", sessionTokenOrJwt(handleBoardItems))
	mux.HandleFunc("/api/board/layouts", sessionTokenOrJwt(handleBoardLayouts))
	mux.HandleFunc("/api/board/layouts/", sessionTokenOrJwt(handleBoardLayouts))
	mux.HandleFunc("/api/projects", sessionTokenOrJwt(handleListProjects))
	mux.HandleFunc("/api/projects/", sessionTokenOrJwt(handleProjectsAPI))
	mux.HandleFunc("/api/sessions/", sessionTokenOrJwt(handleSessionsAPI))
	mux.HandleFunc("/api/fs", sessionTokenOrJwt(handleFS))
	mux.HandleFunc("/api/mkdir", sessionTokenOrJwt(handleMkdir))
	mux.HandleFunc("/api/fs/download", sessionTokenOrJwt(handleFSDownload))
	mux.HandleFunc("/api/fs/upload", sessionTokenOrJwt(handleFSUpload))
	mux.HandleFunc("/api/paste-image", sessionTokenOrJwt(handlePasteImage))
	mux.HandleFunc("/api/tunnels", sessionTokenOrJwt(handleTunnels))
	mux.HandleFunc("/api/tunnels/", sessionTokenOrJwt(handleTunnels))
	mux.HandleFunc("/ws", sessionTokenOrJwt(handleWebSocket))
	mux.HandleFunc("/ws/pty-state", sessionTokenOrJwt(handlePtyState))

	// Hook endpoint — called by Claude Code hooks running inside our own
	// PTY sessions, so it carries no JWT. requireLoopback keeps it off the
	// network: the daemon binds 0.0.0.0 and the handler mutates the
	// claude-session→pty mapping, which a LAN neighbour must not reach.
	mux.HandleFunc("/api/hook", requireLoopback(handleHook))

	return mux
}

func main() {
	// Handle subcommands
	if len(os.Args) > 1 {
		switch os.Args[1] {
		case "help", "--help", "-h":
			fmt.Printf(`ab-pty v%s - PTY daemon for AB

Usage: ab-pty [command]

Server:
  (none)      Start the PTY daemon server

Session management (no JWT needed):
  list        List active PTY sessions
  create      Create new PTY session (use -h for options)
  kill <id>   Kill session by ID or name (kills all matching names)

In-session API client (for use INSIDE a PTY session — auth from env):
  client      Full UI-parity CLI: sessions list/get/create/kill/write/tail/meta/lock
              Run 'ab-pty client -h' for subcommands.

Utilities:
  version     Show version
  genjwt      Generate JWT token (use -h for options)
  tls         Native TLS / mutual TLS (init, status, fingerprint, client)
  client add <name> <sha256>    Authorize a client certificate (mTLS allow-list)
  client list                   List authorized client certificates
  client revoke <name>          Revoke one (takes effect immediately)
  mcp         Run in MCP mode
  setup-mcp   Setup MCP config in claude_desktop_config.json
  help        Show this help

Environment variables:
  AB_PTY_PORT              Server port (default: 8421)
  AB_PTY_DATABASE          SQLite database path (default: /opt/ab/data/sessions.db)
  AB_PTY_JWT_SECRET_PATH   JWT secret file path (default: /opt/ab/.jwt-secret, then legacy paths)
  AB_PTY_SESSION_ID        (set by daemon in each PTY) caller session id
  AB_PTY_SESSION_TOKEN     (set by daemon in each PTY) bearer for /api/pty/* calls

TLS (all opt-in; the default is plain HTTP, exactly as before):
  AB_PTY_TLS_MODE          off (default) | optional | required
                           off      — plain HTTP, no certificates touched.
                           optional — HTTPS; a client certificate is requested
                                      but not required. Enrolment mode: the app
                                      connects without a key so its fingerprint
                                      can be registered.
                           required — HTTPS; the client must present a
                                      certificate whose SHA-256 fingerprint is
                                      in the allow-list, or the TLS handshake
                                      is aborted before any HTTP is served.
  AB_PTY_TLS_CERT          Server certificate (default: <jwt-secret-dir>/tls/server.crt)
  AB_PTY_TLS_KEY           Server key         (default: <jwt-secret-dir>/tls/server.key)
  AB_PTY_TLS_ALLOW_LOOPBACK  1 = connections from 127.0.0.1/::1 may skip the
                           client certificate even in required mode (keeps the
                           in-session 'ab' CLI and /api/hook working). Default 0.

Setup:
  ab-pty tls init                        # generate the server keypair (SANs
                                         # cover localhost, 127.0.0.1, ::1, the
                                         # hostname and every interface IP)
  ab-pty client add phone <sha256>       # authorize a client certificate
  AB_PTY_TLS_MODE=required ab-pty        # run locked down
`, Version)
			return
		case "list":
			runListSessions()
			return
		case "create":
			runCreateSession(os.Args[2:])
			return
		case "kill":
			if len(os.Args) < 3 {
				fmt.Fprintln(os.Stderr, "Usage: ab-pty kill <session_id or name>")
				os.Exit(1)
			}
			runKillSession(os.Args[2])
			return
		case "genjwt":
			runGenJWT(os.Args[2:])
			return
		case "version":
			fmt.Println(Version)
			return
		case "mcp":
			runMCPMode()
			return
		case "setup-mcp":
			setupMCPConfig()
			return
		case "client":
			runClient(os.Args[2:])
			return
		case "tls":
			runTLS(os.Args[2:])
			return
		}
	}

	// Singleton check - prevent multiple instances
	execPath, _ := os.Executable()
	lockFile := filepath.Join(filepath.Dir(execPath), ".ab-pty.lock")
	lockFd, err := os.OpenFile(lockFile, os.O_CREATE|os.O_RDWR, 0644)
	if err != nil {
		log.Fatalf("Cannot open lock file: %v", err)
	}
	err = syscall.Flock(int(lockFd.Fd()), syscall.LOCK_EX|syscall.LOCK_NB)
	if err != nil {
		log.Fatal("Another instance of ab-pty is already running")
	}
	// Keep lockFd open for the lifetime of the process (lock auto-releases on exit)

	port := os.Getenv("AB_PTY_PORT")
	if port == "" {
		port = "8421"
	}

	initDB()
	restoreSessions()
	cleanupStaleBoardItems()
	initProjectsIndexer()
	ensureMCPConfigured()
	ensureHooksConfigured()
	ensureAbSkillInstalled()

	mux := buildMux()

	// Periodic PTY state broadcast (processes change without events)
	go func() {
		ticker := time.NewTicker(3 * time.Second)
		defer ticker.Stop()
		for range ticker.C {
			broadcastPtyState()
		}
	}()

	log.Printf("AB-PTY starting on :%s", port)

	// Create listener with SO_REUSEPORT for graceful restart.
	// The option number differs per OS (15 on Linux, 0x200 on Darwin) — a
	// hardcoded Linux value here used to make the daemon fail to listen at
	// all on macOS with "protocol not available". x/sys/unix.SO_REUSEPORT
	// resolves to the correct value for whichever OS this binary is built
	// for.
	lc := net.ListenConfig{
		Control: func(network, address string, c syscall.RawConn) error {
			var opErr error
			err := c.Control(func(fd uintptr) {
				opErr = syscall.SetsockoptInt(int(fd), syscall.SOL_SOCKET, unix.SO_REUSEPORT, 1)
			})
			if err != nil {
				return err
			}
			return opErr
		},
	}

	ln, err := lc.Listen(context.Background(), "tcp", ":"+port)
	if err != nil {
		log.Fatal(err)
	}

	// Native TLS. Default AB_PTY_TLS_MODE=off leaves `ln` untouched — the
	// listener stays plain HTTP, byte-for-byte the pre-mTLS behaviour.
	if mode := tlsMode(); mode != TLSModeOff {
		tlsCfg, terr := buildTLSConfig(mode)
		if terr != nil {
			log.Fatal(terr)
		}
		ln = tls.NewListener(ln, tlsCfg)
		log.Printf("TLS enabled: mode=%s cert=%s sha256=%s", mode, tlsCertPath(), prettyFingerprint(tlsServerFingerprint))
		if mode == TLSModeRequired {
			n := 0
			if clients, cerr := listAuthorizedClients(); cerr == nil {
				n = len(clients)
			}
			log.Printf("TLS client auth: required, %d authorized certificate(s); loopback exempt=%v", n, tlsAllowLoopback())
			if n == 0 {
				log.Printf("WARN: mode=required with an empty allow-list — every client will be rejected. Add one: ab-pty client add <name> <sha256>")
			}
		}
	}

	srv := &http.Server{
		Handler: mux,
		// Slowloris guard. A client that opens a connection and dribbles
		// header bytes forever used to pin a goroutine for the life of the
		// process, because http.Serve's zero-value timeouts are infinite.
		ReadHeaderTimeout: 20 * time.Second,
		// Reap idle keep-alive connections. Does not apply to hijacked
		// (websocket) connections.
		IdleTimeout: 120 * time.Second,
		// 1 MiB of headers is already absurd for this API.
		MaxHeaderBytes: 1 << 20,

		// Deliberately NOT setting ReadTimeout / WriteTimeout: they are
		// absolute deadlines on the underlying net.Conn and survive the
		// hijack that gorilla/websocket performs on /ws and /ws/pty-state.
		// Setting either would tear down every terminal websocket on a
		// fixed timer regardless of activity. ReadHeaderTimeout covers the
		// pre-hijack window, which is the part that needs a bound; the
		// long-lived phase is policed by the websocket ping/pong loop.
	}

	// Relay path (docs/RELAY.md). Phase 0 wires the synthetic listener but
	// has no tunnel feeding it yet; when the ssh side lands it delivers its
	// channels to exactly this listener, and inherits this mux and a
	// required-mTLS config without a second authentication path existing.
	if relayEnabled() {
		ln, rerr := serveRelay(srv)
		if rerr != nil {
			log.Fatal(rerr)
		}
		relayLn = ln
	}

	// Graceful shutdown. systemd sends SIGTERM on `systemctl restart`; the
	// old code took the default action and died mid-write, so websocket
	// clients saw a truncated stream instead of a close frame and any
	// session_meta update still in flight was lost. Drain instead.
	shutdown := make(chan os.Signal, 1)
	signal.Notify(shutdown, syscall.SIGINT, syscall.SIGTERM)

	serveErr := make(chan error, 1)
	go func() {
		if err := srv.Serve(ln); err != nil && err != http.ErrServerClosed {
			serveErr <- err
		}
	}()

	select {
	case err := <-serveErr:
		log.Fatal(err)
	case sig := <-shutdown:
		log.Printf("received %s — shutting down", sig)
		// PTY processes are intentionally left running: they are
		// re-adopted on the next start by restoreSessions, which is the
		// whole point of session_meta.active. We only need to stop
		// accepting work and let in-flight HTTP handlers finish.
		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()
		if err := srv.Shutdown(ctx); err != nil {
			log.Printf("graceful shutdown timed out: %v", err)
		}
		closePtySubscribers()
		if db != nil {
			if err := db.Close(); err != nil {
				log.Printf("closing database: %v", err)
			}
		}
		log.Printf("shutdown complete")
	}
}

// closePtySubscribers sends a websocket close frame to every state
// subscriber so browsers see a clean disconnect (and reconnect promptly)
// instead of a dangling socket that only fails on the next write.
func closePtySubscribers() {
	subs := snapshotStateSubs()

	msg := websocket.FormatCloseMessage(websocket.CloseGoingAway, "daemon shutting down")
	for _, s := range subs {
		// Straight to the connection: the pump may already be parked on a
		// write, and a close frame that waits its turn is a close frame
		// nobody sees.
		s.conn.WriteMessage(websocket.CloseMessage, msg)
		s.stop("daemon shutting down")
	}
	if len(subs) > 0 {
		log.Printf("closed %d pty-state subscriber(s)", len(subs))
	}
}

func initDB() {
	// Canonical DB location: /opt/ab/data/sessions.db
	// Env AB_PTY_DATABASE overrides (used by Docker: /state/pty/sessions.db).
	// If neither the canonical dir nor env is set, fall back to legacy
	// /opt/data/sessions.db (hz1-avito, test hosts) with a warning.
	const canonicalDataDir = "/opt/ab/data"

	dbPath := os.Getenv("AB_PTY_DATABASE")
	if dbPath == "" {
		canonicalPath := filepath.Join(canonicalDataDir, "sessions.db")
		legacyPath := "/opt/data/sessions.db"

		if _, err := os.Stat(canonicalPath); err == nil {
			dbPath = canonicalPath
		} else if _, err := os.Stat(legacyPath); err == nil {
			log.Printf("WARN: using legacy DB path %s — migrate to %s", legacyPath, canonicalPath)
			dbPath = legacyPath
		} else {
			// First run: create canonical dir
			os.MkdirAll(canonicalDataDir, 0755)
			dbPath = canonicalPath
		}
	} else {
		// Ensure the directory for the env-provided path exists
		os.MkdirAll(filepath.Dir(dbPath), 0755)
	}

	var err error
	db, err = sql.Open("sqlite3", dbPath)
	if err != nil {
		log.Fatal(err)
	}

	_, err = db.Exec(`
		CREATE TABLE IF NOT EXISTS session_meta (
			id TEXT PRIMARY KEY,
			label TEXT DEFAULT '',
			locked INTEGER DEFAULT 0,
			active INTEGER DEFAULT 0,
			meta TEXT DEFAULT '{}',
			created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
			updated_at DATETIME DEFAULT CURRENT_TIMESTAMP
		)
	`)
	if err != nil {
		log.Fatal(err)
	}

	_, err = db.Exec(`
		CREATE TABLE IF NOT EXISTS board_items (
			id TEXT PRIMARY KEY,
			type TEXT NOT NULL,
			x INTEGER NOT NULL DEFAULT 0,
			y INTEGER NOT NULL DEFAULT 0,
			label TEXT DEFAULT '',
			pty_id TEXT,
			note_content TEXT,
			current_path TEXT,
			created_at TEXT NOT NULL,
			updated_at TEXT NOT NULL
		)
	`)
	if err != nil {
		log.Fatal(err)
	}

	_, err = db.Exec(`
		CREATE TABLE IF NOT EXISTS board_layouts (
			name TEXT PRIMARY KEY,
			snapshot TEXT NOT NULL,
			saved_at TEXT NOT NULL,
			updated_at TEXT NOT NULL
		)
	`)
	if err != nil {
		log.Fatal(err)
	}

	// Migration: add active column if not exists
	db.Exec(`ALTER TABLE session_meta ADD COLUMN active INTEGER DEFAULT 0`)
	db.Exec(`ALTER TABLE board_items ADD COLUMN x INTEGER NOT NULL DEFAULT 0`)
	db.Exec(`ALTER TABLE board_items ADD COLUMN y INTEGER NOT NULL DEFAULT 0`)
	// Tags are JSON-encoded []string. Free-form labels users attach to items;
	// many items per tag, many tags per item. IDE-mode sidebar renders a
	// section per distinct tag. Default '[]' so existing rows are valid.
	db.Exec(`ALTER TABLE board_items ADD COLUMN tags TEXT NOT NULL DEFAULT '[]'`)

	// Projects indexer tables
	_, err = db.Exec(`
		CREATE TABLE IF NOT EXISTS projects (
			hash TEXT PRIMARY KEY,
			path TEXT,
			name TEXT,
			session_count INTEGER DEFAULT 0,
			latest_mtime INTEGER DEFAULT 0,
			settings TEXT DEFAULT '{}'
		)
	`)
	if err != nil {
		log.Fatal(err)
	}

	// Migration: add settings column if not exists (ignore error if already exists)
	db.Exec(`ALTER TABLE projects ADD COLUMN settings TEXT DEFAULT '{}'`)

	_, err = db.Exec(`
		CREATE TABLE IF NOT EXISTS claude_sessions (
			id TEXT PRIMARY KEY,
			project_hash TEXT,
			created TEXT,
			size INTEGER,
			has_content INTEGER DEFAULT 0,
			message_count INTEGER DEFAULT 0,
			FOREIGN KEY (project_hash) REFERENCES projects(hash)
		)
	`)
	if err != nil {
		log.Fatal(err)
	}

	_, err = db.Exec(`CREATE INDEX IF NOT EXISTS idx_sessions_project ON claude_sessions(project_hash)`)
	if err != nil {
		log.Fatal(err)
	}

	// Mutual-TLS client allow-list (see mtls.go). Created unconditionally,
	// including in AB_PTY_TLS_MODE=off installs, so `ab-pty client list`
	// answers on a daemon that has never had TLS switched on.
	initTLSClientsTable()
}

type BoardItemRecord struct {
	ID          string `json:"id"`
	Type        string `json:"type"`
	Label       string `json:"label"`
	PtyID       string `json:"ptyId,omitempty"`
	NoteContent string `json:"noteContent,omitempty"`
	CurrentPath string `json:"currentPath,omitempty"`
	// Free-form labels for IDE-mode organization. One item can have many
	// tags; sidebar groups items by distinct tag name. Always serialised as
	// a JSON array — never null — so the front can rely on the field.
	Tags []string `json:"tags"`
}

type BoardLayoutRecord struct {
	Name     string                 `json:"name"`
	SavedAt  string                 `json:"savedAt"`
	Snapshot map[string]interface{} `json:"snapshot"`
}

func listBoardItems() ([]map[string]interface{}, error) {
	rows, err := db.Query(`
		SELECT id, type, label, pty_id, note_content, current_path, tags
		FROM board_items
		ORDER BY updated_at DESC, created_at DESC, id ASC
	`)
	if err != nil {
		return nil, err
	}
	defer rows.Close()

	// Build set of live session IDs to filter stale terminals
	sessionsMu.RLock()
	liveIDs := make(map[string]bool, len(sessions))
	for id := range sessions {
		liveIDs[id] = true
	}
	sessionsMu.RUnlock()

	items := make([]map[string]interface{}, 0)
	var staleIDs []string
	for rows.Next() {
		var id, itemType, label string
		var ptyID, noteContent, currentPath sql.NullString
		var tagsJSON sql.NullString
		if err := rows.Scan(&id, &itemType, &label, &ptyID, &noteContent, &currentPath, &tagsJSON); err != nil {
			return nil, err
		}

		// Drop stale terminals — ptyId empty or session not alive
		if itemType == "terminal" {
			if ptyID.String == "" || !liveIDs[ptyID.String] {
				staleIDs = append(staleIDs, id)
				continue
			}
		}

		// Tags are stored as JSON. Default to empty array so the front-end
		// never sees null (`tags ?? []` would also work but explicit is
		// safer for cross-language clients).
		tags := []string{}
		if tagsJSON.Valid && tagsJSON.String != "" {
			_ = json.Unmarshal([]byte(tagsJSON.String), &tags)
		}

		items = append(items, map[string]interface{}{
			"id":          id,
			"type":        itemType,
			"label":       label,
			"ptyId":       ptyID.String,
			"noteContent": noteContent.String,
			"currentPath": currentPath.String,
			"tags":        tags,
		})
	}

	// Clean up stale records from DB
	for _, id := range staleIDs {
		db.Exec(`DELETE FROM board_items WHERE id = ?`, id)
	}

	return items, rows.Err()
}

func upsertBoardItem(item BoardItemRecord) error {
	if item.ID == "" {
		return fmt.Errorf("missing item id")
	}
	if item.Type == "" {
		return fmt.Errorf("missing item type")
	}

	now := time.Now().UTC().Format(time.RFC3339)
	// Normalise tags to a JSON array. Nil/empty becomes "[]" so subsequent
	// reads always parse to a real slice. Trim/dedupe is the front-end's
	// job; we just persist whatever it sends.
	tags := item.Tags
	if tags == nil {
		tags = []string{}
	}
	tagsJSON, _ := json.Marshal(tags)
	_, err := db.Exec(`
		INSERT INTO board_items (id, type, label, pty_id, note_content, current_path, tags, created_at, updated_at)
		VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
		ON CONFLICT(id) DO UPDATE SET
			type = excluded.type,
			label = excluded.label,
			pty_id = excluded.pty_id,
			note_content = excluded.note_content,
			current_path = excluded.current_path,
			tags = excluded.tags,
			updated_at = excluded.updated_at
	`, item.ID, item.Type, item.Label, item.PtyID, item.NoteContent, item.CurrentPath, string(tagsJSON), now, now)
	return err
}

func deleteBoardItem(itemID string) (bool, error) {
	result, err := db.Exec(`DELETE FROM board_items WHERE id = ?`, itemID)
	if err != nil {
		return false, err
	}
	rowsAffected, err := result.RowsAffected()
	if err != nil {
		return false, err
	}
	return rowsAffected > 0, nil
}

func syncBoardItems(items []BoardItemRecord) error {
	tx, err := db.Begin()
	if err != nil {
		return err
	}
	defer tx.Rollback()

	if _, err := tx.Exec(`DELETE FROM board_items`); err != nil {
		return err
	}

	now := time.Now().UTC().Format(time.RFC3339)
	for _, item := range items {
		if item.ID == "" || item.Type == "" {
			return fmt.Errorf("invalid board item")
		}
		tags := item.Tags
		if tags == nil {
			tags = []string{}
		}
		tagsJSON, _ := json.Marshal(tags)
		if _, err := tx.Exec(`
			INSERT INTO board_items (id, type, label, pty_id, note_content, current_path, tags, created_at, updated_at)
			VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)
		`, item.ID, item.Type, item.Label, item.PtyID, item.NoteContent, item.CurrentPath, string(tagsJSON), now, now); err != nil {
			return err
		}
	}

	return tx.Commit()
}

func listBoardLayouts() ([]map[string]interface{}, error) {
	rows, err := db.Query(`SELECT name, snapshot, saved_at FROM board_layouts ORDER BY saved_at DESC, name ASC`)
	if err != nil {
		return nil, err
	}
	defer rows.Close()

	layouts := make([]map[string]interface{}, 0)
	for rows.Next() {
		var name, snapshotJSON, savedAt string
		if err := rows.Scan(&name, &snapshotJSON, &savedAt); err != nil {
			return nil, err
		}
		var snapshot map[string]interface{}
		if err := json.Unmarshal([]byte(snapshotJSON), &snapshot); err != nil {
			return nil, err
		}

		layouts = append(layouts, map[string]interface{}{
			"name":     name,
			"savedAt":  savedAt,
			"snapshot": snapshot,
		})
	}

	return layouts, rows.Err()
}

func getBoardLayout(name string) (*BoardLayoutRecord, error) {
	var snapshotJSON, savedAt string
	row := db.QueryRow(`SELECT snapshot, saved_at FROM board_layouts WHERE name = ?`, name)
	if err := row.Scan(&snapshotJSON, &savedAt); err != nil {
		if err == sql.ErrNoRows {
			return nil, nil
		}
		return nil, err
	}

	var snapshot map[string]interface{}
	if err := json.Unmarshal([]byte(snapshotJSON), &snapshot); err != nil {
		return nil, err
	}

	return &BoardLayoutRecord{
		Name:     name,
		SavedAt:  savedAt,
		Snapshot: snapshot,
	}, nil
}

func saveBoardLayout(name string, snapshot map[string]interface{}) (string, error) {
	if name == "" {
		return "", fmt.Errorf("missing layout name")
	}

	snapshotJSON, err := json.Marshal(snapshot)
	if err != nil {
		return "", err
	}

	now := time.Now().UTC().Format(time.RFC3339)
	_, err = db.Exec(`
		INSERT INTO board_layouts (name, snapshot, saved_at, updated_at)
		VALUES (?, ?, ?, ?)
		ON CONFLICT(name) DO UPDATE SET
			snapshot = excluded.snapshot,
			saved_at = excluded.saved_at,
			updated_at = excluded.updated_at
	`, name, string(snapshotJSON), now, now)
	if err != nil {
		return "", err
	}

	return now, nil
}

func deleteBoardLayout(name string) (bool, error) {
	result, err := db.Exec(`DELETE FROM board_layouts WHERE name = ?`, name)
	if err != nil {
		return false, err
	}
	rowsAffected, err := result.RowsAffected()
	if err != nil {
		return false, err
	}
	return rowsAffected > 0, nil
}

func getSessionMeta(sessionID string) *SessionMeta {
	row := db.QueryRow("SELECT id, label, locked, meta, created_at, updated_at FROM session_meta WHERE id = ?", sessionID)
	meta := &SessionMeta{}
	var metaJSON string
	var locked int
	err := row.Scan(&meta.ID, &meta.Label, &locked, &metaJSON, &meta.CreatedAt, &meta.UpdatedAt)
	if err != nil {
		return nil
	}
	meta.Locked = locked != 0
	json.Unmarshal([]byte(metaJSON), &meta.Meta)
	return meta
}

func setSessionMeta(sessionID string, label *string, locked *bool, metaUpdate map[string]interface{}) *SessionMeta {
	existing := getSessionMeta(sessionID)

	if existing == nil {
		metaJSON := "{}"
		if metaUpdate != nil {
			b, _ := json.Marshal(metaUpdate)
			metaJSON = string(b)
		}
		labelVal := ""
		if label != nil {
			labelVal = *label
		}
		lockedVal := 0
		if locked != nil && *locked {
			lockedVal = 1
		}
		db.Exec("INSERT INTO session_meta (id, label, locked, active, meta) VALUES (?, ?, ?, 1, ?)",
			sessionID, labelVal, lockedVal, metaJSON)
	} else {
		if label != nil {
			db.Exec("UPDATE session_meta SET label = ?, updated_at = CURRENT_TIMESTAMP WHERE id = ?", *label, sessionID)
		}
		if locked != nil {
			lockedVal := 0
			if *locked {
				lockedVal = 1
			}
			db.Exec("UPDATE session_meta SET locked = ?, updated_at = CURRENT_TIMESTAMP WHERE id = ?", lockedVal, sessionID)
		}
		if metaUpdate != nil {
			existingMeta := existing.Meta
			if existingMeta == nil {
				existingMeta = make(map[string]interface{})
			}
			for k, v := range metaUpdate {
				existingMeta[k] = v
			}
			b, _ := json.Marshal(existingMeta)
			// Also set active=1 when updating meta (session is being started/recreated)
			db.Exec("UPDATE session_meta SET meta = ?, active = 1, updated_at = CURRENT_TIMESTAMP WHERE id = ?", string(b), sessionID)
		}
	}

	return getSessionMeta(sessionID)
}

// sessionShortUID extracts the random suffix from a session ID. Format is
// `pty_<unix-ts>_<random>` so the last underscore-segment is the short UID.
// Used to make auto-generated session names human-readable and stable.
func sessionShortUID(sessionID string) string {
	idx := strings.LastIndex(sessionID, "_")
	if idx < 0 || idx == len(sessionID)-1 {
		return ""
	}
	return sessionID[idx+1:]
}

// deriveAutoBase picks a stem for auto-generated session names. Prefers
// the project directory's basename (e.g. "av-photo" for
// "/lxd-exch/avito/av-photo") so agents scanning `ab sessions list` can
// tell sessions apart from the name alone. When the path is a root-ish
// placeholder ("/", ".", ""), falls back to the host's short name —
// otherwise every shell opened at the filesystem root would be an
// indistinguishable "root-XXXXX" blob in the list.
func deriveAutoBase(projectPath string) string {
	base := filepath.Base(projectPath)
	if base != "" && base != "." && base != "/" {
		return base
	}
	if hn, err := os.Hostname(); err == nil && hn != "" {
		return strings.SplitN(hn, ".", 2)[0]
	}
	return "shell"
}

// legacyGenericNameRe matches names an older code path assigned when the
// basename of a "/" project path was "" — literal "root", plus the
// "root-<digits>" shape a later collision-suffix pass produced. When we
// restore such a session and the current project_path has a real
// basename, we discard the legacy name so the auto-namer below re-derives
// from the path. This migrates existing sessions on the next daemon
// restart with zero manual rename effort. User-picked names that happen
// to include "root" as a substring (e.g. "root-fs") are unaffected —
// the regex anchors on the whole string.
var legacyGenericNameRe = regexp.MustCompile(`^root(-\d+)?$`)

// findAliveSessionByName returns the ID of the first alive session whose
// Name matches the argument, or "" if none. Caller already holds no lock —
// this acquires sessionsMu.RLock briefly.
func findAliveSessionByName(name string) string {
	if name == "" {
		return ""
	}
	sessionsMu.RLock()
	defer sessionsMu.RUnlock()
	for id, s := range sessions {
		if s.IsAlive() && s.Name == name {
			return id
		}
	}
	return ""
}

// resolvePtyTarget maps a user-provided identifier (either a `pty_<ts>_<rand>`
// ID or a session name) to a concrete session ID. Returns the matched session
// ID and whether a unique alive match was found. Used by CLI subcommands so
// `ab sessions write rt-scrapper-29335 …` works alongside `ab sessions write
// pty_1775647145_29335 …`.
func resolvePtyTarget(arg string) (string, bool) {
	if arg == "" {
		return "", false
	}
	sessionsMu.RLock()
	defer sessionsMu.RUnlock()
	// Exact ID match wins immediately — it's how the daemon indexes sessions.
	if _, ok := sessions[arg]; ok {
		return arg, true
	}
	// Otherwise scan for an alive session with the matching Name.
	var hits []string
	for id, s := range sessions {
		if s.IsAlive() && s.Name == arg {
			hits = append(hits, id)
		}
	}
	if len(hits) == 1 {
		return hits[0], true
	}
	return "", false
}

func expandPath(path string) string {
	if path == "~" || len(path) > 1 && path[:2] == "~/" {
		usr, _ := user.Current()
		if path == "~" {
			return usr.HomeDir
		}
		return filepath.Join(usr.HomeDir, path[2:])
	}
	return path
}

func createPtySession(projectPath string, rows, cols int, name, continueSession string, shellOnly bool, sessionID string, customCmd []string) (*Session, error) {
	projectPath = expandPath(projectPath)
	if info, err := os.Stat(projectPath); err != nil {
		return nil, fmt.Errorf("project path not found: %s", projectPath)
	} else if !info.IsDir() {
		return nil, fmt.Errorf("project path is not a directory: %s", projectPath)
	}

	if sessionID == "" {
		// Generate unique session ID: pty_<timestamp>_<random>
		sessionID = fmt.Sprintf("pty_%d_%d", time.Now().Unix(), time.Now().UnixNano()%100000)
	}

	// For shell sessions: pass only the bare minimum so bash --login builds
	// the full environment from /etc/profile + ~/.bashrc (identical to SSH).
	// For claude sessions: inherit daemon env (needs PATH to find claude binary).
	var cmd *exec.Cmd
	if len(customCmd) > 0 {
		cmd = exec.Command(customCmd[0], customCmd[1:]...)
		cmd.Env = nil // inherit nothing — let login shell build env
		shellOnly = true
	} else if shellOnly {
		cmd = exec.Command("bash", "--login", "-i")
		cmd.Env = nil // inherit nothing — let login shell build env
	} else {
		if continueSession != "" {
			cmd = exec.Command("claude", "--dangerously-skip-permissions", "--resume", continueSession)
		} else {
			cmd = exec.Command("claude", "--dangerously-skip-permissions")
		}
		cmd.Env = append(os.Environ(), "IS_SANDBOX=1")
	}

	cmd.Dir = projectPath

	// Shell sessions: bare minimum for bash --login to work
	if shellOnly || len(customCmd) > 0 {
		usr, _ := user.Current()
		cmd.Env = []string{
			"HOME=" + usr.HomeDir,
			"USER=" + usr.Username,
			"LOGNAME=" + usr.Username,
			"TERM=xterm-256color",
			"COLORTERM=truecolor",
			"FORCE_COLOR=1",
			"LANG=en_US.UTF-8",
			"LC_ALL=en_US.UTF-8",
		}
	} else {
		cmd.Env = append(cmd.Env,
			"TERM=xterm-256color",
			"COLORTERM=truecolor",
			"FORCE_COLOR=1",
			"LANG=en_US.UTF-8",
			"LC_ALL=en_US.UTF-8",
		)
	}

	// In-session API — the agent running inside the PTY can use these to
	// call /api/pty/* endpoints on 127.0.0.1 (or via the `ab-pty client` CLI).
	// Token is derived from the daemon JWT secret + session id (HMAC) and is
	// only valid while the session is alive.
	if tok := deriveSessionToken(sessionID); tok != "" {
		cmd.Env = append(cmd.Env,
			"AB_PTY_SESSION_ID="+sessionID,
			"AB_PTY_SESSION_TOKEN="+tok,
		)
	}
	// The in-session CLI builds its own URL — it needs the scheme, not just
	// the port, or it will speak plain HTTP to a TLS listener.
	if m := tlsMode(); m != TLSModeOff {
		cmd.Env = append(cmd.Env, tlsModeEnv+"="+m)
	}
	// Expose the daemon's listening port so the CLI default target is correct.
	if port := os.Getenv("AB_PTY_PORT"); port != "" {
		cmd.Env = append(cmd.Env, "AB_PTY_PORT="+port)
	}

	ptmx, err := pty.StartWithSize(cmd, &pty.Winsize{
		Rows: uint16(rows),
		Cols: uint16(cols),
	})
	if err != nil {
		log.Printf("Failed to start PTY (path=%s, cmd=%v): %v", projectPath, cmd.Args, err)
		return nil, fmt.Errorf("path=%s cmd=%v: %w", projectPath, cmd.Args, err)
	}

	// Resolve the session name. Priority:
	//   1. Explicit `-name` arg (user picked it on purpose)
	//   2. Auto-generated `<basename(projectPath)>-<short-uid>` (last 5 digits
	//      of sessionID's random part — gives a stable, human-readable handle
	//      that doesn't collide with sibling sessions in the same dir).
	// In both cases we enforce uniqueness among ALIVE sessions: a clash would
	// make CLI name-based resolution ambiguous. On clash we add the short-uid
	// suffix (auto path) or return an error (explicit path) — caller decides.
	autoBase := deriveAutoBase(projectPath)
	shortUID := sessionShortUID(sessionID)
	if name == "" {
		name = autoBase
		if shortUID != "" {
			name = autoBase + "-" + shortUID
		}
	}
	if existing := findAliveSessionByName(name); existing != "" && existing != sessionID {
		// Collision among alive sessions. Auto-resolved by appending short-uid
		// if not already present; explicit names that still collide get an
		// error so the caller can pick a different one.
		if shortUID != "" && !strings.HasSuffix(name, "-"+shortUID) {
			name = name + "-" + shortUID
		}
		if existing := findAliveSessionByName(name); existing != "" && existing != sessionID {
			return nil, fmt.Errorf("session name %q is already in use by %s", name, existing)
		}
	}

	session := &Session{
		ID:          sessionID,
		Name:        name,
		ProjectPath: projectPath,
		LastCwd:     projectPath,
		CreatedAt:   time.Now(),
		Alive:       true,
		ShellOnly:   shellOnly,
		Pty:         ptmx,
		Cmd:         cmd,
		Clients:     make(map[*SafeConn]bool),
		Scrollback:  make([]string, 0),
		LastRows:    rows,
		LastCols:    cols,
	}

	sessionsMu.Lock()
	sessions[sessionID] = session
	sessionsMu.Unlock()

	meta := map[string]interface{}{
		"last_cwd":     projectPath,
		"project_path": projectPath,
		"project_name": name,
		"shell_only":   shellOnly,
	}
	if continueSession != "" {
		meta["claude_session_id"] = continueSession
	}
	setSessionMeta(sessionID, nil, nil, meta)

	// Start reader goroutine
	go readPtyLoop(session)

	// Start cwd tracker goroutine
	go trackCwd(session)

	// Track running AI child process (claude/codex/aider) so we can re-launch
	// it after a daemon restart.
	go trackAICmd(session)

	// Start claude session tracker for non-shell sessions without explicit session ID
	if !shellOnly && continueSession == "" {
		go trackClaudeSession(session)
	}

	return session, nil
}

// remapClaudeToWrapper rewrites a `claude …` cmdline to the `claudes` wrapper
// and drops any `--dangerously-skip-permissions` flag (the wrapper adds it).
func remapClaudeToWrapper(cmdline string) string {
	parts := strings.Fields(cmdline)
	if len(parts) == 0 {
		return cmdline
	}
	// Replace the claude binary with the wrapper
	parts[0] = "claudes"
	// Drop --dangerously-skip-permissions (the wrapper always passes it)
	filtered := parts[:0]
	for _, a := range parts {
		if a == "--dangerously-skip-permissions" {
			continue
		}
		filtered = append(filtered, a)
	}
	return strings.Join(filtered, " ")
}

// trackAICmd periodically inspects child processes of the session's shell and
// records the command line of any running AI agent (claude/codex/aider/cursor)
// into session_meta.last_ai_cmd. On daemon restart, restoreSessions feeds this
// command back into the new shell so the agent resumes.
func trackAICmd(session *Session) {
	ticker := time.NewTicker(5 * time.Second)
	defer ticker.Stop()
	for {
		<-ticker.C
		if !session.IsAlive() {
			return
		}
		if session.Cmd == nil || session.Cmd.Process == nil {
			continue
		}

		procs := getChildProcesses(session.Cmd.Process.Pid)
		aiCmd := ""
		for _, p := range procs {
			switch p.Cmd {
			case "claude":
				// Raw `claude` refuses to run as root with --dangerously-skip-permissions.
				// Remap to the `claudes` wrapper (IS_SANDBOX=1 claude --dangerously-skip-permissions "$@"),
				// which handles both; strip the flag to avoid duplication.
				aiCmd = remapClaudeToWrapper(p.Args)
			case "codex", "aider", "cursor":
				aiCmd = p.Args
			case "node", "npm", "npx":
				if hasCodexLikeArgs(p.Args) {
					aiCmd = p.Args
				}
			}
			if aiCmd != "" {
				break
			}
		}

		existing := getSessionMeta(session.ID)
		var prev string
		if existing != nil && existing.Meta != nil {
			if s, ok := existing.Meta["last_ai_cmd"].(string); ok {
				prev = s
			}
		}

		if aiCmd != prev {
			setSessionMeta(session.ID, nil, nil, map[string]interface{}{
				"last_ai_cmd": aiCmd,
			})
		}
	}
}

// trackCwd periodically reads the current working directory of the PTY process
// and saves it to the database for restoration after daemon restart
func trackCwd(session *Session) {
	ticker := time.NewTicker(5 * time.Second)
	defer ticker.Stop()

	for session.IsAlive() {
		<-ticker.C
		if !session.IsAlive() || session.Cmd == nil || session.Cmd.Process == nil {
			return
		}

		// Read cwd from /proc/<pid>/cwd
		pid := session.Cmd.Process.Pid
		cwdLink := fmt.Sprintf("/proc/%d/cwd", pid)
		cwd, err := os.Readlink(cwdLink)
		if err != nil {
			continue
		}

		// Update if changed
		session.mu.Lock()
		if cwd != session.LastCwd {
			session.LastCwd = cwd
			session.mu.Unlock()

			// Save to database
			updateSessionCwd(session.ID, cwd)
		} else {
			session.mu.Unlock()
		}
	}
}

// updateSessionCwd updates only the last_cwd in session meta
func updateSessionCwd(sessionID, cwd string) {
	meta := getSessionMeta(sessionID)
	if meta == nil {
		return
	}
	if meta.Meta == nil {
		meta.Meta = make(map[string]interface{})
	}
	meta.Meta["last_cwd"] = cwd
	setSessionMeta(sessionID, nil, nil, meta.Meta)
}

// trackClaudeSession watches for new Claude session files and links them to the PTY
func trackClaudeSession(session *Session) {
	// Wait a bit for Claude to create session file
	time.Sleep(3 * time.Second)

	// Get project hash from project path
	projectPath := session.ProjectPath
	if projectPath == "" || projectPath == "~" {
		return
	}

	// Expand ~ to home directory
	if strings.HasPrefix(projectPath, "~") {
		usr, _ := user.Current()
		projectPath = filepath.Join(usr.HomeDir, projectPath[1:])
	}

	// Create hash from path (same as Claude does)
	projectHash := strings.ReplaceAll(projectPath, "/", "-")
	projectDir := filepath.Join(claudeProjectsDir, projectHash)

	// Check every 2 seconds for up to 30 seconds
	ticker := time.NewTicker(2 * time.Second)
	defer ticker.Stop()

	startTime := session.CreatedAt
	attempts := 0
	maxAttempts := 15

	for session.IsAlive() && attempts < maxAttempts {
		<-ticker.C
		attempts++

		if !session.IsAlive() {
			return
		}

		// Check if already has session ID
		meta := getSessionMeta(session.ID)
		if meta != nil && meta.Meta != nil {
			if _, ok := meta.Meta["claude_session_id"].(string); ok {
				return // Already linked
			}
		}

		// Look for .jsonl files newer than session start
		entries, err := os.ReadDir(projectDir)
		if err != nil {
			continue
		}

		var newestSession string
		var newestMtime time.Time

		for _, entry := range entries {
			if entry.IsDir() || !strings.HasSuffix(entry.Name(), ".jsonl") {
				continue
			}
			if strings.HasPrefix(entry.Name(), "agent-") {
				continue
			}

			filePath := filepath.Join(projectDir, entry.Name())
			info, err := os.Stat(filePath)
			if err != nil {
				continue
			}

			// File must be modified after PTY creation
			if info.ModTime().After(startTime) && info.ModTime().After(newestMtime) {
				// Verify it has content
				if info.Size() > 50 {
					newestSession = strings.TrimSuffix(entry.Name(), ".jsonl")
					newestMtime = info.ModTime()
				}
			}
		}

		if newestSession != "" {
			// Link the session
			if meta == nil {
				meta = &SessionMeta{Meta: make(map[string]interface{})}
			}
			if meta.Meta == nil {
				meta.Meta = make(map[string]interface{})
			}
			meta.Meta["claude_session_id"] = newestSession
			setSessionMeta(session.ID, nil, nil, meta.Meta)
			broadcastPtyState()
			return
		}
	}
}

func readPtyLoop(session *Session) {
	buf := make([]byte, 8192)
	for session.IsAlive() {
		n, err := session.Pty.Read(buf)
		if err != nil {
			if err != io.EOF {
				log.Printf("PTY read error: %v", err)
			}
			break
		}
		if n > 0 {
			text := string(buf[:n])

			session.mu.Lock()
			session.Scrollback = append(session.Scrollback, text)
			if cleaned := extractMeaningfulTerminalOutput(text); cleaned != "" && cleaned != session.LastOutputDigest {
				session.LastOutputAt = time.Now()
				session.LastOutputDigest = cleaned
			}
			if len(session.Scrollback) > maxScrollback {
				session.Scrollback = session.Scrollback[len(session.Scrollback)-maxScrollback:]
			}
			// Track bracketed-paste mode toggles from the foreground app.
			// Whichever marker appears LATER in this chunk wins; if only
			// one appears, that one wins. Used by the stdin handler to
			// decide whether to wrap pasted payloads in \x1b[200~/\x1b[201~.
			onIdx := strings.LastIndex(text, "\x1b[?2004h")
			offIdx := strings.LastIndex(text, "\x1b[?2004l")
			if onIdx > offIdx {
				session.BracketedPaste = true
			} else if offIdx > onIdx {
				session.BracketedPaste = false
			}
			session.mu.Unlock()

			broadcastToClients(session, map[string]interface{}{
				"type": "output",
				"data": text,
			})
		}
	}

	session.setAlive(false)
	deactivateSession(session.ID)
	broadcastToClients(session, map[string]interface{}{"type": "session_ended"})
	broadcastPtyState()
}

func broadcastToClients(session *Session, msg map[string]interface{}) {
	data, _ := json.Marshal(msg)

	// Copy clients to avoid holding lock during writes
	session.mu.RLock()
	clients := make([]*SafeConn, 0, len(session.Clients))
	for c := range session.Clients {
		clients = append(clients, c)
	}
	session.mu.RUnlock()

	// Write to each client (SafeConn handles its own locking)
	for _, c := range clients {
		c.WriteMessage(websocket.TextMessage, data)
	}
}

func killSession(sessionID string) {
	sessionsMu.Lock()
	session, ok := sessions[sessionID]
	if !ok {
		sessionsMu.Unlock()
		return
	}
	delete(sessions, sessionID)
	sessionsMu.Unlock()

	session.setAlive(false)
	if session.Cmd != nil && session.Cmd.Process != nil {
		session.Cmd.Process.Kill()
		session.Cmd.Wait()
	}
	if session.Pty != nil {
		session.Pty.Close()
	}

	// Mark as inactive in DB
	deactivateSession(sessionID)
	db.Exec("DELETE FROM board_items WHERE pty_id = ?", sessionID)
}

func deactivateSession(sessionID string) {
	db.Exec("UPDATE session_meta SET active = 0, updated_at = CURRENT_TIMESTAMP WHERE id = ?", sessionID)
}

// restoreSessions restores active PTY sessions after daemon restart
// Called only once at startup
func restoreSessions() {
	rows, err := db.Query("SELECT id, meta FROM session_meta WHERE active = 1")
	if err != nil {
		log.Printf("Failed to query active sessions: %v", err)
		return
	}
	defer rows.Close()

	restored := 0
	for rows.Next() {
		var id, metaStr string
		if err := rows.Scan(&id, &metaStr); err != nil {
			continue
		}

		// Skip if already in memory
		sessionsMu.RLock()
		_, exists := sessions[id]
		sessionsMu.RUnlock()
		if exists {
			continue
		}

		var meta map[string]interface{}
		if err := json.Unmarshal([]byte(metaStr), &meta); err != nil {
			continue
		}

		shellOnly := false
		if so, ok := meta["shell_only"].(bool); ok {
			shellOnly = so
		}

		lastCwd, _ := meta["last_cwd"].(string)
		projectPath, _ := meta["project_path"].(string)
		projectName, _ := meta["project_name"].(string)
		claudeSessionID, _ := meta["claude_session_id"].(string)

		// Determine start path
		startPath := lastCwd
		if startPath == "" {
			startPath = projectPath
		}
		if startPath == "" {
			startPath = "~"
		}

		// Legacy-name migration: pre-fix code set project_name = "root"
		// when basename of a "/" project_path was empty, and a later
		// collision-suffix pass turned that into "root-<digits>".
		// Both leave the session indistinguishable from siblings at the
		// same cwd. If the current project_path has a real basename, drop
		// the legacy name so createPtySession's auto-namer re-derives
		// from the path — one-shot rewrite on the first restore under
		// the new binary, persisted back into meta.project_name by the
		// setSessionMeta call in createPtySession.
		if projectName != "" && legacyGenericNameRe.MatchString(projectName) {
			if realBase := filepath.Base(projectPath); realBase != "" && realBase != "." && realBase != "/" {
				log.Printf("restore %s: migrating legacy name %q → derive from project_path %q", id, projectName, projectPath)
				projectName = ""
			}
		}

		// Restore session
		var (
			session *Session
			err     error
		)
		if shellOnly {
			// Bash: start in last_cwd
			session, err = createPtySession(startPath, 40, 120, projectName, "", true, id, nil)
		} else if claudeSessionID != "" {
			// Claude: continue session
			session, err = createPtySession(startPath, 40, 120, projectName, claudeSessionID, false, id, nil)
		} else {
			// No claude session to continue, mark as inactive
			deactivateSession(id)
			continue
		}

		if session != nil {
			restored++
			log.Printf("Restored session %s (shell=%v, path=%s)", id, shellOnly, startPath)

			// If an AI command (claude/codex/aider) was running in this session
			// before the restart, re-launch it by feeding the command into the
			// new shell's stdin. Only applies to shell sessions — claude-only
			// sessions are already resumed via --resume above.
			if shellOnly {
				if aiCmd, ok := meta["last_ai_cmd"].(string); ok && aiCmd != "" {
					go relaunchAICmd(session, aiCmd)
				}
			}
		} else if err != nil {
			log.Printf("Failed to restore session %s: %v", id, err)
		}
	}

	if restored > 0 {
		log.Printf("Restored %d sessions", restored)
	}
}

// relaunchAICmd writes an AI command into a freshly-restored shell session so
// the previously-running agent (claude/codex/…) starts back up. Waits briefly
// for the login shell to reach its prompt before writing.
func relaunchAICmd(session *Session, aiCmd string) {
	time.Sleep(2 * time.Second)
	if !session.IsAlive() || session.Pty == nil {
		return
	}
	if _, err := session.Pty.Write([]byte(aiCmd + "\n")); err != nil {
		log.Printf("Failed to relaunch AI cmd in %s: %v", session.ID, err)
		return
	}
	log.Printf("Re-launched AI cmd in %s: %s", session.ID, aiCmd)
}

// cleanupStaleBoardItems removes terminal board_items whose pty_id
// doesn't match any live session. Runs once at startup after restoreSessions.
func cleanupStaleBoardItems() {
	sessionsMu.RLock()
	liveIDs := make(map[string]bool, len(sessions))
	for id := range sessions {
		liveIDs[id] = true
	}
	sessionsMu.RUnlock()

	rows, err := db.Query(`SELECT id, pty_id FROM board_items WHERE type = 'terminal'`)
	if err != nil {
		return
	}
	defer rows.Close()

	var stale []string
	for rows.Next() {
		var id, ptyID string
		if err := rows.Scan(&id, &ptyID); err != nil {
			continue
		}
		// Remove if pty_id is empty or session doesn't exist
		if ptyID == "" || !liveIDs[ptyID] {
			stale = append(stale, id)
		}
	}

	for _, id := range stale {
		db.Exec(`DELETE FROM board_items WHERE id = ?`, id)
	}

	if len(stale) > 0 {
		log.Printf("Cleaned up %d stale board items", len(stale))
	}
}

func setWinsize(f *os.File, rows, cols int) {
	syscall.Syscall(syscall.SYS_IOCTL, f.Fd(), uintptr(syscall.TIOCSWINSZ),
		uintptr(unsafe.Pointer(&struct{ h, w, x, y uint16 }{uint16(rows), uint16(cols), 0, 0})))
}

func broadcastPtyState() {
	state := make([]map[string]interface{}, 0)

	sessionsMu.RLock()
	for _, s := range sessions {
		meta := getSessionMeta(s.ID)
		locked := false
		label := ""
		claudeSessionID := ""
		projectName := ""
		if meta != nil {
			locked = meta.Locked
			label = meta.Label
			if csid, ok := meta.Meta["claude_session_id"].(string); ok {
				claudeSessionID = csid
			}
			if pn, ok := meta.Meta["project_name"].(string); ok {
				projectName = pn
			}
		}

		sessionType := "claude"
		if s.ShellOnly {
			sessionType = "bash"
		}

		s.mu.RLock()
		clientCount := len(s.Clients)
		lastCwd := s.LastCwd
		s.mu.RUnlock()

		// Collect child processes if session is alive
		var processes []ProcessInfo
		if s.IsAlive() && s.Cmd != nil && s.Cmd.Process != nil {
			processes = getChildProcesses(s.Cmd.Process.Pid)
		}
		if processes == nil {
			processes = []ProcessInfo{}
		}

		hasClaude := false
		hasCodex := false
		for _, p := range processes {
			switch p.Cmd {
			case "claude":
				hasClaude = true
			case "codex":
				hasCodex = true
			case "node", "npm", "npx":
				if hasCodexLikeArgs(p.Args) {
					hasCodex = true
				}
			}
		}

		// Auto-clear stale hook-based AI status: if status says working but no known
		// AI process is found, the agent was likely interrupted.
		aiSt := getAiStatus(s.ID)
		if aiSt != "" && aiSt != "idle" {
			hasAI := false
			for _, p := range processes {
				switch p.Cmd {
				case "claude", "codex", "aider", "cursor":
					hasAI = true
				}
			}
			if !hasAI {
				// AI process gone — clear status
				aiStatusMu.Lock()
				delete(aiStatuses, s.ID)
				aiStatusMu.Unlock()
				aiSt = ""
			}
		}
		if aiSt == "" || (aiSt == "idle" && hasCodex && !hasClaude) {
			aiSt = getCodexHeuristicStatus(s, processes)
		}

		state = append(state, map[string]interface{}{
			"id":                s.ID,
			"name":              s.Name,
			"project_path":      s.ProjectPath,
			"last_cwd":          lastCwd,
			"project_name":      projectName,
			"created_at":        s.CreatedAt.Format(time.RFC3339),
			"clients":           clientCount,
			"alive":             s.IsAlive(),
			"type":              sessionType,
			"locked":            locked,
			"label":             label,
			"claude_session_id": claudeSessionID,
			"processes":         processes,
			"ai_status":         aiSt,
		})
	}
	sessionsMu.RUnlock()

	msg, _ := json.Marshal(map[string]interface{}{
		"type":     "pty_state",
		"sessions": state,
	})

	// Hand the frame to each subscriber's own write pump — never write from
	// here, or one stalled peer stops live state for every other client.
	fanoutStateFrame(msg)
}

// broadcastBoardItemsChanged notifies all /ws/pty-state subscribers that the
// daemon's board_items table mutated (upsert / delete / sync). Front debounces
// and re-fetches the list — payload-less so we don't have to enumerate diffs.
// This is what makes `ab notes create` from a peer agent appear live in the UI
// without a page reload.
func broadcastBoardItemsChanged() {
	msg, _ := json.Marshal(map[string]interface{}{"type": "board_items_changed"})
	fanoutStateFrame(msg)
}

// === Projects Indexer ===

func initProjectsIndexer() {
	usr, _ := user.Current()
	claudeProjectsDir = filepath.Join(usr.HomeDir, ".claude", "projects")

	// Check if directory exists
	if _, err := os.Stat(claudeProjectsDir); os.IsNotExist(err) {
		log.Printf("Claude projects dir not found: %s", claudeProjectsDir)
		return
	}

	// Initial scan
	log.Printf("Scanning Claude projects: %s", claudeProjectsDir)
	start := time.Now()
	scanAllProjects()
	log.Printf("Initial scan completed in %v", time.Since(start))

	// Start watcher
	go startProjectsWatcher()

	// Start cleanup scheduler
	go startCleanupScheduler()
}

func startCleanupScheduler() {
	intervalStr := os.Getenv("AB_PTY_CLEANUP_INTERVAL")
	interval := 60 // default 1 minute
	if intervalStr != "" {
		if v, err := strconv.Atoi(intervalStr); err == nil && v > 0 {
			interval = v
		}
	}

	ticker := time.NewTicker(time.Duration(interval) * time.Second)
	defer ticker.Stop()

	// Run cleanup immediately on start
	cleanupInvalidProjects()

	for range ticker.C {
		cleanupInvalidProjects()
	}
}

func cleanupInvalidProjects() {
	var sessionsDeleted, projectsDeleted int64

	// 1. Delete projects with invalid path (not starting with /)
	result, err := db.Exec(`DELETE FROM claude_sessions WHERE project_hash IN (SELECT hash FROM projects WHERE path NOT LIKE '/%')`)
	if err != nil {
		log.Printf("Cleanup sessions (invalid path) error: %v", err)
	} else {
		n, _ := result.RowsAffected()
		sessionsDeleted += n
	}

	result, err = db.Exec(`DELETE FROM projects WHERE path NOT LIKE '/%'`)
	if err != nil {
		log.Printf("Cleanup projects (invalid path) error: %v", err)
	} else {
		n, _ := result.RowsAffected()
		projectsDeleted += n
	}

	// 2. Delete projects whose folder no longer exists on disk
	rows, err := db.Query(`SELECT hash FROM projects`)
	if err != nil {
		log.Printf("Cleanup query error: %v", err)
		return
	}
	defer rows.Close()

	var toDelete []string
	for rows.Next() {
		var hash string
		if err := rows.Scan(&hash); err != nil {
			continue
		}
		projectDir := filepath.Join(claudeProjectsDir, hash)
		if _, err := os.Stat(projectDir); os.IsNotExist(err) {
			toDelete = append(toDelete, hash)
		}
	}

	for _, hash := range toDelete {
		db.Exec(`DELETE FROM claude_sessions WHERE project_hash = ?`, hash)
		result, err := db.Exec(`DELETE FROM projects WHERE hash = ?`, hash)
		if err == nil {
			n, _ := result.RowsAffected()
			projectsDeleted += n
			sessionsDeleted++ // approximate
		}
	}

	if projectsDeleted > 0 || sessionsDeleted > 0 {
		log.Printf("Cleanup: deleted %d projects, %d sessions", projectsDeleted, sessionsDeleted)
	}
}

func scanAllProjects() {
	entries, err := os.ReadDir(claudeProjectsDir)
	if err != nil {
		log.Printf("Failed to read projects dir: %v", err)
		return
	}

	// Get path mapping from history.jsonl
	pathMapping := getProjectPathsFromHistory()

	for _, entry := range entries {
		if !entry.IsDir() {
			continue
		}
		scanProject(entry.Name(), pathMapping)
	}
}

func getProjectPathsFromHistory() map[string]string {
	mapping := make(map[string]string)
	usr, _ := user.Current()
	historyPath := filepath.Join(usr.HomeDir, ".claude", "history.jsonl")

	file, err := os.Open(historyPath)
	if err != nil {
		return mapping
	}
	defer file.Close()

	scanner := bufio.NewScanner(file)
	// Increase buffer size for long lines
	buf := make([]byte, 0, 64*1024)
	scanner.Buffer(buf, 1024*1024)

	for scanner.Scan() {
		line := scanner.Text()
		// Quick check for project field
		if !strings.Contains(line, `"project"`) {
			continue
		}

		var entry map[string]interface{}
		if err := json.Unmarshal([]byte(line), &entry); err != nil {
			continue
		}

		path, ok := entry["project"].(string)
		if !ok || path == "" {
			continue
		}

		// Create hash from path (same as Claude does)
		hash := strings.ReplaceAll(path, "/", "-")
		mapping[hash] = path
	}

	return mapping
}

func scanProject(projectHash string, pathMapping map[string]string) {
	projectDir := filepath.Join(claudeProjectsDir, projectHash)

	entries, err := os.ReadDir(projectDir)
	if err != nil {
		return
	}

	var sessionCount int
	var latestMtime int64
	validSessions := make(map[string]bool)

	for _, entry := range entries {
		if entry.IsDir() || !strings.HasSuffix(entry.Name(), ".jsonl") {
			continue
		}
		if strings.HasPrefix(entry.Name(), "agent-") {
			continue
		}

		filePath := filepath.Join(projectDir, entry.Name())
		info, err := os.Stat(filePath)
		if err != nil {
			continue
		}

		// Skip small files
		if info.Size() < 50 {
			continue
		}

		// Count messages
		msgCount := countSessionMessages(filePath)
		if msgCount == 0 {
			continue
		}

		sessionID := strings.TrimSuffix(entry.Name(), ".jsonl")
		mtime := info.ModTime().Unix()

		if mtime > latestMtime {
			latestMtime = mtime
		}

		validSessions[sessionID] = true

		// Upsert session
		db.Exec(`
			INSERT INTO claude_sessions (id, project_hash, created, size, has_content, message_count)
			VALUES (?, ?, ?, ?, 1, ?)
			ON CONFLICT(id) DO UPDATE SET
				created = excluded.created,
				size = excluded.size,
				has_content = 1,
				message_count = excluded.message_count
		`, sessionID, projectHash, info.ModTime().Format(time.RFC3339), info.Size(), msgCount)

		sessionCount++
	}

	// Clean up sessions that no longer exist on disk
	rows, _ := db.Query("SELECT id FROM claude_sessions WHERE project_hash = ?", projectHash)
	if rows != nil {
		var toDelete []string
		for rows.Next() {
			var id string
			rows.Scan(&id)
			if !validSessions[id] {
				toDelete = append(toDelete, id)
			}
		}
		rows.Close()
		for _, id := range toDelete {
			db.Exec("DELETE FROM claude_sessions WHERE id = ?", id)
		}
	}

	if sessionCount == 0 {
		// Remove project if no valid sessions
		db.Exec("DELETE FROM projects WHERE hash = ?", projectHash)
		return
	}

	// Get project path
	projectPath := pathMapping[projectHash]
	if projectPath == "" {
		// Try to recover path from hash by replacing - with /
		projectPath = recoverPathFromHash(projectHash)
	}
	projectName := filepath.Base(projectPath)
	if projectName == "" || projectName == "." || projectName == "-" {
		projectName = projectHash
	}

	// Upsert project
	db.Exec(`
		INSERT INTO projects (hash, path, name, session_count, latest_mtime)
		VALUES (?, ?, ?, ?, ?)
		ON CONFLICT(hash) DO UPDATE SET
			path = excluded.path,
			name = excluded.name,
			session_count = excluded.session_count,
			latest_mtime = excluded.latest_mtime
	`, projectHash, projectPath, projectName, sessionCount, latestMtime)
}

// recoverPathFromHash tries to reconstruct the original path from a hash
// by replacing dashes with slashes and checking if the directory exists
func recoverPathFromHash(hash string) string {
	if hash == "" || hash[0] != '-' {
		return hash
	}

	// Remove leading dash and split by dash
	parts := strings.Split(hash[1:], "-")
	if len(parts) == 0 {
		return hash
	}

	// Try to find existing path by progressively joining parts
	// Start from the end and work backwards to find the longest existing path
	for i := len(parts); i >= 1; i-- {
		// Try joining first i parts as path
		testPath := "/" + strings.Join(parts[:i], "/")
		if info, err := os.Stat(testPath); err == nil && info.IsDir() {
			// Found existing directory, append remaining parts
			if i < len(parts) {
				testPath = testPath + "/" + strings.Join(parts[i:], "/")
			}
			// Verify full path or return what we have
			if _, err := os.Stat(testPath); err == nil {
				return testPath
			}
			// Return partial match with remaining as subdirs
			return "/" + strings.Join(parts[:i], "/") + "/" + strings.Join(parts[i:], "/")
		}
	}

	// Fallback: just convert all dashes to slashes
	return "/" + strings.Join(parts, "/")
}

func countSessionMessages(filePath string) int {
	file, err := os.Open(filePath)
	if err != nil {
		return 0
	}
	defer file.Close()

	count := 0
	scanner := bufio.NewScanner(file)
	buf := make([]byte, 0, 64*1024)
	scanner.Buffer(buf, 10*1024*1024) // 10MB buffer for large lines

	for scanner.Scan() {
		line := scanner.Text()

		// Quick pre-filter
		if !strings.Contains(line, `"type":"user"`) &&
			!strings.Contains(line, `"type":"assistant"`) {
			continue
		}

		// Parse JSON to check for actual content
		var entry map[string]interface{}
		if err := json.Unmarshal([]byte(line), &entry); err != nil {
			continue
		}

		msgType, _ := entry["type"].(string)
		if msgType != "user" && msgType != "assistant" {
			continue
		}

		// Check for non-empty content
		hasContent := false
		if msgType == "user" {
			if msg, ok := entry["message"].(map[string]interface{}); ok {
				if content, ok := msg["content"].(string); ok && content != "" {
					hasContent = true
				}
			}
		} else if msgType == "assistant" {
			if msg, ok := entry["message"].(map[string]interface{}); ok {
				if contentArr, ok := msg["content"].([]interface{}); ok {
					for _, c := range contentArr {
						if block, ok := c.(map[string]interface{}); ok {
							if block["type"] == "text" {
								if text, ok := block["text"].(string); ok && text != "" {
									hasContent = true
									break
								}
							}
						}
					}
				}
			}
		}

		if hasContent {
			count++
		}
	}
	return count
}

func startProjectsWatcher() {
	watcher, err := fsnotify.NewWatcher()
	if err != nil {
		log.Printf("Failed to create watcher: %v", err)
		return
	}
	defer watcher.Close()

	// Watch main projects dir
	err = watcher.Add(claudeProjectsDir)
	if err != nil {
		log.Printf("Failed to watch projects dir: %v", err)
		return
	}

	// Watch each project subdirectory
	entries, _ := os.ReadDir(claudeProjectsDir)
	for _, entry := range entries {
		if entry.IsDir() {
			subDir := filepath.Join(claudeProjectsDir, entry.Name())
			watcher.Add(subDir)
		}
	}

	log.Printf("Started watching: %s", claudeProjectsDir)

	pathMapping := getProjectPathsFromHistory()
	debounceTimer := make(map[string]*time.Timer)
	debounceMu := sync.Mutex{}

	for {
		select {
		case event, ok := <-watcher.Events:
			if !ok {
				return
			}

			// Debounce rapid events for same file
			debounceMu.Lock()
			if timer, exists := debounceTimer[event.Name]; exists {
				timer.Stop()
			}
			debounceTimer[event.Name] = time.AfterFunc(100*time.Millisecond, func() {
				handleFileEvent(event, pathMapping, watcher)
				debounceMu.Lock()
				delete(debounceTimer, event.Name)
				debounceMu.Unlock()
			})
			debounceMu.Unlock()

		case err, ok := <-watcher.Errors:
			if !ok {
				return
			}
			log.Printf("Watcher error: %v", err)
		}
	}
}

func handleFileEvent(event fsnotify.Event, pathMapping map[string]string, watcher *fsnotify.Watcher) {
	// Check if it's a project directory or session file
	relPath, _ := filepath.Rel(claudeProjectsDir, event.Name)
	parts := strings.Split(relPath, string(filepath.Separator))

	if len(parts) == 1 && event.Has(fsnotify.Create) {
		// New project directory
		if info, err := os.Stat(event.Name); err == nil && info.IsDir() {
			watcher.Add(event.Name)
			scanProject(parts[0], pathMapping)
		}
	} else if len(parts) >= 1 {
		// Session file changed
		projectHash := parts[0]
		scanProject(projectHash, pathMapping)
	}
}

func getProjectsFromDB() []Project {
	rows, err := db.Query(`
		SELECT hash, path, name, session_count, latest_mtime
		FROM projects
		ORDER BY latest_mtime DESC
	`)
	if err != nil {
		return nil
	}
	defer rows.Close()

	var projects []Project
	for rows.Next() {
		var p Project
		rows.Scan(&p.Hash, &p.Path, &p.Name, &p.SessionCount, &p.LatestMtime)
		projects = append(projects, p)
	}
	return projects
}

func getSessionsFromDB(projectHash string) []ClaudeSession {
	rows, err := db.Query(`
		SELECT id, project_hash, created, size, has_content, COALESCE(message_count, 0)
		FROM claude_sessions
		WHERE project_hash = ?
		ORDER BY created DESC
	`, projectHash)
	if err != nil {
		return nil
	}
	defer rows.Close()

	var sessions []ClaudeSession
	for rows.Next() {
		var s ClaudeSession
		var hasContent int
		rows.Scan(&s.ID, &s.ProjectHash, &s.Created, &s.Size, &hasContent, &s.MessageCount)
		s.HasContent = hasContent != 0
		sessions = append(sessions, s)
	}
	return sessions
}

// HTTP Handlers

func handleListProjects(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	w.Header().Set("Cache-Control", "no-store")
	w.Header().Set("Access-Control-Allow-Origin", "*")

	projects := getProjectsFromDB()
	if projects == nil {
		projects = []Project{}
	}

	// Add live PTY info
	sessionsMu.RLock()
	ptyByPath := make(map[string][]string)
	for _, s := range sessions {
		if s.IsAlive() {
			ptyByPath[s.ProjectPath] = append(ptyByPath[s.ProjectPath], s.ID)
		}
	}
	sessionsMu.RUnlock()

	result := make([]map[string]interface{}, 0, len(projects))
	for _, p := range projects {
		result = append(result, map[string]interface{}{
			"hash":          p.Hash,
			"path":          p.Path,
			"name":          p.Name,
			"session_count": p.SessionCount,
			"latest_mtime":  p.LatestMtime,
			"live_ptys":     ptyByPath[p.Path],
		})
	}

	json.NewEncoder(w).Encode(result)
}

func handleProjectsAPI(w http.ResponseWriter, r *http.Request) {
	if allowOptions(w, r, "GET, POST, DELETE, OPTIONS") {
		return
	}

	// Parse: /api/projects/{hash}[/sessions]
	path := r.URL.Path[len("/api/projects/"):]
	parts := strings.Split(path, "/")

	projectHash := parts[0]

	if len(parts) >= 2 && parts[1] == "sessions" {
		// GET /api/projects/{hash}/sessions
		sessions := getSessionsFromDB(projectHash)
		if sessions == nil {
			sessions = []ClaudeSession{}
		}
		writeJSON(w, 0, sessions)
		return
	}

	// GET /api/projects/{hash}
	projects := getProjectsFromDB()
	for _, p := range projects {
		if p.Hash == projectHash {
			writeJSON(w, 0, p)
			return
		}
	}

	writeError(w, 404, "Project not found")
}

func handleSessionsAPI(w http.ResponseWriter, r *http.Request) {
	if allowOptions(w, r, "GET, DELETE, OPTIONS") {
		return
	}

	// Parse: /api/sessions/{hash}/{sessionId}[/content]
	path := r.URL.Path[len("/api/sessions/"):]
	parts := strings.Split(path, "/")

	if len(parts) < 2 {
		writeError(w, 404, "Not found")
		return
	}

	projectHash := parts[0]
	sessionID := parts[1]

	if r.Method == "DELETE" {
		// DELETE /api/sessions/{hash}/{sessionId}
		filePath := filepath.Join(claudeProjectsDir, projectHash, sessionID+".jsonl")
		if err := os.Remove(filePath); err != nil {
			if os.IsNotExist(err) {
				writeError(w, 404, "Session not found")
			} else {
				writeError(w, 500, err.Error())
			}
			return
		}
		db.Exec("DELETE FROM claude_sessions WHERE id = ? AND project_hash = ?", sessionID, projectHash)
		writeJSON(w, 0, map[string]interface{}{"ok": true})
		return
	}

	// GET /api/sessions/{hash}/{sessionId}/content
	if len(parts) < 3 || parts[2] != "content" {
		writeError(w, 404, "Not found")
		return
	}

	messages := readSessionContent(projectHash, sessionID)
	writeJSON(w, 0, map[string]interface{}{
		"messages": messages,
	})
}

func readSessionContent(projectHash, sessionID string) []map[string]interface{} {
	filePath := filepath.Join(claudeProjectsDir, projectHash, sessionID+".jsonl")

	file, err := os.Open(filePath)
	if err != nil {
		return nil
	}
	defer file.Close()

	var messages []map[string]interface{}
	scanner := bufio.NewScanner(file)
	buf := make([]byte, 0, 64*1024)
	scanner.Buffer(buf, 10*1024*1024) // 10MB buffer for large lines

	for scanner.Scan() {
		line := scanner.Text()

		var entry map[string]interface{}
		if err := json.Unmarshal([]byte(line), &entry); err != nil {
			continue
		}

		msgType, _ := entry["type"].(string)
		if msgType != "user" && msgType != "assistant" && msgType != "summary" {
			continue
		}

		// Extract content based on message type
		var content string
		if msgType == "user" {
			if msg, ok := entry["message"].(map[string]interface{}); ok {
				content, _ = msg["content"].(string)
			}
		} else if msgType == "assistant" {
			if msg, ok := entry["message"].(map[string]interface{}); ok {
				if contentArr, ok := msg["content"].([]interface{}); ok {
					for _, c := range contentArr {
						if block, ok := c.(map[string]interface{}); ok {
							if block["type"] == "text" {
								if text, ok := block["text"].(string); ok {
									if content != "" {
										content += "\n"
									}
									content += text
								}
							}
						}
					}
				}
			}
		} else if msgType == "summary" {
			content, _ = entry["summary"].(string)
		}

		if content != "" {
			messages = append(messages, map[string]interface{}{
				"type":    msgType,
				"content": content,
			})
		}
	}

	return messages
}

func setJSONHeaders(w http.ResponseWriter) {
	w.Header().Set("Content-Type", "application/json")
	w.Header().Set("Cache-Control", "no-store")
	w.Header().Set("Access-Control-Allow-Origin", "*")
}

func setJSONCORSMethods(w http.ResponseWriter, methods string) {
	setJSONHeaders(w)
	w.Header().Set("Access-Control-Allow-Methods", methods)
	w.Header().Set("Access-Control-Allow-Headers", "Content-Type, Authorization")
}

func writeJSON(w http.ResponseWriter, status int, v interface{}) {
	if status > 0 {
		w.WriteHeader(status)
	}
	json.NewEncoder(w).Encode(v)
}

func writeError(w http.ResponseWriter, status int, message string) {
	writeJSON(w, status, map[string]string{"error": message})
}

func allowOptions(w http.ResponseWriter, r *http.Request, methods string) bool {
	setJSONCORSMethods(w, methods)
	return r.Method == http.MethodOptions
}

func requireMethod(w http.ResponseWriter, r *http.Request, method string) bool {
	if r.Method != method {
		writeError(w, http.StatusMethodNotAllowed, "Method not allowed")
		return false
	}
	return true
}

func decodeJSONBody(w http.ResponseWriter, r *http.Request, dst interface{}) bool {
	if err := json.NewDecoder(r.Body).Decode(dst); err != nil {
		writeError(w, http.StatusBadRequest, "Invalid request body")
		return false
	}
	return true
}

func handleInfo(w http.ResponseWriter, r *http.Request) {
	setJSONHeaders(w)

	hostname, _ := os.Hostname()
	sessionsMu.RLock()
	sessionCount := len(sessions)
	sessionsMu.RUnlock()

	port := os.Getenv("AB_PTY_PORT")
	if port == "" {
		port = "8421"
	}

	// TLS state is deliberately public: the client needs to know which mode
	// the daemon is in *before* it can authenticate (in `optional` it has no
	// certificate yet), and a server certificate fingerprint is not a secret —
	// every peer already sees the whole certificate during the handshake.
	info := map[string]interface{}{
		"version":  Version,
		"hostname": hostname,
		"sessions": sessionCount,
		"port":     port,
		"tls_mode": tlsMode(),
	}
	if tlsServerFingerprint != "" {
		info["tls_server_fingerprint"] = tlsServerFingerprint
	}
	// Present only over TLS: tells the caller whether the certificate it just
	// presented is on the allow-list, which is how the app distinguishes
	// "enrolled" from "tolerated because the daemon is in optional mode".
	if r.TLS != nil {
		info["tls_client_authorized"] = false
		if name := tlsPeerName(r); name != "" {
			info["tls_client_authorized"] = true
			info["tls_client_name"] = name
		}
	}
	writeJSON(w, 0, info)
}

func handleHealth(w http.ResponseWriter, r *http.Request) {
	setJSONHeaders(w)

	sessionsMu.RLock()
	count := len(sessions)
	sessionsMu.RUnlock()

	writeJSON(w, 0, map[string]interface{}{
		"status":   "ok",
		"sessions": count,
	})
}

func classifyPtyCreateError(err error) string {
	if err == nil {
		return "pty_create_failed"
	}
	msg := strings.ToLower(err.Error())
	switch {
	case strings.Contains(msg, "project path not found"):
		return "project_path_not_found"
	case strings.Contains(msg, "project path is not a directory"):
		return "project_path_not_found"
	case strings.Contains(msg, "chdir"):
		return "project_path_not_found"
	case strings.Contains(msg, "claude") && strings.Contains(msg, "no such file or directory"):
		return "claude_binary_not_found"
	case strings.Contains(msg, "executable file not found"):
		return "claude_binary_not_found"
	default:
		return "pty_create_failed"
	}
}

func handleListPty(w http.ResponseWriter, r *http.Request) {
	if allowOptions(w, r, "GET, POST, OPTIONS") {
		return
	}

	// POST /api/pty - create new PTY session
	if r.Method == "POST" {
		var data map[string]interface{}
		if err := json.NewDecoder(r.Body).Decode(&data); err != nil {
			writeError(w, 400, "Invalid JSON")
			return
		}

		projectPath, _ := data["project_path"].(string)
		if projectPath == "" {
			projectPath = "~"
		}
		rows := int(getFloat(data, "rows", 40))
		cols := int(getFloat(data, "cols", 120))
		shellOnly, _ := data["shell_only"].(bool)
		name, _ := data["name"].(string)
		projectName, _ := data["project_name"].(string)
		continueSession, _ := data["continue_session"].(string)

		// Parse custom command if provided
		var customCmd []string
		if cmdRaw, ok := data["cmd"]; ok {
			switch v := cmdRaw.(type) {
			case string:
				if v != "" {
					customCmd = strings.Fields(v)
				}
			case []interface{}:
				for _, item := range v {
					if s, ok := item.(string); ok {
						customCmd = append(customCmd, s)
					}
				}
			}
		}

		session, err := createPtySession(projectPath, rows, cols, name, continueSession, shellOnly, "", customCmd)

		// Save project_name in meta if provided
		if session != nil && projectName != "" {
			setSessionMeta(session.ID, nil, nil, map[string]interface{}{"project_name": projectName})
		}
		if session == nil {
			details := "unknown create error"
			if err != nil {
				details = err.Error()
			}
			writeJSON(w, 500, map[string]interface{}{
				"error":      "Failed to create PTY session",
				"details":    details,
				"error_type": classifyPtyCreateError(err),
			})
			return
		}

		go broadcastPtyState()

		writeJSON(w, 0, map[string]interface{}{
			"ok":           true,
			"session_id":   session.ID,
			"name":         session.Name,
			"project_path": session.ProjectPath,
			"type":         map[bool]string{true: "bash", false: "claude"}[session.ShellOnly],
		})
		return
	}

	// GET /api/pty - list sessions
	result := make([]map[string]interface{}, 0)

	sessionsMu.RLock()
	for _, s := range sessions {
		meta := getSessionMeta(s.ID)
		locked := false
		label := ""
		metaData := map[string]interface{}{}
		if meta != nil {
			locked = meta.Locked
			label = meta.Label
			metaData = meta.Meta
		}

		sessionType := "claude"
		if s.ShellOnly {
			sessionType = "bash"
		}

		s.mu.RLock()
		clientCount := len(s.Clients)
		scrollbackSize := len(s.Scrollback)
		s.mu.RUnlock()

		result = append(result, map[string]interface{}{
			"id":              s.ID,
			"name":            s.Name,
			"project_path":    s.ProjectPath,
			"created_at":      s.CreatedAt.Format(time.RFC3339),
			"clients":         clientCount,
			"scrollback_size": scrollbackSize,
			"alive":           s.IsAlive(),
			"type":            sessionType,
			"locked":          locked,
			"label":           label,
			"meta":            metaData,
		})
	}
	sessionsMu.RUnlock()

	writeJSON(w, 0, result)
}

func handlePtyAPI(w http.ResponseWriter, r *http.Request) {
	if allowOptions(w, r, "GET, POST, DELETE, PATCH, OPTIONS") {
		return
	}

	// Parse path: /api/pty/{session_id}[/lock|/meta]
	path := r.URL.Path[len("/api/pty/"):]
	parts := filepath.SplitList(path)
	if len(parts) == 0 {
		parts = []string{path}
	}

	// Split by /
	var sessionID, action string
	if idx := len(path) - 1; idx > 0 {
		for i := len(path) - 1; i >= 0; i-- {
			if path[i] == '/' {
				sessionID = path[:i]
				action = path[i+1:]
				break
			}
		}
	}
	if sessionID == "" {
		sessionID = path
	}

	// Allow name-based addressing alongside the canonical pty_<ts>_<rand> id.
	// `ab sessions write rt-scrapper-29335 …` hits this endpoint with the name
	// in the path; resolve it to the underlying ID before routing the action.
	if resolved, ok := resolvePtyTarget(sessionID); ok {
		sessionID = resolved
	}

	switch {
	case action == "lock" && r.Method == "POST":
		locked := true
		setSessionMeta(sessionID, nil, &locked, nil)
		broadcastPtyState()
		writeJSON(w, 0, map[string]interface{}{"ok": true, "locked": true})

	case action == "lock" && r.Method == "DELETE":
		locked := false
		setSessionMeta(sessionID, nil, &locked, nil)
		broadcastPtyState()
		writeJSON(w, 0, map[string]interface{}{"ok": true, "locked": false})

	case action == "meta" && r.Method == "PATCH":
		var data map[string]interface{}
		json.NewDecoder(r.Body).Decode(&data)

		var label *string
		if l, ok := data["label"].(string); ok {
			label = &l
		}
		var metaUpdate map[string]interface{}
		if m, ok := data["meta"].(map[string]interface{}); ok {
			metaUpdate = m
		}

		// Optional rename via `name`. Canonical mutable identifier — must stay
		// unique among alive sessions so CLI name-based addressing is
		// unambiguous. The change touches both in-memory Session.Name (used by
		// list JSON) and the persisted meta.project_name (used by
		// restoreSessions after a daemon restart).
		if newName, ok := data["name"].(string); ok && newName != "" {
			if existing := findAliveSessionByName(newName); existing != "" && existing != sessionID {
				writeError(w, 409, fmt.Sprintf("session name %q is already in use by %s", newName, existing))
				return
			}
			sessionsMu.Lock()
			if s, ok := sessions[sessionID]; ok {
				s.Name = newName
			}
			sessionsMu.Unlock()
			if metaUpdate == nil {
				metaUpdate = map[string]interface{}{}
			}
			metaUpdate["project_name"] = newName
		}

		meta := setSessionMeta(sessionID, label, nil, metaUpdate)
		resp := map[string]interface{}{"ok": true, "label": meta.Label, "meta": meta.Meta}
		sessionsMu.RLock()
		if s, ok := sessions[sessionID]; ok {
			resp["name"] = s.Name
		}
		sessionsMu.RUnlock()
		writeJSON(w, 0, resp)

	case action == "stdin" && r.Method == "POST":
		// Write raw text into a session's PTY master. Used by the in-session
		// `ab-pty client sessions write` CLI to inject prompts into peer agents.
		sessionsMu.RLock()
		s, exists := sessions[sessionID]
		sessionsMu.RUnlock()
		if !exists {
			writeError(w, 404, "Session not found")
			return
		}
		if !s.IsAlive() {
			writeError(w, 409, "Session is not alive")
			return
		}
		var body struct {
			Text  string `json:"text"`
			Enter *bool  `json:"enter,omitempty"` // default true
		}
		if err := json.NewDecoder(r.Body).Decode(&body); err != nil {
			writeError(w, 400, "Invalid JSON body")
			return
		}
		payload := body.Text
		enter := true
		if body.Enter != nil {
			enter = *body.Enter
		}
		// Submit semantics. Two modes depending on whether the foreground
		// TUI has bracketed-paste mode on (tracked from the output stream
		// in readPtyLoop; Codex/Claude Code/modern shells turn it on).
		//
		//   bracketed=true  → wrap payload in \x1b[200~ ... \x1b[201~ so the
		//                     TUI treats the bytes as a single PASTE event,
		//                     then write the Enter OUTSIDE the markers as a
		//                     real keypress. Without the markers the TUI
		//                     bundles a `text\r` write together via its
		//                     paste-debounce heuristic and the \r becomes a
		//                     newline inside the input box (=hung input).
		//                     Observed in Codex 0.139+.
		//   bracketed=false → preserve old behaviour for plain shells (bash,
		//                     etc.): text bytes raw, brief pause, then \r.
		//                     Sending the CSI markers to a non-aware shell
		//                     would inject `[200~` / `[201~` literals.
		s.mu.RLock()
		bracketed := s.BracketedPaste
		s.mu.RUnlock()

		total := 0
		if payload != "" {
			var bytes []byte
			if bracketed {
				bytes = append(bytes, "\x1b[200~"...)
				bytes = append(bytes, payload...)
				bytes = append(bytes, "\x1b[201~"...)
			} else {
				bytes = []byte(payload)
			}
			n, err := s.Pty.Write(bytes)
			if err != nil {
				writeError(w, 500, fmt.Sprintf("Write failed: %v", err))
				return
			}
			total += n
		}
		if enter {
			// Brief pause so the TUI finishes processing the paste (or
			// debounces a raw-byte burst) before the standalone Enter.
			// 80ms covers Codex 0.139+; 30ms was too tight.
			delay := 30 * time.Millisecond
			if bracketed {
				delay = 80 * time.Millisecond
			}
			time.Sleep(delay)
			n, err := s.Pty.Write([]byte("\r"))
			if err != nil {
				writeError(w, 500, fmt.Sprintf("Enter-write failed: %v", err))
				return
			}
			total += n
		}
		writeJSON(w, 0, map[string]interface{}{"ok": true, "bytes": total, "bracketed_paste": bracketed})

	case action == "key" && r.Method == "POST":
		// Inject a special key press (Enter, Tab, Escape, Ctrl-C, arrow keys,
		// etc.) into a session's stdin. Maps symbolic names to the same byte
		// sequences a terminal emits when the physical key is pressed.
		sessionsMu.RLock()
		s, exists := sessions[sessionID]
		sessionsMu.RUnlock()
		if !exists {
			writeError(w, 404, "Session not found")
			return
		}
		if !s.IsAlive() {
			writeError(w, 409, "Session is not alive")
			return
		}
		var body struct {
			Key string `json:"key"`
		}
		if err := json.NewDecoder(r.Body).Decode(&body); err != nil {
			writeError(w, 400, "Invalid JSON body")
			return
		}
		var bytes []byte
		switch strings.ToLower(body.Key) {
		case "enter", "return", "cr":
			bytes = []byte("\r")
		case "lf", "newline":
			bytes = []byte("\n")
		case "crlf":
			bytes = []byte("\r\n")
		case "tab":
			bytes = []byte("\t")
		case "escape", "esc":
			bytes = []byte{0x1b}
		case "backspace", "bs":
			bytes = []byte{0x7f}
		case "space":
			bytes = []byte(" ")
		case "up":
			bytes = []byte("\x1b[A")
		case "down":
			bytes = []byte("\x1b[B")
		case "right":
			bytes = []byte("\x1b[C")
		case "left":
			bytes = []byte("\x1b[D")
		case "home":
			bytes = []byte("\x1b[H")
		case "end":
			bytes = []byte("\x1b[F")
		case "pageup", "pgup":
			bytes = []byte("\x1b[5~")
		case "pagedown", "pgdn":
			bytes = []byte("\x1b[6~")
		case "ctrl-c", "c-c":
			bytes = []byte{0x03}
		case "ctrl-d", "c-d":
			bytes = []byte{0x04}
		case "ctrl-z", "c-z":
			bytes = []byte{0x1a}
		case "ctrl-l", "c-l":
			bytes = []byte{0x0c}
		case "ctrl-u", "c-u":
			bytes = []byte{0x15}
		case "ctrl-w", "c-w":
			bytes = []byte{0x17}
		default:
			writeError(w, 400, fmt.Sprintf("Unknown key: %q (use enter, tab, esc, backspace, up, down, left, right, ctrl-c, ctrl-d, ctrl-z, ...)", body.Key))
			return
		}
		if _, err := s.Pty.Write(bytes); err != nil {
			writeError(w, 500, fmt.Sprintf("Write failed: %v", err))
			return
		}
		writeJSON(w, 0, map[string]interface{}{"ok": true, "key": body.Key, "bytes": len(bytes)})

	case action == "scrollback" && r.Method == "GET":
		// Return recent scrollback as plain text. Used by `ab-pty client sessions tail`.
		sessionsMu.RLock()
		s, exists := sessions[sessionID]
		sessionsMu.RUnlock()
		if !exists {
			writeError(w, 404, "Session not found")
			return
		}
		lines := 200
		if q := r.URL.Query().Get("lines"); q != "" {
			if n, err := strconv.Atoi(q); err == nil && n > 0 {
				lines = n
			}
		}
		s.mu.RLock()
		total := len(s.Scrollback)
		start := 0
		if total > lines {
			start = total - lines
		}
		slice := append([]string{}, s.Scrollback[start:]...)
		s.mu.RUnlock()
		writeJSON(w, 0, map[string]interface{}{
			"ok":    true,
			"lines": slice,
			"total": total,
		})

	case action == "" && r.Method == "DELETE":
		sessionsMu.RLock()
		_, exists := sessions[sessionID]
		sessionsMu.RUnlock()

		if !exists {
			writeError(w, 404, "Session not found")
			return
		}

		killSession(sessionID)
		go broadcastPtyState()
		writeJSON(w, 0, map[string]interface{}{"ok": true})

	default:
		writeError(w, 404, "Not found")
	}
}

func handleBoardItems(w http.ResponseWriter, r *http.Request) {
	if allowOptions(w, r, "GET, PUT, POST, DELETE, OPTIONS") {
		return
	}

	switch {
	case r.URL.Path == "/api/board/items":
		if !requireMethod(w, r, http.MethodGet) {
			return
		}
		items, err := listBoardItems()
		if err != nil {
			writeError(w, http.StatusInternalServerError, "Failed to list board items")
			return
		}
		writeJSON(w, 0, items)
		return

	case r.URL.Path == "/api/board/items/sync":
		if !requireMethod(w, r, http.MethodPost) {
			return
		}
		var payload struct {
			Items []BoardItemRecord `json:"items"`
		}
		if !decodeJSONBody(w, r, &payload) {
			return
		}
		if err := syncBoardItems(payload.Items); err != nil {
			writeError(w, http.StatusInternalServerError, "Failed to sync board items")
			return
		}
		go broadcastBoardItemsChanged()
		writeJSON(w, 0, map[string]interface{}{"ok": true, "count": len(payload.Items)})
		return
	}

	if !strings.HasPrefix(r.URL.Path, "/api/board/items/") {
		writeError(w, http.StatusNotFound, "Not found")
		return
	}

	itemID, err := url.PathUnescape(strings.TrimPrefix(r.URL.Path, "/api/board/items/"))
	if err != nil || itemID == "" {
		writeError(w, http.StatusBadRequest, "Invalid item id")
		return
	}

	switch r.Method {
	case http.MethodPut:
		var item BoardItemRecord
		if !decodeJSONBody(w, r, &item) {
			return
		}
		item.ID = itemID
		if err := upsertBoardItem(item); err != nil {
			writeError(w, http.StatusInternalServerError, "Failed to save board item")
			return
		}
		go broadcastBoardItemsChanged()
		writeJSON(w, 0, map[string]interface{}{"ok": true})
	case http.MethodDelete:
		deleted, err := deleteBoardItem(itemID)
		if err != nil {
			writeError(w, http.StatusInternalServerError, "Failed to delete board item")
			return
		}
		if !deleted {
			writeError(w, http.StatusNotFound, "Board item not found")
			return
		}
		go broadcastBoardItemsChanged()
		writeJSON(w, 0, map[string]interface{}{"ok": true})
	default:
		writeError(w, http.StatusMethodNotAllowed, "Method not allowed")
	}
}

func handleBoardLayouts(w http.ResponseWriter, r *http.Request) {
	if allowOptions(w, r, "GET, PUT, DELETE, OPTIONS") {
		return
	}

	if r.URL.Path == "/api/board/layouts" {
		if !requireMethod(w, r, http.MethodGet) {
			return
		}
		layouts, err := listBoardLayouts()
		if err != nil {
			writeError(w, http.StatusInternalServerError, "Failed to list board layouts")
			return
		}
		writeJSON(w, 0, layouts)
		return
	}

	if !strings.HasPrefix(r.URL.Path, "/api/board/layouts/") {
		writeError(w, http.StatusNotFound, "Not found")
		return
	}

	layoutName, err := url.PathUnescape(strings.TrimPrefix(r.URL.Path, "/api/board/layouts/"))
	if err != nil || strings.TrimSpace(layoutName) == "" {
		writeError(w, http.StatusBadRequest, "Invalid layout name")
		return
	}

	switch r.Method {
	case http.MethodGet:
		layout, err := getBoardLayout(layoutName)
		if err != nil {
			writeError(w, http.StatusInternalServerError, "Failed to load board layout")
			return
		}
		if layout == nil {
			writeError(w, http.StatusNotFound, "Layout not found")
			return
		}
		writeJSON(w, 0, layout)
	case http.MethodPut:
		var payload struct {
			Snapshot map[string]interface{} `json:"snapshot"`
		}
		if !decodeJSONBody(w, r, &payload) {
			return
		}
		if payload.Snapshot == nil {
			writeError(w, http.StatusBadRequest, "snapshot must be an object")
			return
		}
		savedAt, err := saveBoardLayout(layoutName, payload.Snapshot)
		if err != nil {
			writeError(w, http.StatusInternalServerError, "Failed to save board layout")
			return
		}
		writeJSON(w, 0, map[string]interface{}{"ok": true, "name": layoutName, "savedAt": savedAt})
	case http.MethodDelete:
		deleted, err := deleteBoardLayout(layoutName)
		if err != nil {
			writeError(w, http.StatusInternalServerError, "Failed to delete board layout")
			return
		}
		if !deleted {
			writeError(w, http.StatusNotFound, "Layout not found")
			return
		}
		writeJSON(w, 0, map[string]interface{}{"ok": true})
	default:
		writeError(w, http.StatusMethodNotAllowed, "Method not allowed")
	}
}

func handlePasteImage(w http.ResponseWriter, r *http.Request) {
	if allowOptions(w, r, "POST, OPTIONS") {
		return
	}

	if r.Method != "POST" {
		writeError(w, 405, "Method not allowed")
		return
	}

	var data struct {
		ImageData string `json:"image_data"` // base64-encoded image
		MimeType  string `json:"mime_type"`  // e.g., "image/png"
	}

	if err := json.NewDecoder(r.Body).Decode(&data); err != nil {
		writeError(w, 400, "Invalid JSON")
		return
	}

	if data.ImageData == "" {
		writeError(w, 400, "Missing image_data")
		return
	}

	// Decode base64
	imageBytes, err := base64.StdEncoding.DecodeString(data.ImageData)
	if err != nil {
		writeError(w, 400, "Invalid base64 data")
		return
	}

	// Determine file extension from mime type
	ext := "png"
	switch data.MimeType {
	case "image/jpeg", "image/jpg":
		ext = "jpg"
	case "image/gif":
		ext = "gif"
	case "image/webp":
		ext = "webp"
	case "image/bmp":
		ext = "bmp"
	}

	// Generate filename with timestamp
	filename := fmt.Sprintf("paste-%d.%s", time.Now().UnixNano(), ext)
	filepath := "/tmp/" + filename

	// Write file
	if err := os.WriteFile(filepath, imageBytes, 0644); err != nil {
		writeError(w, 500, "Failed to write file")
		return
	}

	writeJSON(w, 0, map[string]interface{}{
		"ok":   true,
		"path": filepath,
	})
}

func handlePtyState(w http.ResponseWriter, r *http.Request) {
	rawConn, err := upgrader.Upgrade(w, r, nil)
	if err != nil {
		return
	}
	conn := &SafeConn{conn: rawConn}

	// Each subscriber gets its own buffered queue and writer goroutine; this
	// goroutine only ever reads. See subscribers.go.
	sub := newStateSub(conn)
	registerStateSub(sub)
	defer sub.stop("client disconnected")

	// Server-side keepalive: without it a tunnel endpoint can hold this
	// subscription open long after the client behind it is gone.
	defer armLiveness(conn)()

	// Send initial state
	broadcastPtyState()

	for {
		_, msg, err := conn.ReadMessage()
		if err != nil {
			break
		}

		var data map[string]interface{}
		if json.Unmarshal(msg, &data) == nil {
			if data["type"] == "ping" {
				conn.WriteJSON(map[string]string{"type": "pong"})
			}
		}
	}
}

func handleWebSocket(w http.ResponseWriter, r *http.Request) {
	rawConn, err := upgrader.Upgrade(w, r, nil)
	if err != nil {
		return
	}
	conn := &SafeConn{conn: rawConn}
	defer conn.Close()

	// Server-side keepalive, same contract as /ws/pty-state: any inbound
	// frame (the client's own ping, terminal input, a pong) refreshes the
	// read deadline, so only a peer that has gone silent for four ping
	// periods is torn down.
	defer armLiveness(conn)()

	var session *Session
	var createErr error
	pendingScrollback := false

	// Read init message
	_, msg, err := conn.ReadMessage()
	if err != nil {
		return
	}

	var initData map[string]interface{}
	if err := json.Unmarshal(msg, &initData); err != nil {
		return
	}

	action, _ := initData["action"].(string)
	if action == "" {
		action = "new"
	}
	ptyID, _ := initData["pty_id"].(string)
	continueSession, _ := initData["continue_session"].(string)
	projectPath, _ := initData["project_path"].(string)
	if projectPath == "" {
		projectPath = "~"
	}
	rows := int(getFloat(initData, "rows", 40))
	cols := int(getFloat(initData, "cols", 120))

	switch action {
	case "recreate":
		if ptyID == "" {
			conn.WriteJSON(map[string]string{"type": "error", "message": "pty_id required"})
			return
		}

		sessionsMu.RLock()
		oldSession, exists := sessions[ptyID]
		sessionsMu.RUnlock()

		if !exists {
			conn.WriteJSON(map[string]string{"type": "error", "message": "PTY not found"})
			return
		}

		meta := getSessionMeta(ptyID)
		var claudeSessionID string
		var lastCwd string
		if meta != nil && meta.Meta != nil {
			claudeSessionID, _ = meta.Meta["claude_session_id"].(string)
			lastCwd, _ = meta.Meta["last_cwd"].(string)
		}
		// Use last_cwd if available, otherwise fall back to ProjectPath
		startPath := lastCwd
		if startPath == "" {
			startPath = oldSession.ProjectPath
		}
		oldName := oldSession.Name

		killSession(ptyID)
		session, createErr = createPtySession(startPath, rows, cols, oldName, claudeSessionID, false, ptyID, nil)
		pendingScrollback = false

	case "shadow":
		if ptyID == "" {
			conn.WriteJSON(map[string]string{"type": "error", "message": "pty_id required"})
			return
		}

		sessionsMu.RLock()
		oldSession, exists := sessions[ptyID]
		sessionsMu.RUnlock()

		if !exists {
			conn.WriteJSON(map[string]string{"type": "error", "message": "PTY not found"})
			return
		}

		meta := getSessionMeta(ptyID)
		var claudeSessionID string
		if meta != nil && meta.Meta != nil {
			claudeSessionID, _ = meta.Meta["claude_session_id"].(string)
		}

		session, createErr = createPtySession(oldSession.ProjectPath, rows, cols, oldSession.Name, claudeSessionID, false, "", nil)

	case "attach":
		if ptyID == "" {
			conn.WriteJSON(map[string]string{"type": "error", "message": "pty_id required"})
			return
		}

		sessionsMu.RLock()
		s, exists := sessions[ptyID]
		sessionsMu.RUnlock()

		if !exists {
			conn.WriteJSON(map[string]string{"type": "error", "message": "PTY session not found"})
			return
		}

		if !s.IsAlive() {
			conn.WriteJSON(map[string]string{"type": "error", "message": "PTY session is dead"})
			return
		}

		session = s

		if reqScroll, ok := initData["request_scrollback"].(bool); ok && reqScroll {
			session.mu.RLock()
			scrollback := strings.Join(session.Scrollback, "")
			session.mu.RUnlock()
			if scrollback != "" {
				conn.WriteJSON(map[string]interface{}{"type": "output", "data": scrollback})
			}
		} else {
			pendingScrollback = true
		}

	default:
		shellOnly, _ := initData["shell_only"].(bool)
		name, _ := initData["name"].(string)

		// Parse custom command if provided
		var customCmd []string
		if cmdRaw, ok := initData["cmd"]; ok {
			switch v := cmdRaw.(type) {
			case string:
				if v != "" {
					customCmd = strings.Fields(v)
				}
			case []interface{}:
				for _, item := range v {
					if s, ok := item.(string); ok {
						customCmd = append(customCmd, s)
					}
				}
			}
		}

		session, createErr = createPtySession(projectPath, rows, cols, name, continueSession, shellOnly, "", customCmd)
		go broadcastPtyState()
	}

	if session == nil {
		msg := "Failed to create session"
		if createErr != nil {
			msg = createErr.Error()
		}
		conn.WriteJSON(map[string]string{"type": "error", "message": msg})
		return
	}

	// Register client
	session.mu.Lock()
	session.Clients[conn] = true
	session.mu.Unlock()

	defer func() {
		session.mu.Lock()
		delete(session.Clients, conn)
		session.mu.Unlock()
	}()

	conn.WriteJSON(map[string]interface{}{
		"type":         "ready",
		"session_id":   session.ID,
		"name":         session.Name,
		"project_path": session.ProjectPath,
	})

	// Handle client messages
	for {
		_, msg, err := conn.ReadMessage()
		if err != nil {
			break
		}

		var data map[string]interface{}
		if err := json.Unmarshal(msg, &data); err != nil {
			continue
		}

		msgType, _ := data["type"].(string)

		switch msgType {
		case "ping":
			conn.WriteJSON(map[string]string{"type": "pong"})

		case "input":
			if !session.IsAlive() {
				conn.WriteJSON(map[string]string{"type": "session_ended"})
				return
			}
			input, _ := data["data"].(string)
			session.mu.Lock()
			session.LastInputAt = time.Now()
			session.LastOutputDigest = ""
			session.mu.Unlock()
			session.Pty.WriteString(input)
			go broadcastPtyState()

		case "resize":
			// Winsize lives on the Session and is written from whichever
			// websocket goroutine owns this terminal, while readers sit in
			// other goroutines (restore paths, tests). Take session.mu for
			// the read-compare-write so two clients resizing at once can't
			// interleave into a mismatched rows/cols pair.
			curRows, curCols := session.Winsize()
			newRows := int(getFloat(data, "rows", float64(curRows)))
			newCols := int(getFloat(data, "cols", float64(curCols)))

			if newRows != curRows || newCols != curCols {
				session.setWinsize(newRows, newCols)
				setWinsize(session.Pty, newRows, newCols)

				if !pendingScrollback {
					session.mu.RLock()
					scrollback := strings.Join(session.Scrollback, "")
					session.mu.RUnlock()
					if scrollback != "" {
						conn.WriteJSON(map[string]string{"type": "clear"})
						conn.WriteJSON(map[string]interface{}{"type": "output", "data": scrollback})
					}
				}
			}

			if pendingScrollback {
				pendingScrollback = false
				session.mu.RLock()
				scrollback := strings.Join(session.Scrollback, "")
				session.mu.RUnlock()
				if scrollback != "" {
					conn.WriteJSON(map[string]string{"type": "clear"})
					conn.WriteJSON(map[string]interface{}{"type": "output", "data": scrollback})
				}
			}
		}
	}
}

func getFloat(m map[string]interface{}, key string, def float64) float64 {
	if v, ok := m[key].(float64); ok {
		return v
	}
	return def
}

// FileInfo represents a file or directory
type FileInfo struct {
	Name    string `json:"name"`
	Path    string `json:"path"`
	IsDir   bool   `json:"is_dir"`
	Size    int64  `json:"size"`
	ModTime int64  `json:"mod_time"`
	Mode    string `json:"mode"`
}

// handleFS handles /api/fs endpoint for file system browsing and operations
func handleFS(w http.ResponseWriter, r *http.Request) {
	setJSONHeaders(w)

	switch r.Method {
	case "GET":
		handleFSGet(w, r)
	case "POST":
		handleFSCreate(w, r)
	case "PUT":
		handleFSWrite(w, r)
	case "DELETE":
		handleFSDelete(w, r)
	default:
		writeError(w, http.StatusMethodNotAllowed, "Method not allowed")
	}
}

func handleFSGet(w http.ResponseWriter, r *http.Request) {

	path := r.URL.Query().Get("path")
	if path == "" {
		path = "/"
	}

	// Expand ~ to home directory
	path = expandPath(path)

	// Clean path to prevent directory traversal
	path = filepath.Clean(path)

	info, err := os.Stat(path)
	if err != nil {
		writeError(w, http.StatusNotFound, "Path not found: "+path)
		return
	}

	if !info.IsDir() {
		// Check if content is requested
		if r.URL.Query().Get("content") == "true" {
			// Read and return file content
			data, err := os.ReadFile(path)
			if err != nil {
				writeError(w, http.StatusInternalServerError, "Cannot read file: "+err.Error())
				return
			}
			writeJSON(w, 0, map[string]interface{}{
				"path":    path,
				"name":    info.Name(),
				"content": string(data),
				"size":    info.Size(),
			})
			return
		}

		// Return single file info
		writeJSON(w, 0, map[string]interface{}{
			"path":   path,
			"parent": filepath.Dir(path),
			"files": []FileInfo{{
				Name:    info.Name(),
				Path:    path,
				IsDir:   false,
				Size:    info.Size(),
				ModTime: info.ModTime().Unix(),
				Mode:    info.Mode().String(),
			}},
		})
		return
	}

	// List directory contents
	entries, err := os.ReadDir(path)
	if err != nil {
		writeError(w, http.StatusInternalServerError, "Cannot read directory: "+err.Error())
		return
	}

	files := make([]FileInfo, 0, len(entries))
	for _, entry := range entries {
		info, err := entry.Info()
		if err != nil {
			continue
		}

		files = append(files, FileInfo{
			Name:    entry.Name(),
			Path:    filepath.Join(path, entry.Name()),
			IsDir:   entry.IsDir(),
			Size:    info.Size(),
			ModTime: info.ModTime().Unix(),
			Mode:    info.Mode().String(),
		})
	}

	// Sort: directories first, then by name
	sort.Slice(files, func(i, j int) bool {
		if files[i].IsDir != files[j].IsDir {
			return files[i].IsDir
		}
		return files[i].Name < files[j].Name
	})

	writeJSON(w, 0, map[string]interface{}{
		"path":   path,
		"parent": filepath.Dir(path),
		"files":  files,
	})
}

func handleFSCreate(w http.ResponseWriter, r *http.Request) {
	var req struct {
		Path   string `json:"path"`
		Action string `json:"action"` // "mkdir" or "touch"
		Name   string `json:"name"`
	}

	if !decodeJSONBody(w, r, &req) {
		return
	}

	basePath := expandPath(req.Path)
	basePath = filepath.Clean(basePath)
	targetPath := filepath.Join(basePath, req.Name)

	// Validate name
	if req.Name == "" || strings.Contains(req.Name, "/") || strings.Contains(req.Name, "..") {
		writeError(w, http.StatusBadRequest, "Invalid name")
		return
	}

	switch req.Action {
	case "mkdir":
		if err := os.Mkdir(targetPath, 0755); err != nil {
			writeError(w, http.StatusInternalServerError, err.Error())
			return
		}
	case "touch":
		file, err := os.Create(targetPath)
		if err != nil {
			writeError(w, http.StatusInternalServerError, err.Error())
			return
		}
		file.Close()
	default:
		writeError(w, http.StatusBadRequest, "Invalid action")
		return
	}

	writeJSON(w, 0, map[string]interface{}{
		"ok":   true,
		"path": targetPath,
	})
}

func handleMkdir(w http.ResponseWriter, r *http.Request) {
	setJSONHeaders(w)

	if !requireMethod(w, r, http.MethodPost) {
		return
	}

	var req struct {
		Path string `json:"path"`
	}

	if !decodeJSONBody(w, r, &req) {
		return
	}

	if req.Path == "" || strings.Contains(req.Path, "..") {
		writeError(w, http.StatusBadRequest, "Invalid path")
		return
	}

	targetPath := filepath.Clean(expandPath(req.Path))
	if err := os.MkdirAll(targetPath, 0755); err != nil {
		writeError(w, http.StatusInternalServerError, err.Error())
		return
	}

	writeJSON(w, 0, map[string]interface{}{
		"ok":   true,
		"path": targetPath,
	})
}

func handleFSWrite(w http.ResponseWriter, r *http.Request) {
	var req struct {
		Path    string `json:"path"`
		Content string `json:"content"`
	}

	if !decodeJSONBody(w, r, &req) {
		return
	}

	path := expandPath(req.Path)
	path = filepath.Clean(path)

	// Check if file exists
	info, err := os.Stat(path)
	if err != nil {
		writeError(w, http.StatusNotFound, "File not found")
		return
	}

	if info.IsDir() {
		writeError(w, http.StatusBadRequest, "Cannot write to directory")
		return
	}

	// Write file
	if err := os.WriteFile(path, []byte(req.Content), info.Mode()); err != nil {
		writeError(w, http.StatusInternalServerError, "Cannot write file: "+err.Error())
		return
	}

	writeJSON(w, 0, map[string]interface{}{
		"ok":   true,
		"path": path,
	})
}

func handleFSDelete(w http.ResponseWriter, r *http.Request) {
	path := r.URL.Query().Get("path")
	if path == "" {
		writeError(w, http.StatusBadRequest, "Path required")
		return
	}

	path = expandPath(path)
	path = filepath.Clean(path)

	// Safety check: don't allow deleting root or home
	usr, _ := user.Current()
	if path == "/" || path == usr.HomeDir || path == "/root" || path == "/home" {
		writeError(w, http.StatusForbidden, "Cannot delete protected path")
		return
	}

	info, err := os.Stat(path)
	if err != nil {
		writeError(w, http.StatusNotFound, "Path not found")
		return
	}

	if info.IsDir() {
		err = os.RemoveAll(path)
	} else {
		err = os.Remove(path)
	}

	if err != nil {
		writeError(w, http.StatusInternalServerError, err.Error())
		return
	}

	writeJSON(w, 0, map[string]interface{}{
		"ok": true,
	})
}

// handleFSDownload serves a file as binary download
func handleFSDownload(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodGet {
		setJSONHeaders(w)
		writeError(w, http.StatusMethodNotAllowed, "Method not allowed")
		return
	}

	path := r.URL.Query().Get("path")
	if path == "" {
		setJSONHeaders(w)
		writeError(w, http.StatusBadRequest, "Path required")
		return
	}

	path = expandPath(path)
	path = filepath.Clean(path)

	info, err := os.Stat(path)
	if err != nil {
		setJSONHeaders(w)
		writeError(w, http.StatusNotFound, "File not found")
		return
	}

	if info.IsDir() {
		setJSONHeaders(w)
		writeError(w, http.StatusBadRequest, "Cannot download directory")
		return
	}

	w.Header().Set("Content-Disposition", "attachment; filename=\""+filepath.Base(path)+"\"")
	w.Header().Set("Content-Type", "application/octet-stream")
	w.Header().Set("Access-Control-Allow-Origin", "*")
	http.ServeFile(w, r, path)
}

// handleFSUpload handles multipart file upload
func handleFSUpload(w http.ResponseWriter, r *http.Request) {
	setJSONHeaders(w)

	if !requireMethod(w, r, http.MethodPost) {
		return
	}

	// 100MB max
	r.ParseMultipartForm(100 << 20)

	destDir := r.FormValue("path")
	if destDir == "" {
		destDir = "/"
	}
	destDir = expandPath(destDir)
	destDir = filepath.Clean(destDir)

	info, err := os.Stat(destDir)
	if err != nil || !info.IsDir() {
		writeError(w, http.StatusBadRequest, "Destination directory not found")
		return
	}

	file, handler, err := r.FormFile("file")
	if err != nil {
		writeError(w, http.StatusBadRequest, "No file in request")
		return
	}
	defer file.Close()

	// Validate filename
	name := filepath.Base(handler.Filename)
	if name == "" || name == "." || name == ".." {
		writeError(w, http.StatusBadRequest, "Invalid filename")
		return
	}

	targetPath := filepath.Join(destDir, name)

	dst, err := os.Create(targetPath)
	if err != nil {
		writeError(w, http.StatusInternalServerError, "Cannot create file: "+err.Error())
		return
	}
	defer dst.Close()

	if _, err := io.Copy(dst, file); err != nil {
		writeError(w, http.StatusInternalServerError, "Cannot write file: "+err.Error())
		return
	}

	writeJSON(w, 0, map[string]interface{}{
		"ok":   true,
		"path": targetPath,
		"name": name,
	})
}

// === MCP Mode ===

func runMCPMode() {
	// Initialize DB for MCP mode
	initDB()

	// Read JSON-RPC from stdin, write to stdout
	scanner := bufio.NewScanner(os.Stdin)
	buf := make([]byte, 0, 64*1024)
	scanner.Buffer(buf, 1024*1024)

	for scanner.Scan() {
		line := scanner.Text()
		response := handleMCPRequest(line)
		if response != "" {
			fmt.Println(response)
		}
	}
}

func handleMCPRequest(line string) string {
	var req map[string]interface{}
	if err := json.Unmarshal([]byte(line), &req); err != nil {
		return mcpError(-1, -32700, "Parse error")
	}

	id, _ := req["id"]
	method, _ := req["method"].(string)

	switch method {
	case "initialize":
		return mcpResponse(id, map[string]interface{}{
			"protocolVersion": "2024-11-05",
			"capabilities": map[string]interface{}{
				"tools": map[string]interface{}{},
			},
			"serverInfo": map[string]interface{}{
				"name":    "ab-pty",
				"version": Version,
			},
		})

	case "notifications/initialized":
		return "" // No response for notifications

	case "tools/list":
		return mcpResponse(id, map[string]interface{}{
			"tools": []map[string]interface{}{},
		})

	case "tools/call":
		params, _ := req["params"].(map[string]interface{})
		toolName, _ := params["name"].(string)
		return mcpToolResult(id, "Unknown tool: "+toolName)

	default:
		return mcpError(id, -32601, "Method not found: "+method)
	}
}

func mcpResponse(id interface{}, result interface{}) string {
	resp := map[string]interface{}{
		"jsonrpc": "2.0",
		"id":      id,
		"result":  result,
	}
	data, _ := json.Marshal(resp)
	return string(data)
}

func mcpError(id interface{}, code int, message string) string {
	resp := map[string]interface{}{
		"jsonrpc": "2.0",
		"id":      id,
		"error": map[string]interface{}{
			"code":    code,
			"message": message,
		},
	}
	data, _ := json.Marshal(resp)
	return string(data)
}

func mcpToolResult(id interface{}, text string) string {
	return mcpResponse(id, map[string]interface{}{
		"content": []map[string]interface{}{
			{
				"type": "text",
				"text": text,
			},
		},
	})
}

// Skills installed into Claude Code and Codex (one dir per skill).
// A legacy concatenated Codex AGENTS.md is also written for older builds.
// The marker lets the
// daemon detect its own files and refresh them on upgrade without
// clobbering user edits. Each skill's source is `skills/<name>.md`
// embedded at build time; users can override per-skill by setting
// AB_PTY_SKILLS_DIR=/path/to/skills and dropping a same-named .md there.
const abSkillMarkerV1 = "generated-by=ab-pty"

//go:embed skills/ab.md
var defaultAbSkill string

// skillBundle is one entry in the install set. The slice is kept so adding a
// second skill later is a one-line change; with a single entry the legacy
// Codex AGENTS.md concat below collapses to a byte copy of the body.
type skillBundle struct {
	name     string // dir name under ~/.claude/skills and ~/.codex/skills
	embedded string // baked-in default content
}

// Previously also `ab-team-protocol`; merged into `ab` (2026-06-28) because
// the two skills always loaded together in practice and the parallel Codex
// AGENTS.md concat created a class of bugs where one half went missing on a
// host. Old `~/.claude/skills/ab-team-protocol/` and `~/.codex/skills/
// ab-team-protocol/` are cleaned up by removeRetiredSkills() below.
var installedSkills = []skillBundle{
	{name: "ab", embedded: defaultAbSkill},
}

// retiredSkills are skills we used to install but have since merged into
// another entry. ensureAbSkillInstalled() removes their on-disk traces (only
// the files we wrote, identified by abSkillMarkerV1) so dead skill dirs don't
// hang around on long-lived hosts.
var retiredSkills = []string{"ab-team-protocol"}

// loadSkillBody returns the body for a skill plus the source it came from
// (for logging). Precedence: ${AB_PTY_SKILLS_DIR}/<name>.md if set and the
// file is non-empty, else the embedded default. No hard-coded fallback
// paths — host customisation is opt-in via the env var.
func loadSkillBody(name, embedded string) (body string, source string) {
	if dir := strings.TrimSpace(os.Getenv("AB_PTY_SKILLS_DIR")); dir != "" {
		p := filepath.Join(dir, name+".md")
		if data, err := os.ReadFile(p); err == nil && len(data) > 0 {
			return string(data), p
		}
	}
	return embedded, "embedded"
}

func codexHomeDir(usrHome string) string {
	if dir := strings.TrimSpace(os.Getenv("CODEX_HOME")); dir != "" {
		return dir
	}
	return filepath.Join(usrHome, ".codex")
}

// ensureAbSkillInstalled writes every entry in `installedSkills` to disk:
//
//   - Claude: one directory per skill at ~/.claude/skills/<name>/SKILL.md.
//     Each skill has its own YAML `description:`, so Claude only loads what's
//     relevant to the user's request — no bloated single-trigger doc.
//   - Codex: one directory per skill at $CODEX_HOME/skills/<name>/SKILL.md
//     (or ~/.codex/skills when CODEX_HOME is unset). A legacy ~/.codex/AGENTS.md
//     is still written for older Codex builds.
//
// Per-file refresh logic: if the existing file carries our marker
// (`generated-by=ab-pty`), it's safe to overwrite on next daemon start.
// Files without the marker are user-edited and we leave them alone, so
// host-local customisation survives daemon upgrades.
func ensureAbSkillInstalled() {
	usr, err := user.Current()
	if err != nil || usr.HomeDir == "" {
		return
	}

	// Load each skill body once (env override or embedded fallback).
	type loaded struct {
		name, body, source string
	}
	loadedSkills := make([]loaded, 0, len(installedSkills))
	for _, s := range installedSkills {
		body, source := loadSkillBody(s.name, s.embedded)
		loadedSkills = append(loadedSkills, loaded{name: s.name, body: body, source: source})
	}

	writeIfOurs := func(path, content string) {
		if existing, err := os.ReadFile(path); err == nil {
			if !strings.Contains(string(existing), abSkillMarkerV1) {
				return // user-authored, leave alone
			}
		}
		if err := os.MkdirAll(filepath.Dir(path), 0755); err != nil {
			log.Printf("ab skill: failed to mkdir %s: %v", filepath.Dir(path), err)
			return
		}
		if err := os.WriteFile(path, []byte(content), 0644); err != nil {
			log.Printf("ab skill: failed to write %s: %v", path, err)
			return
		}
		log.Printf("Installed ab skill: %s", path)
	}

	// Claude: one skill dir per entry.
	for _, s := range loadedSkills {
		claudePath := filepath.Join(usr.HomeDir, ".claude", "skills", s.name, "SKILL.md")
		writeIfOurs(claudePath, s.body)
		log.Printf("ab skill %s source: %s", s.name, s.source)
	}

	// Codex: one skill dir per entry.
	codexHome := codexHomeDir(usr.HomeDir)
	for _, s := range loadedSkills {
		codexSkillPath := filepath.Join(codexHome, "skills", s.name, "SKILL.md")
		writeIfOurs(codexSkillPath, s.body)
	}

	// Legacy Codex: concatenate all skills into one AGENTS.md. With a single
	// entry this collapses to a byte copy of the body — no separator.
	parts := make([]string, 0, len(loadedSkills))
	for _, s := range loadedSkills {
		parts = append(parts, strings.TrimRight(s.body, "\n"))
	}
	codexBody := strings.Join(parts, "\n\n---\n\n") + "\n"
	codexPath := filepath.Join(codexHome, "AGENTS.md")
	writeIfOurs(codexPath, codexBody)

	// Clean up dirs of skills we no longer install (only ours — files
	// without the marker are user-authored and we leave them alone).
	removeIfOurs := func(path string) {
		data, err := os.ReadFile(path)
		if err != nil {
			return
		}
		if !strings.Contains(string(data), abSkillMarkerV1) {
			return
		}
		if err := os.Remove(path); err != nil {
			log.Printf("ab skill: failed to remove retired %s: %v", path, err)
			return
		}
		// Try to drop the (now empty) parent dir. Ignore error — non-empty dirs
		// stay, which is what we want for hand-edited siblings.
		os.Remove(filepath.Dir(path))
		log.Printf("Removed retired ab skill: %s", path)
	}
	for _, name := range retiredSkills {
		removeIfOurs(filepath.Join(usr.HomeDir, ".claude", "skills", name, "SKILL.md"))
		removeIfOurs(filepath.Join(codexHome, "skills", name, "SKILL.md"))
	}
}

// ensureMCPConfigured quietly ensures MCP is configured on startup
func ensureMCPConfigured() {
	usr, _ := user.Current()
	settingsPath := filepath.Join(usr.HomeDir, ".claude", "settings.json")

	execPath, err := os.Executable()
	if err != nil {
		return
	}
	execPath, _ = filepath.Abs(execPath)

	var settings map[string]interface{}
	data, err := os.ReadFile(settingsPath)
	if err == nil {
		json.Unmarshal(data, &settings)
	}
	if settings == nil {
		settings = make(map[string]interface{})
	}

	mcpServers, ok := settings["mcpServers"].(map[string]interface{})
	if !ok {
		mcpServers = make(map[string]interface{})
	}

	// Check if already configured correctly
	if existing, ok := mcpServers["ab-pty"].(map[string]interface{}); ok {
		if cmd, ok := existing["command"].(string); ok && cmd == execPath {
			return // Already configured
		}
	}

	// Configure
	mcpServers["ab-pty"] = map[string]interface{}{
		"type":    "stdio",
		"command": execPath,
		"args":    []string{"mcp"},
	}
	settings["mcpServers"] = mcpServers

	os.MkdirAll(filepath.Dir(settingsPath), 0755)
	output, _ := json.MarshalIndent(settings, "", "  ")
	if err := os.WriteFile(settingsPath, output, 0644); err == nil {
		log.Printf("MCP server configured in %s", settingsPath)
	}
}

// setupMCPConfig ensures MCP server is configured in Claude settings (verbose)
func setupMCPConfig() {
	usr, _ := user.Current()
	settingsPath := filepath.Join(usr.HomeDir, ".claude", "settings.json")

	// Get path to current executable
	execPath, err := os.Executable()
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error getting executable path: %v\n", err)
		os.Exit(1)
	}
	execPath, _ = filepath.Abs(execPath)

	// Read existing settings or create new
	var settings map[string]interface{}

	data, err := os.ReadFile(settingsPath)
	if err == nil {
		json.Unmarshal(data, &settings)
	}
	if settings == nil {
		settings = make(map[string]interface{})
	}

	// Ensure mcpServers exists
	mcpServers, ok := settings["mcpServers"].(map[string]interface{})
	if !ok {
		mcpServers = make(map[string]interface{})
	}

	// Check if ab-pty is already configured
	if existing, ok := mcpServers["ab-pty"].(map[string]interface{}); ok {
		// Check if path matches
		if args, ok := existing["args"].([]interface{}); ok && len(args) > 0 {
			if args[0] == "mcp" {
				if cmd, ok := existing["command"].(string); ok && cmd == execPath {
					fmt.Println("MCP server already configured correctly")
					return
				}
			}
		}
	}

	// Configure ab-pty MCP server
	mcpServers["ab-pty"] = map[string]interface{}{
		"type":    "stdio",
		"command": execPath,
		"args":    []string{"mcp"},
	}
	settings["mcpServers"] = mcpServers

	// Ensure directory exists
	os.MkdirAll(filepath.Dir(settingsPath), 0755)

	// Write settings
	output, err := json.MarshalIndent(settings, "", "  ")
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error marshaling settings: %v\n", err)
		os.Exit(1)
	}

	if err := os.WriteFile(settingsPath, output, 0644); err != nil {
		fmt.Fprintf(os.Stderr, "Error writing settings: %v\n", err)
		os.Exit(1)
	}

	fmt.Printf("MCP server configured in %s\n", settingsPath)
	fmt.Printf("Command: %s mcp\n", execPath)
}

// === AI Status Tracking (via Claude Code hooks) ===

// aiStatus tracks the current state of AI agents running in PTY sessions.
// Key: session_id from Claude Code hook, Value: status string
var (
	aiStatusMu sync.RWMutex
	aiStatuses = map[string]aiStatusEntry{}
)

type aiStatusEntry struct {
	Status    string // "working", "idle", "tool:Bash", "tool:Edit", etc.
	Tool      string // current tool name (if working)
	UpdatedAt time.Time
}

func getAiStatus(ptyID string) string {
	aiStatusMu.RLock()
	defer aiStatusMu.RUnlock()
	// Look up by ptyID directly, or scan for matching session
	if entry, ok := aiStatuses[ptyID]; ok {
		// Expire stale entries (>15s without update — agent likely interrupted)
		if time.Since(entry.UpdatedAt) > 15*time.Second {
			return ""
		}
		return entry.Status
	}
	return ""
}

func setAiStatus(ptyID, status, tool string) {
	aiStatusMu.Lock()
	aiStatuses[ptyID] = aiStatusEntry{
		Status:    status,
		Tool:      tool,
		UpdatedAt: time.Now(),
	}
	aiStatusMu.Unlock()
	go broadcastPtyState()
}

func hasCodexLikeArgs(args string) bool {
	return strings.Contains(args, "@openai/codex") || strings.Contains(args, "/codex/codex")
}

func extractMeaningfulTerminalOutput(text string) string {
	cleaned := ansiEscapePattern.ReplaceAllString(text, "")
	return strings.TrimSpace(cleaned)
}

func getCodexHeuristicStatus(session *Session, processes []ProcessInfo) string {
	hasCodex := false
	busyCmd := ""

	for _, p := range processes {
		switch p.Cmd {
		case "codex":
			hasCodex = true
		case "node", "npm", "npx":
			if hasCodexLikeArgs(p.Args) {
				hasCodex = true
			}
		default:
			if busyCmd == "" {
				busyCmd = p.Cmd
			}
		}
	}

	if !hasCodex {
		return ""
	}

	if busyCmd != "" {
		return "tool:" + busyCmd
	}

	session.mu.RLock()
	lastInputAt := session.LastInputAt
	lastOutputAt := session.LastOutputAt
	session.mu.RUnlock()

	now := time.Now()
	if !lastInputAt.IsZero() && now.Sub(lastInputAt) < 12*time.Second {
		return "working"
	}

	// Ignore startup/idle redraw noise unless it follows actual user input.
	if !lastInputAt.IsZero() &&
		lastOutputAt.After(lastInputAt) &&
		now.Sub(lastOutputAt) < 12*time.Second &&
		now.Sub(lastInputAt) < 2*time.Minute {
		return "working"
	}

	return "idle"
}

// findPtyIDByPid finds the PTY session ID that owns the given process (by walking up)
func findPtyIDByPid(pid int) string {
	sessionsMu.RLock()
	defer sessionsMu.RUnlock()
	for _, s := range sessions {
		if s.Cmd != nil && s.Cmd.Process != nil {
			if isDescendant(pid, s.Cmd.Process.Pid) {
				return s.ID
			}
		}
	}
	return ""
}

// isDescendant checks if childPid is a descendant of ancestorPid
func isDescendant(childPid, ancestorPid int) bool {
	pid := childPid
	for i := 0; i < 20; i++ {
		if pid == ancestorPid {
			return true
		}
		if pid <= 1 {
			return false
		}
		// Read parent PID from /proc/{pid}/stat
		data, err := os.ReadFile(fmt.Sprintf("/proc/%d/stat", pid))
		if err != nil {
			return false
		}
		// Format: pid (comm) state ppid ...
		// Find closing paren, then parse ppid
		s := string(data)
		closeIdx := strings.LastIndex(s, ")")
		if closeIdx < 0 || closeIdx+2 >= len(s) {
			return false
		}
		fields := strings.Fields(s[closeIdx+2:])
		if len(fields) < 2 {
			return false
		}
		ppid, err := strconv.Atoi(fields[1])
		if err != nil {
			return false
		}
		pid = ppid
	}
	return false
}

var (
	getPtyForClaudeSessionFn = getPtyForClaudeSession
	findPtyByPidAncestryFn   = findPtyByPidAncestry
	findPtyByClaudeProcessFn = findPtyByClaudeProcess
	findPtyIDByCwdFn         = findPtyIDByCwd
)

func resolvePtyForHook(sessionID, cwd string, callerPid int) (ptyID, matchMethod, remappedFrom string) {
	// Prefer caller PID over cache. Claude can reuse the same session_id from a
	// different PTY, so cache must not win when ancestry gives us a concrete owner.
	cachedPtyID := getPtyForClaudeSessionFn(sessionID)
	if callerPid > 0 {
		ptyID = findPtyByPidAncestryFn(callerPid)
		if ptyID != "" {
			matchMethod = "pid-ancestry"
			if cachedPtyID != "" && cachedPtyID != ptyID {
				remappedFrom = cachedPtyID
			}
			return ptyID, matchMethod, remappedFrom
		}
	}
	if cachedPtyID != "" {
		return cachedPtyID, "cache", ""
	}
	ptyID = findPtyByClaudeProcessFn(sessionID)
	if ptyID != "" {
		return ptyID, "process-scan", ""
	}
	if cwd != "" && cwd != "/" {
		ptyID = findPtyIDByCwdFn(cwd)
		if ptyID != "" {
			return ptyID, "cwd", ""
		}
	}
	return "", "", ""
}

// handleHook receives Claude Code hook POSTs and updates AI status
func handleHook(w http.ResponseWriter, r *http.Request) {
	if r.Method != http.MethodPost {
		http.Error(w, "POST only", http.StatusMethodNotAllowed)
		return
	}

	var body struct {
		HookEventName string `json:"hook_event_name"`
		ToolName      string `json:"tool_name"`
		SessionID     string `json:"session_id"`
		Cwd           string `json:"cwd"`
		CallerPid     int    `json:"caller_pid"`
	}
	if err := json.NewDecoder(r.Body).Decode(&body); err != nil {
		http.Error(w, "bad json", http.StatusBadRequest)
		return
	}

	log.Printf("[hook] event=%s tool=%s session=%s cwd=%s", body.HookEventName, body.ToolName, body.SessionID, body.Cwd)

	ptyID, matchMethod, remappedFrom := resolvePtyForHook(body.SessionID, body.Cwd, body.CallerPid)
	if ptyID == "" {
		log.Printf("[hook] no PTY found for session=%s cwd=%s caller_pid=%d", body.SessionID, body.Cwd, body.CallerPid)
		w.WriteHeader(http.StatusOK)
		return
	}
	if remappedFrom != "" {
		log.Printf("[hook] remapped session=%s from pty=%s to pty=%s via %s", body.SessionID, remappedFrom, ptyID, matchMethod)
	}
	log.Printf("[hook] matched pty=%s via %s", ptyID, matchMethod)
	// Cache the mapping for future calls
	setClaudeSessionMapping(body.SessionID, ptyID)

	switch body.HookEventName {
	case "UserPromptSubmit":
		setAiStatus(ptyID, "working", "")
	case "PreToolUse":
		setAiStatus(ptyID, "tool:"+body.ToolName, body.ToolName)
	case "PostToolUse", "PostToolUseFailure":
		setAiStatus(ptyID, "working", "")
	case "Stop":
		setAiStatus(ptyID, "idle", "")
	case "SessionStart":
		setAiStatus(ptyID, "working", "")
	case "SessionEnd":
		aiStatusMu.Lock()
		delete(aiStatuses, ptyID)
		aiStatusMu.Unlock()
		claudeSessionMapMu.Lock()
		delete(claudeSessionMap, body.SessionID)
		claudeSessionMapMu.Unlock()
		go broadcastPtyState()
	default:
		setAiStatus(ptyID, "working", "")
	}

	w.WriteHeader(http.StatusOK)
}

// ensureHooksConfigured merges hooks from claude-hooks.json into ~/.claude/settings.json
func ensureHooksConfigured() {
	settingsPath := filepath.Join(os.Getenv("HOME"), ".claude", "settings.json")

	// Try to find hooks file: next to binary (cwd), then /app/
	var hooksData []byte
	var err error
	for _, path := range []string{"claude-hooks.json", "/app/claude-hooks.json"} {
		hooksData, err = os.ReadFile(path)
		if err == nil {
			log.Printf("Hooks config loaded from %s", path)
			break
		}
	}
	if err != nil {
		return // No hooks file — nothing to do
	}

	var hooksConfig map[string]interface{}
	if err := json.Unmarshal(hooksData, &hooksConfig); err != nil {
		fmt.Fprintf(os.Stderr, "Error parsing hooks config: %v\n", err)
		return
	}

	hooks, ok := hooksConfig["hooks"]
	if !ok {
		return
	}

	var settings map[string]interface{}
	if data, err := os.ReadFile(settingsPath); err == nil {
		json.Unmarshal(data, &settings)
	}
	if settings == nil {
		settings = map[string]interface{}{}
	}

	settings["hooks"] = hooks

	output, err := json.MarshalIndent(settings, "", "  ")
	if err != nil {
		fmt.Fprintf(os.Stderr, "Error marshaling settings: %v\n", err)
		return
	}

	if err := os.WriteFile(settingsPath, output, 0644); err != nil {
		fmt.Fprintf(os.Stderr, "Error writing settings with hooks: %v\n", err)
		return
	}

	fmt.Printf("Hooks configured in %s\n", settingsPath)
}

// === Claude session → PTY session mapping ===
var (
	claudeSessionMapMu sync.RWMutex
	claudeSessionMap   = map[string]string{} // claude_session_id → pty_id
)

func getPtyForClaudeSession(claudeSessionID string) string {
	if claudeSessionID == "" {
		return ""
	}
	claudeSessionMapMu.RLock()
	defer claudeSessionMapMu.RUnlock()
	return claudeSessionMap[claudeSessionID]
}

func setClaudeSessionMapping(claudeSessionID, ptyID string) {
	if claudeSessionID == "" || ptyID == "" {
		return
	}
	claudeSessionMapMu.Lock()
	claudeSessionMap[claudeSessionID] = ptyID
	claudeSessionMapMu.Unlock()
}

// findPtyByPidAncestry walks up the process tree from pid to find which PTY session owns it
func findPtyByPidAncestry(pid int) string {
	sessionsMu.RLock()
	defer sessionsMu.RUnlock()
	for _, s := range sessions {
		if s.Cmd != nil && s.Cmd.Process != nil {
			if isDescendant(pid, s.Cmd.Process.Pid) {
				return s.ID
			}
		}
	}
	return ""
}

// findPtyByClaudeProcess finds PTY session by checking which PTY has a claude
// child process whose cmdline contains the given session ID.
// Only returns a match if the session ID is verified via /proc/pid/cmdline.
func findPtyByClaudeProcess(claudeSessionID string) string {
	if claudeSessionID == "" {
		return ""
	}
	sessionsMu.RLock()
	defer sessionsMu.RUnlock()

	var singleAIPty string
	aiCount := 0

	for _, s := range sessions {
		if !s.IsAlive() || s.Cmd == nil || s.Cmd.Process == nil {
			continue
		}
		pid := s.Cmd.Process.Pid
		procs := getChildProcesses(pid)
		for _, p := range procs {
			if p.Cmd == "claude" || p.Cmd == "codex" || p.Cmd == "aider" {
				aiCount++
				singleAIPty = s.ID
				// Verify session ID in cmdline
				cmdline, _ := os.ReadFile(fmt.Sprintf("/proc/%d/cmdline", p.Pid))
				if strings.Contains(string(cmdline), claudeSessionID) {
					return s.ID
				}
			}
		}
	}

	// If only one AI process exists across all PTYs, it must be the one
	if aiCount == 1 {
		return singleAIPty
	}
	return ""
}

// findPtyIDByCwd finds PTY session by matching cwd
func findPtyIDByCwd(cwd string) string {
	if cwd == "" {
		return ""
	}
	sessionsMu.RLock()
	defer sessionsMu.RUnlock()
	for _, s := range sessions {
		s.mu.RLock()
		lastCwd := s.LastCwd
		s.mu.RUnlock()
		if lastCwd == cwd {
			return s.ID
		}
		// Also check project path
		if s.ProjectPath == cwd {
			return s.ID
		}
	}
	// Fallback: check any session with matching meta
	for _, s := range sessions {
		meta := getSessionMeta(s.ID)
		if meta != nil {
			if lc, ok := meta.Meta["last_cwd"].(string); ok && lc == cwd {
				return s.ID
			}
		}
	}
	return ""
}

// === SSH tunnels (`tu` shell helper) =======================================
//
// Thin HTTP wrapper around the host-side `tu` script (see /lxd-exch/system/tu).
// The script forwards local ports to a fixed vultr host via `(auto)ssh -R`.
// Three verbs:
//   GET  /api/tunnels                — `tu ls`, parsed into JSON
//   POST /api/tunnels  {src,dst,detached?}
//                                    — `tu [-d] src:dst`, returns parsed list
//   DELETE /api/tunnels/{pid}        — `tu k <pid>`
//
// `tu` is host-only and not bundled with the daemon. If it's not on PATH or
// not at the canonical path, every endpoint returns 200 with `installed:false`
// so the UI can render a placeholder rather than treating it as an error.

const tuCanonicalPath = "/lxd-exch/system/tu"

// resolveTuPath returns the path to the `tu` script, or "" if not found.
// Order: $TU_PATH override → canonical path → $PATH lookup.
func resolveTuPath() string {
	if p := os.Getenv("TU_PATH"); p != "" {
		if _, err := os.Stat(p); err == nil {
			return p
		}
	}
	if _, err := os.Stat(tuCanonicalPath); err == nil {
		return tuCanonicalPath
	}
	if p, err := exec.LookPath("tu"); err == nil {
		return p
	}
	return ""
}

type tunnelEntry struct {
	PID     string `json:"pid"`
	SrcPort string `json:"src_port"` // local port (your machine)
	DstPort string `json:"dst_port"` // public port (vultr)
	URL     string `json:"url"`
	Status  string `json:"status"`
}

// parseTuLs parses the column output of `tu ls`:
//
//	PID      LOCAL        URL                                 STATUS
//	---      -----        ---                                 ------
//	12345    :3000        http://209.250.240.193:30001       running
//
// LOCAL = ":<src_port>"; URL ends in ":<dst_port>". Dashes/header are skipped.
func parseTuLs(out string) []tunnelEntry {
	rows := []tunnelEntry{}
	for _, line := range strings.Split(out, "\n") {
		fields := strings.Fields(line)
		if len(fields) < 4 {
			continue
		}
		// Skip header + separator rows.
		if fields[0] == "PID" || strings.HasPrefix(fields[0], "---") {
			continue
		}
		// PID must be numeric.
		if _, err := strconv.Atoi(fields[0]); err != nil {
			continue
		}
		src := strings.TrimPrefix(fields[1], ":")
		url := fields[2]
		status := fields[3]
		// Dst port = trailing :<num> in URL.
		dst := ""
		if i := strings.LastIndex(url, ":"); i >= 0 && i+1 < len(url) {
			dst = url[i+1:]
		}
		rows = append(rows, tunnelEntry{
			PID:     fields[0],
			SrcPort: src,
			DstPort: dst,
			URL:     url,
			Status:  status,
		})
	}
	return rows
}

// runTu executes `tu` with the given args and returns stdout + stderr combined.
// Caller is responsible for argument validation (we accept only known shapes).
func runTu(args ...string) (string, error) {
	tuPath := resolveTuPath()
	if tuPath == "" {
		return "", fmt.Errorf("tu not installed")
	}
	cmd := exec.Command(tuPath, args...)
	out, err := cmd.CombinedOutput()
	return string(out), err
}

func handleTunnels(w http.ResponseWriter, r *http.Request) {
	tuPath := resolveTuPath()

	switch r.Method {
	case http.MethodGet:
		if tuPath == "" {
			writeJSON(w, http.StatusOK, map[string]interface{}{
				"installed": false,
				"tunnels":   []tunnelEntry{},
				"message":   "tu not installed on this host",
			})
			return
		}
		out, err := runTu("ls")
		if err != nil && !strings.Contains(out, "No active tunnels") {
			writeError(w, http.StatusInternalServerError, fmt.Sprintf("tu ls failed: %v: %s", err, out))
			return
		}
		writeJSON(w, http.StatusOK, map[string]interface{}{
			"installed": true,
			"tunnels":   parseTuLs(out),
		})

	case http.MethodPost:
		if tuPath == "" {
			writeError(w, http.StatusServiceUnavailable, "tu not installed on this host")
			return
		}
		var body struct {
			SrcPort  string `json:"src_port"`
			DstPort  string `json:"dst_port"`
			Detached bool   `json:"detached"`
		}
		if err := json.NewDecoder(r.Body).Decode(&body); err != nil {
			writeError(w, http.StatusBadRequest, "invalid json")
			return
		}
		// Validate ports are positive integers, no shell metacharacters.
		if !isPortNumber(body.SrcPort) || !isPortNumber(body.DstPort) {
			writeError(w, http.StatusBadRequest, "src_port and dst_port must be positive integers")
			return
		}
		args := []string{}
		if body.Detached {
			args = append(args, "-d")
		}
		args = append(args, body.SrcPort+":"+body.DstPort)
		out, err := runTu(args...)
		if err != nil && !body.Detached {
			// Foreground mode never returns from `exec ssh` cleanly — but the
			// daemon should never invoke without -d (we'd block forever). If
			// the user posts without detached=true, force it on so the call
			// returns instead of hanging the connection.
			writeError(w, http.StatusInternalServerError, fmt.Sprintf("tu failed: %v: %s", err, out))
			return
		}
		// Re-list to return the canonical state (PID may have changed).
		listOut, _ := runTu("ls")
		writeJSON(w, http.StatusOK, map[string]interface{}{
			"installed":  true,
			"tunnels":    parseTuLs(listOut),
			"create_log": out,
		})

	case http.MethodDelete:
		if tuPath == "" {
			writeError(w, http.StatusServiceUnavailable, "tu not installed on this host")
			return
		}
		// Path: /api/tunnels/{pid}
		pid := strings.TrimPrefix(r.URL.Path, "/api/tunnels/")
		pid = strings.TrimSuffix(pid, "/")
		if pid == "" {
			writeError(w, http.StatusBadRequest, "pid required")
			return
		}
		// Allow numeric PID or literal '*' (kill-all). Nothing else.
		if pid != "*" {
			if _, err := strconv.Atoi(pid); err != nil {
				writeError(w, http.StatusBadRequest, "pid must be numeric or '*'")
				return
			}
		}
		out, err := runTu("k", pid)
		if err != nil && !strings.Contains(out, "Killing PID") {
			writeError(w, http.StatusInternalServerError, fmt.Sprintf("tu k %s failed: %v: %s", pid, err, out))
			return
		}
		listOut, _ := runTu("ls")
		writeJSON(w, http.StatusOK, map[string]interface{}{
			"installed": true,
			"tunnels":   parseTuLs(listOut),
			"kill_log":  out,
		})

	default:
		w.Header().Set("Allow", "GET, POST, DELETE")
		writeError(w, http.StatusMethodNotAllowed, "method not allowed")
	}
}

// isPortNumber returns true iff s is a base-10 unsigned int 1..65535.
func isPortNumber(s string) bool {
	n, err := strconv.Atoi(s)
	if err != nil || n <= 0 || n > 65535 {
		return false
	}
	return true
}
