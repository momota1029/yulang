#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
archive="${1:-}"

usage() {
  cat >&2 <<'EOF'
usage: scripts/release-install-smoke.sh <dist/yulang-<target>.tar.gz>

Runs the Unix installer and uninstaller against a local HTTP release directory.
EOF
}

if [[ -z "$archive" ]]; then
  usage
  exit 1
fi
if [[ "$archive" == *.zip ]]; then
  echo "release install smoke: install.sh does not install Windows zip archives" >&2
  exit 1
fi
if [[ ! -f "$archive" ]]; then
  echo "release install smoke: archive not found: $archive" >&2
  exit 1
fi

dist_dir="$(cd "$(dirname "$archive")" && pwd)"
archive_name="$(basename "$archive")"
timeout_duration="${YULANG_SMOKE_TIMEOUT:-30s}"

python_bin=""
if command -v python3 >/dev/null 2>&1; then
  python_bin="python3"
elif command -v python >/dev/null 2>&1; then
  python_bin="python"
else
  echo "release install smoke: python3 or python is required" >&2
  exit 1
fi

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | awk '{print $1}'
  else
    echo "release install smoke: sha256sum or shasum is required" >&2
    exit 1
  fi
}

copy_release_sidecar() {
  local name="$1"
  cp "$repo_root/scripts/$name" "$dist_dir/$name"
}

copy_release_sidecar install.sh
copy_release_sidecar install.ps1
copy_release_sidecar uninstall.sh
copy_release_sidecar uninstall.ps1

{
  for file in "$archive_name" install.sh install.ps1 uninstall.sh uninstall.ps1; do
    printf '%s  %s\n' "$(sha256_file "$dist_dir/$file")" "$file"
  done
} >"$dist_dir/SHA256SUMS"

tmp="$(mktemp -d)"
server_pid=""
cleanup() {
  if [[ -n "$server_pid" ]]; then
    kill "$server_pid" >/dev/null 2>&1 || true
    wait "$server_pid" >/dev/null 2>&1 || true
  fi
  rm -rf "$tmp"
}
trap cleanup EXIT INT TERM

port_file="$tmp/port"
"$python_bin" - "$dist_dir" "$port_file" <<'PY' &
import functools
import http.server
import pathlib
import socketserver
import sys

dist = pathlib.Path(sys.argv[1])
port_file = pathlib.Path(sys.argv[2])

class Handler(http.server.SimpleHTTPRequestHandler):
    def log_message(self, format, *args):
        pass

handler = functools.partial(Handler, directory=str(dist))

class Server(socketserver.TCPServer):
    allow_reuse_address = True

with Server(("127.0.0.1", 0), handler) as httpd:
    port_file.write_text(str(httpd.server_address[1]), encoding="utf-8")
    httpd.serve_forever()
PY
server_pid=$!

for _ in {1..100}; do
  [[ -s "$port_file" ]] && break
  sleep 0.05
done
if [[ ! -s "$port_file" ]]; then
  echo "release install smoke: local release server did not start" >&2
  exit 1
fi
base_url="http://127.0.0.1:$(cat "$port_file")"

run() {
  if command -v timeout >/dev/null 2>&1; then
    timeout "$timeout_duration" "$@"
  else
    "$@"
  fi
}

install_yulang() {
  install_log="$tmp/install.log"
  if ! run env \
    YULANG_RELEASE_BASE_URL="$base_url" \
    HOME="$HOME" \
    SHELL="$SHELL" \
    "$repo_root/scripts/install.sh" --version smoke --prefix "$prefix" >"$install_log" 2>&1; then
    cat "$install_log" >&2
    exit 1
  fi
  test -x "$prefix/bin/yulang"
  test -f "$prefix/lib/yulang-"*/std.yu
  assert_path_registered
}

assert_no_home_std() {
  if find "$HOME/.yulang/lib" -mindepth 1 -maxdepth 1 -name 'yulang-*' 2>/dev/null | grep -q .; then
    echo "release install smoke: runtime created std under HOME instead of install prefix" >&2
    find "$HOME/.yulang/lib" -mindepth 1 -maxdepth 2 -print >&2
    exit 1
  fi
}

assert_path_registered() {
  if ! grep -F "$prefix/bin" "$HOME/.profile" >/dev/null 2>&1; then
    echo "release install smoke: installer did not register $prefix/bin in PATH profile" >&2
    test -f "$HOME/.profile" && cat "$HOME/.profile" >&2
    exit 1
  fi
  if ! run env -i HOME="$HOME" PATH="/usr/bin:/bin" sh -lc ". \"\$HOME/.profile\"; command -v yulang" >/dev/null; then
    echo "release install smoke: yulang is not visible after loading installed PATH profile" >&2
    exit 1
  fi
}

assert_std_cache_seeded() {
  if ! find "$YULANG_CACHE_DIR/artifacts/compiled-unit" -type f -name '*.yucu' 2>/dev/null | grep -q .; then
    echo "release install smoke: installer did not seed std compiled-unit cache" >&2
    find "$YULANG_CACHE_DIR" -maxdepth 4 -type f -print 2>/dev/null >&2 || true
    exit 1
  fi
}

assert_path_removed() {
  if grep -F "$prefix/bin" "$HOME/.profile" >/dev/null 2>&1; then
    echo "release install smoke: uninstaller left $prefix/bin in PATH profile" >&2
    cat "$HOME/.profile" >&2
    exit 1
  fi
}

export HOME="$tmp/home"
export SHELL="/bin/sh"
export XDG_CACHE_HOME="$tmp/xdg-cache"
export YULANG_CACHE_DIR="$tmp/yulang-cache"
unset YULANG_STD
unset YULANG_LIB_DIR
mkdir -p "$HOME" "$XDG_CACHE_HOME" "$YULANG_CACHE_DIR"

prefix="$tmp/prefix"
main="$tmp/main.yu"
cat >"$main" <<'YULANG'
{
    my a = each 1..
    my b = each a<..
    my c = each b<..

    guard: a * a + b * b == c * c

    (a, b, c)
} .once.show
YULANG

install_yulang
assert_std_cache_seeded
run "$prefix/bin/yulang" check "$main" >/dev/null
run_output="$(run "$prefix/bin/yulang" run --print-roots "$main")"
case "$run_output" in
  *'"just (3, 4, 5)"'*) ;;
  *)
    echo "release install smoke: unexpected run output" >&2
    echo "$run_output" >&2
    exit 1
    ;;
esac
assert_no_home_std

server_timeout="${YULANG_SMOKE_SERVER_TIMEOUT:-2s}"
set +e
if command -v timeout >/dev/null 2>&1; then
  timeout "$server_timeout" "$prefix/bin/yulang" server >/dev/null 2>&1
  status=$?
else
  "$prefix/bin/yulang" server >/dev/null 2>&1 &
  yulang_server_pid=$!
  sleep 2
  kill "$yulang_server_pid" >/dev/null 2>&1
  wait "$yulang_server_pid" >/dev/null 2>&1
  status=124
fi
set -e
if [[ "$status" != "0" && "$status" != "124" ]]; then
  echo "release install smoke: yulang server failed to start, status $status" >&2
  exit 1
fi

touch "$prefix/sentinel"
mkdir -p "$YULANG_CACHE_DIR"
touch "$YULANG_CACHE_DIR/sentinel"
run "$repo_root/scripts/uninstall.sh" --prefix "$prefix" >/dev/null
test ! -e "$prefix/bin/yulang"
test -e "$prefix/sentinel"
test -e "$YULANG_CACHE_DIR/sentinel"
assert_path_removed
if find "$prefix/lib" -mindepth 1 -maxdepth 1 -name 'yulang-*' 2>/dev/null | grep -q .; then
  echo "release install smoke: default uninstall left versioned std roots" >&2
  exit 1
fi

install_yulang
mkdir -p "$YULANG_CACHE_DIR"
touch "$YULANG_CACHE_DIR/sentinel"
run "$repo_root/scripts/uninstall.sh" --prefix "$prefix" --purge-cache >/dev/null
test ! -e "$YULANG_CACHE_DIR"
assert_path_removed

install_yulang
touch "$prefix/sentinel"
run "$repo_root/scripts/uninstall.sh" --prefix "$prefix" --all >/dev/null
test ! -e "$prefix"
assert_path_removed

mkdir -p "$HOME"
touch "$HOME/sentinel"
set +e
"$repo_root/scripts/uninstall.sh" --prefix "$HOME/." --all >/dev/null 2>&1
unsafe_status=$?
set -e
if [[ "$unsafe_status" == "0" || ! -e "$HOME/sentinel" ]]; then
  echo "release install smoke: unsafe prefix was not rejected" >&2
  exit 1
fi

echo "release install smoke ok: $archive_name"
