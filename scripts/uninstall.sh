#!/usr/bin/env sh
set -eu

prefix="${YULANG_INSTALL_DIR:-$HOME/.yulang}"
remove_all=0
purge_cache=0

usage() {
  cat >&2 <<'EOF'
usage: scripts/uninstall.sh [--prefix <dir>] [--all] [--purge-cache]

Environment:
  YULANG_INSTALL_DIR   Install prefix. Defaults to ~/.yulang.

By default this removes the release-managed binary and versioned std roots:
  <prefix>/bin/yulang
  <prefix>/lib/yulang-*

Options:
  --all          Remove the whole install prefix.
  --purge-cache  Also remove the user artifact cache.
EOF
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --prefix)
      prefix="${2:-}"
      shift 2
      ;;
    --prefix=*)
      prefix="${1#--prefix=}"
      shift
      ;;
    --all)
      remove_all=1
      shift
      ;;
    --purge-cache)
      purge_cache=1
      shift
      ;;
    -h | --help)
      usage
      exit 0
      ;;
    *)
      echo "uninstall.sh: unknown argument: $1" >&2
      usage
      exit 1
      ;;
  esac
done

if [ -z "$prefix" ]; then
  echo "uninstall.sh: empty prefix" >&2
  exit 1
fi

canonical_path() {
  path="$1"
  if [ -d "$path" ]; then
    (cd "$path" && pwd -P)
    return
  fi

  parent="$(dirname "$path")"
  base="$(basename "$path")"
  parent_canon="$(cd "$parent" 2>/dev/null && pwd -P)" || return 1
  if [ "$parent_canon" = "/" ]; then
    printf '/%s\n' "$base"
  else
    printf '%s/%s\n' "$parent_canon" "$base"
  fi
}

prefix_canon="$(canonical_path "$prefix" || printf '%s\n' "$prefix")"
home_canon="$(canonical_path "$HOME" || printf '%s\n' "$HOME")"
case "$prefix_canon" in
  / | "")
    echo "uninstall.sh: refusing to remove unsafe prefix: $prefix" >&2
    exit 1
    ;;
esac
if [ "$prefix_canon" = "$home_canon" ]; then
  echo "uninstall.sh: refusing to remove unsafe prefix: $prefix" >&2
  exit 1
fi

remove_path() {
  if [ -e "$1" ] || [ -L "$1" ]; then
    rm -rf "$1"
    echo "Removed $1"
  fi
}

cache_root() {
  if [ -n "${YULANG_CACHE_DIR:-}" ]; then
    printf '%s\n' "$YULANG_CACHE_DIR"
  elif [ -n "${XDG_CACHE_HOME:-}" ]; then
    printf '%s\n' "$XDG_CACHE_HOME/yulang"
  else
    printf '%s\n' "$HOME/.cache/yulang"
  fi
}

if [ "$remove_all" -eq 1 ]; then
  remove_path "$prefix"
else
  remove_path "$prefix/bin/yulang"
  remove_path "$prefix/bin/yulang.exe"
  remove_path "$prefix/bin/yulang-lsp"
  remove_path "$prefix/bin/yulang-lsp.exe"

  for std_root in "$prefix/lib"/yulang-*; do
    [ -e "$std_root" ] || [ -L "$std_root" ] || continue
    remove_path "$std_root"
  done

  rmdir "$prefix/bin" "$prefix/lib" "$prefix" 2>/dev/null || true
fi

if [ "$purge_cache" -eq 1 ]; then
  remove_path "$(cache_root)"
fi

echo "Uninstalled yulang from $prefix"
echo "Remove $prefix/bin from PATH if it was added there."
