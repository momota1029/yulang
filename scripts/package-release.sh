#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat >&2 <<'EOF'
usage: scripts/package-release.sh --version <version> --target <target> --binary <path> [--out <dir>]

Create a release archive containing:
  bin/yulang[.exe]
  lib/std/
  README.md
  README.ja.md
  LICENSE-APACHE
  LICENSE-MIT
  release-manifest.txt
EOF
}

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
version=""
target=""
binary=""
out_dir="$repo_root/dist"

while [[ $# -gt 0 ]]; do
  case "$1" in
    --version)
      version="${2:-}"
      shift 2
      ;;
    --version=*)
      version="${1#--version=}"
      shift
      ;;
    --target)
      target="${2:-}"
      shift 2
      ;;
    --target=*)
      target="${1#--target=}"
      shift
      ;;
    --binary)
      binary="${2:-}"
      shift 2
      ;;
    --binary=*)
      binary="${1#--binary=}"
      shift
      ;;
    --out)
      out_dir="${2:-}"
      shift 2
      ;;
    --out=*)
      out_dir="${1#--out=}"
      shift
      ;;
    -h | --help)
      usage
      exit 0
      ;;
    *)
      echo "package-release: unknown argument: $1" >&2
      usage
      exit 1
      ;;
  esac
done

if [[ -z "$version" || -z "$target" || -z "$binary" ]]; then
  usage
  exit 1
fi

if [[ ! -f "$binary" ]]; then
  echo "package-release: binary not found: $binary" >&2
  exit 1
fi

std_version="$(
  sed -n 's/^pub const YULANG_STDLIB_VERSION: &str = "\(.*\)";$/\1/p' \
    "$repo_root/crates/yulang/src/stdlib.rs"
)"
if [[ -z "$std_version" ]]; then
  echo "package-release: failed to read YULANG_STDLIB_VERSION" >&2
  exit 1
fi

package="yulang-${version}-${target}"
stage="$out_dir/$package"
archive_base="$out_dir/yulang-${target}"
bin_name="yulang"
archive="$archive_base.tar.gz"

if [[ "$target" == *windows* ]]; then
  bin_name="yulang.exe"
  archive="$archive_base.zip"
fi

rm -rf "$stage"
mkdir -p "$stage/bin" "$stage/lib" "$out_dir"
cp "$binary" "$stage/bin/$bin_name"
if [[ "$target" != *windows* ]]; then
  chmod 755 "$stage/bin/$bin_name"
fi

"$stage/bin/$bin_name" --std-root "$stage/lib" install std >/dev/null 2>&1

cp "$repo_root/README.md" "$stage/README.md"
cp "$repo_root/README.ja.md" "$stage/README.ja.md"
cp "$repo_root/LICENSE-APACHE" "$stage/LICENSE-APACHE"
cp "$repo_root/LICENSE-MIT" "$stage/LICENSE-MIT"

cat >"$stage/release-manifest.txt" <<EOF
name=yulang
version=$version
target=$target
stdlib=$std_version
EOF

rm -f "$archive"
if [[ "$target" == *windows* ]]; then
  if command -v zip >/dev/null 2>&1; then
    (cd "$out_dir" && zip -qr "$(basename "$archive")" "$package")
  elif command -v powershell.exe >/dev/null 2>&1 && command -v cygpath >/dev/null 2>&1; then
    stage_win="$(cygpath -w "$stage")"
    archive_win="$(cygpath -w "$archive")"
    powershell.exe -NoProfile -Command \
      "Compress-Archive -Path '$stage_win' -DestinationPath '$archive_win' -Force"
  else
    echo "package-release: zip or powershell.exe is required for Windows archives" >&2
    exit 1
  fi
else
  (cd "$out_dir" && tar -czf "$(basename "$archive")" "$package")
fi

echo "$archive"
