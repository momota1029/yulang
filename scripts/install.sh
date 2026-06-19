#!/usr/bin/env sh
set -eu

repo="${YULANG_INSTALL_REPO:-momota1029/yulang}"
version="${YULANG_VERSION:-latest}"
prefix="${YULANG_INSTALL_DIR:-$HOME/.yulang}"

usage() {
  cat >&2 <<'EOF'
usage: scripts/install.sh [--version <tag|latest>] [--prefix <dir>] [--repo <owner/repo>]

Environment:
  YULANG_VERSION       Release tag to install. Defaults to latest full release.
  YULANG_INSTALL_DIR   Install prefix. Defaults to ~/.yulang.
  YULANG_INSTALL_REPO  GitHub repository. Defaults to momota1029/yulang.

Alpha releases are GitHub prereleases, so install them with:
  scripts/install.sh --version v0.1.0-alpha.1
EOF
}

while [ "$#" -gt 0 ]; do
  case "$1" in
    --version)
      version="${2:-}"
      shift 2
      ;;
    --version=*)
      version="${1#--version=}"
      shift
      ;;
    --prefix)
      prefix="${2:-}"
      shift 2
      ;;
    --prefix=*)
      prefix="${1#--prefix=}"
      shift
      ;;
    --repo)
      repo="${2:-}"
      shift 2
      ;;
    --repo=*)
      repo="${1#--repo=}"
      shift
      ;;
    -h | --help)
      usage
      exit 0
      ;;
    *)
      echo "install.sh: unknown argument: $1" >&2
      usage
      exit 1
      ;;
  esac
done

if [ -z "$version" ] || [ -z "$prefix" ] || [ -z "$repo" ]; then
  usage
  exit 1
fi

need() {
  if ! command -v "$1" >/dev/null 2>&1; then
    echo "install.sh: required command not found: $1" >&2
    exit 1
  fi
}

detect_target() {
  os="$(uname -s)"
  arch="$(uname -m)"
  case "$arch" in
    x86_64 | amd64) arch="x86_64" ;;
    arm64 | aarch64) arch="aarch64" ;;
    *)
      echo "install.sh: unsupported architecture: $arch" >&2
      exit 1
      ;;
  esac

  case "$os" in
    Linux) echo "${arch}-unknown-linux-gnu" ;;
    Darwin) echo "${arch}-apple-darwin" ;;
    *)
      echo "install.sh: unsupported OS: $os" >&2
      exit 1
      ;;
  esac
}

sha256_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  elif command -v shasum >/dev/null 2>&1; then
    shasum -a 256 "$1" | awk '{print $1}'
  else
    echo "install.sh: sha256sum or shasum is required" >&2
    exit 1
  fi
}

need curl
need tar
need awk

target="$(detect_target)"
archive="yulang-${target}.tar.gz"
if [ "$version" = "latest" ]; then
  base_url="https://github.com/${repo}/releases/latest/download"
else
  base_url="https://github.com/${repo}/releases/download/${version}"
fi

tmp="$(mktemp -d)"
cleanup() {
  rm -rf "$tmp"
}
trap cleanup EXIT INT TERM

archive_path="$tmp/$archive"
sums_path="$tmp/SHA256SUMS"

if ! curl -fsSL "$base_url/$archive" -o "$archive_path"; then
  echo "install.sh: failed to download $archive from $base_url" >&2
  if [ "$version" = "latest" ]; then
    echo "install.sh: GitHub latest ignores prereleases; pass --version for alpha tags" >&2
  fi
  exit 1
fi

if [ "${YULANG_SKIP_CHECKSUM:-0}" != "1" ]; then
  curl -fsSL "$base_url/SHA256SUMS" -o "$sums_path"
  expected="$(awk -v file="$archive" '$2 == file { print $1; exit }' "$sums_path")"
  if [ -z "$expected" ]; then
    echo "install.sh: checksum entry not found for $archive" >&2
    exit 1
  fi
  actual="$(sha256_file "$archive_path")"
  if [ "$actual" != "$expected" ]; then
    echo "install.sh: checksum mismatch for $archive" >&2
    echo "expected: $expected" >&2
    echo "actual:   $actual" >&2
    exit 1
  fi
fi

tar -xzf "$archive_path" -C "$tmp"
package_root="$(find "$tmp" -mindepth 1 -maxdepth 1 -type d -name 'yulang-*' | sort | head -n 1)"
if [ -z "$package_root" ]; then
  echo "install.sh: package root not found in archive" >&2
  exit 1
fi

bin_dir="$prefix/bin"
mkdir -p "$bin_dir"
cp "$package_root/bin/yulang" "$bin_dir/yulang"
chmod 755 "$bin_dir/yulang"

"$bin_dir/yulang" install std >/dev/null

echo "Installed yulang to $bin_dir/yulang"
echo "Add $bin_dir to PATH if it is not already there."
