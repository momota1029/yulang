#!/usr/bin/env sh
set -eu

repo="${YULANG_INSTALL_REPO:-momota1029/yulang}"
version="${YULANG_VERSION:-latest}"
prefix="${YULANG_INSTALL_DIR:-$HOME/.yulang}"
modify_path=1

usage() {
  cat >&2 <<'EOF'
usage: scripts/install.sh [--version <tag|latest>] [--prefix <dir>] [--repo <owner/repo>] [--no-modify-path]

Environment:
  YULANG_VERSION       Release tag to install. Defaults to latest full release.
  YULANG_INSTALL_DIR   Install prefix. Defaults to ~/.yulang.
  YULANG_INSTALL_REPO  GitHub repository. Defaults to momota1029/yulang.
  YULANG_RELEASE_BASE_URL
                       Override release download base URL, mainly for CI smoke.
  YULANG_NO_SEED_CACHE Set to 1 to skip install-time std cache seeding.
  YULANG_NO_MODIFY_PATH
                       Set to 1 to skip shell profile PATH edits.

Alpha releases are GitHub prereleases, so install them with:
  scripts/install.sh --version v0.1.0-alpha.6
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
    --no-modify-path)
      modify_path=0
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

canonical_install_prefix() {
  path="$1"
  if [ -d "$path" ]; then
    (cd "$path" && pwd -P)
    return
  fi

  parent="$(dirname "$path")"
  base="$(basename "$path")"
  mkdir -p "$parent"
  parent_canon="$(cd "$parent" && pwd -P)"
  if [ "$parent_canon" = "/" ]; then
    printf '/%s\n' "$base"
  else
    printf '%s/%s\n' "$parent_canon" "$base"
  fi
}

prefix="$(canonical_install_prefix "$prefix")"

need() {
  if ! command -v "$1" >/dev/null 2>&1; then
    echo "install.sh: required command not found: $1" >&2
    exit 1
  fi
}

path_contains() {
  case ":${PATH:-}:" in
    *":$1:"*) return 0 ;;
    *) return 1 ;;
  esac
}

escape_double_quoted_path() {
  printf '%s' "$1" | sed 's/\\/\\\\/g; s/"/\\"/g; s/\$/\\$/g; s/`/\\`/g'
}

remove_yulang_path_block() {
  profile="$1"
  [ -f "$profile" ] || return 0
  tmp_profile="$tmp/profile"
  awk '
    /^# >>> yulang path >>>$/ { skip = 1; next }
    /^# <<< yulang path <<<$/{ skip = 0; next }
    skip != 1 { print }
  ' "$profile" >"$tmp_profile"
  cat "$tmp_profile" >"$profile"
}

shell_profile_path() {
  shell_name="$(basename "${SHELL:-}")"
  case "$shell_name" in
    zsh) printf '%s\n' "$HOME/.zshrc" ;;
    bash) printf '%s\n' "$HOME/.bashrc" ;;
    *) printf '%s\n' "$HOME/.profile" ;;
  esac
}

install_path_entry() {
  if [ "${YULANG_NO_MODIFY_PATH:-0}" = "1" ] || [ "$modify_path" -eq 0 ]; then
    echo "Skipped PATH update for $bin_dir"
    echo "Add $bin_dir to PATH manually."
    return
  fi

  if path_contains "$bin_dir"; then
    echo "$bin_dir is already on PATH"
    return
  fi

  shell_name="$(basename "${SHELL:-}")"
  escaped_bin_dir="$(escape_double_quoted_path "$bin_dir")"
  if [ "$shell_name" = "fish" ]; then
    fish_dir="$HOME/.config/fish/conf.d"
    fish_profile="$fish_dir/yulang.fish"
    mkdir -p "$fish_dir"
    cat >"$fish_profile" <<EOF
# Added by yulang installer.
if not contains -- "$escaped_bin_dir" \$PATH
    set -gx PATH "$escaped_bin_dir" \$PATH
end
EOF
    echo "Added $bin_dir to PATH in $fish_profile"
    echo "Restart your shell to use yulang from PATH."
    return
  fi

  profile="$(shell_profile_path)"
  mkdir -p "$(dirname "$profile")"
  touch "$profile"
  remove_yulang_path_block "$profile"
  cat >>"$profile" <<EOF
# >>> yulang path >>>
# Added by yulang installer.
case ":\$PATH:" in
  *:"$escaped_bin_dir":*) ;;
  *) export PATH="$escaped_bin_dir:\$PATH" ;;
esac
# <<< yulang path <<<
EOF
  echo "Added $bin_dir to PATH in $profile"
  echo "Restart your shell to use yulang from PATH."
}

install_std() {
  std_install_log="$tmp/std-install.log"
  if ! YULANG_LIB_DIR="$lib_dir" "$bin_dir/yulang" install std > /dev/null 2>"$std_install_log"; then
    cat "$std_install_log" >&2
    exit 1
  fi
  std_root="$(sed -n '$p' "$std_install_log")"
  if [ -z "$std_root" ]; then
    echo "install.sh: failed to read installed std root" >&2
    exit 1
  fi
}

seed_std_cache() {
  if [ "${YULANG_NO_SEED_CACHE:-0}" = "1" ]; then
    return
  fi

  seed_source="$tmp/std-cache-seed.yu"
  printf '1\n' > "$seed_source"
  if ! YULANG_LIB_DIR="$lib_dir" "$bin_dir/yulang" --std-root "$std_root" run "$seed_source" >/dev/null 2>&1; then
    echo "install.sh: warning: failed to seed std cache" >&2
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
if [ -n "${YULANG_RELEASE_BASE_URL:-}" ]; then
  base_url="${YULANG_RELEASE_BASE_URL%/}"
elif [ "$version" = "latest" ]; then
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
lib_dir="$prefix/lib"
mkdir -p "$bin_dir"
cp "$package_root/bin/yulang" "$bin_dir/yulang"
chmod 755 "$bin_dir/yulang"

mkdir -p "$lib_dir"
install_std
seed_std_cache

echo "Installed yulang to $bin_dir/yulang"
install_path_entry
