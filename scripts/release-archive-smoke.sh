#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
archive="${1:-}"
archive_server_smoke="${YULANG_RELEASE_ARCHIVE_SMOKE_SERVER:-${YULANG_SMOKE_SERVER:-1}}"
archive_contract_smoke="${YULANG_RELEASE_ARCHIVE_SMOKE_CONTRACT:-1}"

if [[ -z "$archive" ]]; then
  echo "release archive smoke: archive path is required" >&2
  exit 1
fi

if [[ ! -f "$archive" ]]; then
  echo "release archive smoke: archive not found: $archive" >&2
  exit 1
fi

tmp="$(mktemp -d)"
cleanup() {
  rm -rf "$tmp"
}
trap cleanup EXIT

case "$archive" in
  *.tar.gz | *.tgz)
    tar -xzf "$archive" -C "$tmp"
    ;;
  *.zip)
    if command -v powershell.exe >/dev/null 2>&1 && command -v cygpath >/dev/null 2>&1; then
      archive_win="$(cygpath -w "$archive")"
      tmp_win="$(cygpath -w "$tmp")"
      powershell.exe -NoProfile -Command \
        "Expand-Archive -Path '$archive_win' -DestinationPath '$tmp_win' -Force"
    elif command -v unzip >/dev/null 2>&1; then
      set +e
      unzip -q "$archive" -d "$tmp"
      status=$?
      set -e
      if [[ "$status" -gt 1 ]]; then
        exit "$status"
      fi
    else
      tar -xf "$archive" -C "$tmp"
    fi
    ;;
  *)
    echo "release archive smoke: unsupported archive type: $archive" >&2
    exit 1
    ;;
esac

bin="$(
  find "$tmp" -type f \( -name yulang -o -name yulang.exe \) -path '*/bin/*' \
    | sort \
    | head -n 1
)"

if [[ -z "$bin" ]]; then
  echo "release archive smoke: yulang binary not found in archive" >&2
  find "$tmp" -maxdepth 3 -type f | sort >&2
  exit 1
fi

package_root="$(cd "$(dirname "$bin")/.." && pwd)"
if [[ ! -f "$package_root/lib/std.yu" ]]; then
  echo "release archive smoke: bundled std root not found: $package_root/lib/std.yu" >&2
  exit 1
fi

manifest="$package_root/release-manifest.txt"
if [[ ! -f "$manifest" ]]; then
  echo "release archive smoke: release-manifest.txt not found" >&2
  exit 1
fi
for key in name version target stdlib stdlib_source_hash cache_schema poly_cache_format control_cache_format compiled_unit_cache_format realm_resolution_cache_format contract_runner; do
  if ! grep -q "^$key=" "$manifest"; then
    echo "release archive smoke: manifest key missing: $key" >&2
    exit 1
  fi
done

manifest_value() {
  local key="$1"
  awk -v key="$key" '
    index($0, key "=") == 1 {
      print substr($0, length(key) + 2)
      found = 1
    }
    END {
      if (!found) {
        exit 1
      }
    }
  ' "$manifest"
}

require_manifest_value() {
  local key="$1"
  local expected="$2"
  local actual
  actual="$(manifest_value "$key")"
  if [[ "$actual" != "$expected" ]]; then
    echo "release archive smoke: manifest $key expected $expected, got $actual" >&2
    exit 1
  fi
}

require_manifest_pattern() {
  local key="$1"
  local pattern="$2"
  local actual
  actual="$(manifest_value "$key")"
  if [[ ! "$actual" =~ $pattern ]]; then
    echo "release archive smoke: manifest $key has invalid value: $actual" >&2
    exit 1
  fi
}

require_manifest_value name yulang
require_manifest_value contract_runner 1
require_manifest_pattern version '^.+$'
require_manifest_pattern target '^.+$'
require_manifest_pattern stdlib '^.+$'
require_manifest_pattern stdlib_source_hash '^[0-9a-f]{64}$'
require_manifest_pattern cache_schema '^[0-9]+$'
require_manifest_pattern poly_cache_format '^[0-9]+$'
require_manifest_pattern control_cache_format '^[0-9]+$'
require_manifest_pattern compiled_unit_cache_format '^[0-9]+$'
require_manifest_pattern realm_resolution_cache_format '^[0-9]+$'

python_bin=""
if command -v python3 >/dev/null 2>&1; then
  python_bin="python3"
elif command -v python >/dev/null 2>&1; then
  python_bin="python"
else
  echo "release archive smoke: python3 or python is required to verify bundled std hash" >&2
  exit 1
fi

hash_std_sources() {
  "$python_bin" - "$1" <<'PY'
import hashlib
import pathlib
import sys

root = pathlib.Path(sys.argv[1])
paths = [root / "std.yu"]
paths.extend(sorted((root / "std").rglob("*.yu")))
digest = hashlib.sha256()
for path in sorted(paths, key=lambda item: item.as_posix()):
    rel = path.relative_to(root).as_posix()
    digest.update(rel.encode("utf-8"))
    digest.update(b"\0")
    digest.update(path.read_bytes())
    digest.update(b"\0")
print(digest.hexdigest())
PY
}

bundled_std_hash="$(hash_std_sources "$package_root/lib")"
require_manifest_value stdlib_source_hash "$bundled_std_hash"

if [[ "$bin" != *.exe ]]; then
  chmod 755 "$bin"
fi

env YULANG_SMOKE_SERVER="$archive_server_smoke" \
  "$repo_root/scripts/release-smoke.sh" "$bin"

if [[ "$archive_contract_smoke" != "0" ]]; then
  "$bin" --std-root "$package_root/lib" contract \
    --contract stable-core \
    --case optional_record_defaults \
    "$repo_root/tests/yulang/cases.toml" >/dev/null
  "$bin" --std-root "$package_root/lib" contract \
    --contract stable-core \
    --case std_result_unwrap_or_public_signature \
    "$repo_root/tests/yulang/cases.toml" >/dev/null
  "$bin" --std-root "$package_root/lib" contract \
    --contract file-resource \
    "$repo_root/tests/yulang/cases.toml" >/dev/null
  "$bin" --std-root "$package_root/lib" contract \
    --contract backend.interpreter \
    "$repo_root/tests/yulang/cases.toml" >/dev/null
fi
