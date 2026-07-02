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
fi
