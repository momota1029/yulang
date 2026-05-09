#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

if (($# == 0)); then
  sample="$(mktemp)"
  trap 'rm -f "$sample"' EXIT
  cat >"$sample" <<'YU'
my inc x = x + 1
inc 41
YU
  set -- "$sample"
fi

for path in "$@"; do
  echo "== $path =="
  /usr/bin/time -p cargo run -q -p yulang -- --native-compare-i64 "$path"
done
