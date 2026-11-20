#!/usr/bin/env bash
# Recheck cycle 297 against a built *prior* Lean cache (not a whole-tree build).
# Usage: bash verify-focused.sh [C296-base-ref] [prior-olean-root]
set -euo pipefail
repo=$(git rev-parse --show-toplevel)
cd "$repo"
base=${1:-ff9d762e03d051f6bfaa9278465c5aaa6342ec38}
prior=${2:-"$repo/lean/.lake/build/lib/lean"}
verify="$repo/notes/verification/cycle297"
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
readonly scratch
mkdir "$scratch/Yulang" "$scratch/results"
git cat-file -e "$base^{commit}"
test -e "$prior/Main.olean"
declare -A new
mapfile -t sources < <(git diff --diff-filter=A --name-only "$base" HEAD -- lean/Yulang)
test "${#sources[@]}" -gt 0
for src in "${sources[@]}"; do
  name=${src##*/}
  new["${name%.lean}"]=1
done
ln -s "$(realpath "$prior/Main.olean")" "$scratch/Main.olean"
while IFS= read -r f; do
  b=${f##*/}
  if [[ ! ${new[${b%%.*}]+added} ]]; then ln -s "$f" "$scratch/Yulang/$b"; fi
done < <(find "$(realpath "$prior/Yulang")" -maxdepth 1 -type f | sort)
export LEAN_PATH="$scratch:$(lean --print-prefix)/lib/lean"
opts=(--trust=0 -j 1 -M 3200 -DwarningAsError=true)
python3 "$verify/theorem-index.py" >"$scratch/index"
cmp "$scratch/index" "$verify/theorem-index.md"
echo "Lean $(lean --version)"
echo "Base tree: $(git rev-parse "$base^{tree}"); tested data tree: $(git rev-parse 'HEAD^{tree}')."
count=0
while IFS= read -r m; do
  [[ ${new[$m]+added} ]] || continue
  (cd lean && timeout 180s lean "${opts[@]}" -R . -o "$scratch/Yulang/$m.olean" "Yulang/$m.lean")
  count=$((count+1))
  echo "Isolated source $m PASS"
done < <(sed -n 's/^import Yulang\.//p' lean/Yulang.lean)
test "$count" -eq "${#sources[@]}"
for f in lean/Audit/Cycle297*.lean; do
  report="$scratch/results/${f##*/}.txt"
  (cd lean && timeout 180s lean "${opts[@]}" "${f#lean/}") >"$report"
  echo "Standalone $f PASS"
done
python3 - "$scratch/results" <<'PY'
import pathlib, re, sys
n=0
allowed={'propext','Classical.choice','Quot.sound'}
for p in pathlib.Path(sys.argv[1]).glob("*.txt"):
    t=p.read_text()
    chunks=re.findall(r"depends on axioms: \[(.*?)\]", t, flags=re.S)
    none=len(re.findall(r"does not depend on any axioms",t))
    assert len(chunks)+none>0,p
    for c in chunks:
        assert set(a.strip() for a in c.split(",")).issubset(allowed),(p,c)
    n+=len(chunks)+none
print(f"Audited {n} theorem declarations; no axioms outside propext, Classical.choice, Quot.sound.")
PY
for f in lean/Audit/Cycle267{Observer,Novelty,Install}.lean \
         lean/Audit/Cycle269{Journal,Adapters,Raw}.lean \
         lean/Audit/Cycle271{ActualBoundary,SourceTraces}.lean \
         lean/Audit/Cycle279{InstallDelta,Witness,ReachableNovelty}.lean \
         lean/Audit/Cycle280{Replay,Archive}.lean \
         lean/Audit/Cycle281{Footprint,PacketChart}.lean \
         lean/Audit/Cycle284{Driver,Window,Failure}.lean \
         lean/Audit/Cycle285{Path,Sharp,Complete}.lean; do
  (cd lean && timeout 140s lean "${opts[@]}" "${f#lean/}") >/dev/null
  echo "Existing $f PASS"
done
{
  sed -n '/^import Yulang\..*297$/p' lean/Yulang.lean
  echo "open Yulang"
  echo "#check GeneralRebaseRawObserver297.strict_exact"
  echo "#check GeneralRebaseSignedHistory297.Version.finite_prefix_minimum"
  echo "#check GeneralRebaseSignedHistory297.Loose.finite_prefix_minimum"
  echo "#check GeneralRebaseSignedRefresh297.preserves_test"
} > "$scratch/barrel-tail.lean"
(cd lean && lean "${opts[@]}" "$scratch/barrel-tail.lean")
echo "Focused barrel tail PASS"
for test in depth-observer merge-observer signed-polarities; do
  (cd lean && timeout 140s lean "${opts[@]}" --run "$verify/run-$test.lean") > "$scratch/report"
  cmp "$scratch/report" "$verify/$test.txt"
  echo "Replay $test byte-identical PASS"
done
echo "Isolated build: $count modules; no whole Lake build or Rust execution."
