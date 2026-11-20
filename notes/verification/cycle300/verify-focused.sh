#!/usr/bin/env bash
# Recheck cycle 300 against a built *prior* Lean cache (not a whole-tree build).
# Usage: bash verify-focused.sh [C299-base-ref] [prior-olean-root]
set -euo pipefail
repo=$(git rev-parse --show-toplevel)
cd "$repo"
base=${1:-8ea24d0ffabde73f974a4556b846a17ed2eb6feb}
prior=${2:-"$repo/lean/.lake/build/lib/lean"}
verify="$repo/notes/verification/cycle300"
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
if [[ ! -e "$scratch/Yulang/GeneralFiniteAssignment246.olean" ]]; then
  (cd lean && timeout 180s lean "${opts[@]}" -R . -o "$scratch/Yulang/GeneralFiniteAssignment246.olean"     "Yulang/GeneralFiniteAssignment246.lean")
  echo "Existing targeted baseline dependency rebuilt: GeneralFiniteAssignment246"
fi
echo "Base tree: $(git rev-parse "$base^{tree}"); tested data tree: $(git rev-parse 'HEAD^{tree}')."
count=0
while IFS= read -r m; do
  [[ ${new[$m]+added} ]] || continue
  (cd lean && timeout 180s lean "${opts[@]}" -R . -o "$scratch/Yulang/$m.olean" "Yulang/$m.lean")
  count=$((count+1))
  echo "Isolated source $m PASS"
done < <(sed -n 's/^import Yulang\.//p' lean/Yulang.lean)
test "$count" -eq "${#sources[@]}"
for f in lean/Audit/Cycle300*.lean; do
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
    expected=re.findall(r"^#print axioms (\S+)", (pathlib.Path("lean/Audit") / p.name.removesuffix(".txt")).read_text(), re.M)
    entries=re.findall(r"^'([^']+)'\s+(?:depends\s+on\s+axioms:\s*\[(.*?)\]|does\s+not\s+depend\s+on\s+any\s+axioms)", t, flags=re.M|re.S)
    assert len(expected)==len(entries)>0,p
    assert set(expected)=={name for name,_ in entries},(p,expected,entries)
    for name,axioms in entries:
        if axioms:
            assert set(a.strip() for a in axioms.split(",")).issubset(allowed),(p,name,axioms)
    n+=len(entries)
print(f"Audited {n} theorem declarations; no axioms outside propext, Classical.choice, Quot.sound.")
PY
for f in lean/Audit/Cycle299*.lean \
         lean/Audit/Cycle298*.lean \
         lean/Audit/Cycle277{CompiledInstall,CompiledEvidence,CompiledStable,CompiledExact}.lean \
         lean/Audit/Cycle285{Display,Path,Sharp,SourceReads}.lean; do
  (cd lean && timeout 140s lean "${opts[@]}" "${f#lean/}") >/dev/null
  echo "Existing $f PASS"
done
{
  sed -n '/^import Yulang\..*300$/p' lean/Yulang.lean
  echo "open Yulang"
  echo "#check GeneralDepthTwoFirstInstall300.enabled"
  echo "#check GeneralDepthTwoSecondInstall300.enabled"
  echo "#check GeneralDepthTwoEvidence300.actual_dictionary"
  echo "#check GeneralDepthTwoFinalHalt300.source_halted"
  echo "#check GeneralDepthTwoCertifiedRead300.evidence_at"
  echo "#check GeneralDepthTwoObserved300.exact_on_actual"
  echo "#check GeneralDepthTwoMachine300.exact_step"
  echo "#check GeneralDepthTwoRootAvailability300.exact_availability"
} > "$scratch/barrel-tail.lean"
(cd lean && lean "${opts[@]}" "$scratch/barrel-tail.lean")
echo "Focused barrel tail PASS"
for test in two-installs where-read phase-data current-candidates; do
  (cd lean && timeout 140s lean "${opts[@]}" --run "$verify/run-$test.lean") > "$scratch/report"
  cmp "$scratch/report" "$verify/$test.txt"
  echo "Replay $test byte-identical PASS"
done
echo "Isolated build: $count modules; no whole Lake build or Rust execution."
