#!/usr/bin/env bash
# Verify a Lean working tree or commit the way the supervisor does by hand.
#
# usage: tools/verify-lean.sh <repo-dir> <base-rev> [--no-build]
#
#   <repo-dir>  a checkout (clone or worktree) containing lean/
#   <base-rev>  the last verified commit; added/removed lines are measured against it
#   --no-build  skip lake build / Audit (only diff checks)
#
# Checks (exit code 0 only if every one passes):
#   1. cd lean && lake build --wfail                 (exit code read directly)
#   2. lake env lean --trust=0 Audit.lean            (exit code read directly)
#   3. every audited declaration depends only on propext / Classical.choice / Quot.sound
#   4. no line removed from any existing lean/ file since <base-rev>
#   5. no sorry / native_decide / axiom (any modifier) / metaprogramming in lines added to lean/
#   6. base exists and is an ancestor of HEAD; lean/ has no uncommitted or untracked files
#   7. lake config (lakefile.*, lake-manifest.json, lean-toolchain) unchanged, except the
#      allowed pattern: new `[[lean_lib]]` blocks are NOT allowed here (report to the owner)
#   8. new files are only lean/Yulang/*.lean, lean/SpecExamples*.lean or lean/Main*.lean, and each new module is imported
#   9. Audit.lean and lean/Audit/*.lean: new lines only appended at the end (top `import` lines also allowed);
#      new audit parts may be added as lean/Audit/<Name>.lean (Audit.lean grew too large to publish whole)
#  10. supervisor-owned gate tools/AxiomGate.lean over every non-system module
#
# LIMITATION: the build runs the worker's Lean code and uses the worker's lean/.lake. For an untrusted
# worker, run this inside a sandbox or on a fresh checkout of the fetched commit (see the harness note).
#
# Output: one "ok: ..." or "FAIL: ..." line per check, and a final "verify-lean: PASS|FAIL".
set -u
set -o pipefail
script_dir=$(cd "$(dirname "$0")" && pwd)
repo=${1:?usage: verify-lean.sh <repo-dir> <base-rev> [--no-build]}
base=${2:?usage: verify-lean.sh <repo-dir> <base-rev> [--no-build]}
nobuild=${3:-}
fail=0
log=$(mktemp -d)
cd "$repo" || { echo "FAIL: cannot cd to $repo"; exit 2; }
head_rev=$(git rev-parse --short HEAD)
git rev-parse --verify --quiet "$base^{commit}" >/dev/null || { echo "FAIL: unknown base $base"; exit 2; }
git merge-base --is-ancestor "$base" HEAD || { echo "FAIL: $base is not an ancestor of HEAD"; exit 2; }
dirty=$(git status --porcelain --untracked-files=all -- lean)
if [ -n "$dirty" ]; then echo "FAIL: lean/ has uncommitted or untracked files:"; echo "$dirty" | head -5; fail=1; fi
echo "verify-lean: $repo @ $head_rev (base $base)"

if [ "$nobuild" != "--no-build" ]; then
  ( cd lean && lake build --wfail > "$log/build.out" 2>&1 )
  rc=$?
  if [ $rc -eq 0 ]; then echo "ok: lake build --wfail ($(tail -1 "$log/build.out"))"; else echo "FAIL: lake build exit $rc (see $log/build.out)"; fail=1; fi

  : > "$log/audit.out"
  for af in Audit.lean $(cd lean && ls Audit/*.lean 2>/dev/null | sort); do
    ( cd lean && lake env lean --trust=0 "$af" >> "$log/audit.out" 2>&1 )
    rc=$?
    if [ $rc -eq 0 ]; then echo "ok: $af exit 0"; else echo "FAIL: $af exit $rc (see $log/audit.out)"; fail=1; fi
  done

  # Audit prints long lines wrapped; join then split per declaration.
  tr '\n' ' ' < "$log/audit.out" | grep -oE 'depends on axioms: \[[^]]*\]' > "$log/axiom-lines.txt"
  total=$(wc -l < "$log/axiom-lines.txt")
  bad=$(sed 's/.*axioms: \[//; s/\]//' "$log/axiom-lines.txt" | tr ',' '\n' | sed 's/ //g' \
        | grep -v -E '^(propext|Classical.choice|Quot.sound|)$' | sort -u)
  if [ -z "$bad" ]; then echo "ok: axioms only propext/Classical.choice/Quot.sound over $total printed declarations"; else echo "FAIL: forbidden axioms: $bad"; fail=1; fi
fi

removed=$(git diff --numstat "$base"..HEAD -- lean | awk '$1!="-" && $2>0 {print $3" (-"$2")"}')
if [ -z "$removed" ]; then echo "ok: no removed lines in lean/ since $base"; else echo "FAIL: removed lines:"; echo "$removed"; fail=1; fi

added=$(git diff "$base"..HEAD -- lean | grep '^+' | grep -v '^+++')
forbidden=$(echo "$added" | grep -nE '(^|[^A-Za-z_])(sorry|sorryAx|admit)([^A-Za-z_]|$)|native_decide|ofReduceBool|skipKernelTC|implemented_by|@\[extern|addDecl|^\+\s*(@\[[^]]*\]\s*)*((private|protected|noncomputable|unsafe|partial)\s+)*axiom\b' | head -8)
if [ -z "$forbidden" ]; then echo "ok: no sorry/native_decide/axiom-like constructs in added lines"; else echo "FAIL: forbidden constructs in added lines:"; echo "$forbidden"; fail=1; fi
review=$(echo "$added" | grep -nE '^\+\s*(run_cmd|#eval|elab|elab_rules|macro|macro_rules|syntax|initialize|builtin_initialize|declare_syntax_cat)\b' | head -8)
reviewn=0
if [ -n "$review" ]; then reviewn=$(echo "$review" | wc -l); echo "REVIEW: metaprogramming/#eval in added lines (a human must read these):"; echo "$review"; fi

# 7. lake config unchanged (only pure additions of `[[lean_lib]] name = "SpecExamples*"` are tolerated)
if ! git diff --quiet "$base"..HEAD -- lean/lakefile.lean lean/lake-manifest.json lean/lean-toolchain; then
  echo "FAIL: lake config changed (lakefile.lean / manifest / toolchain); needs the owner's approval"; fail=1
else
  badlake=$(git diff -U0 "$base"..HEAD -- lean/lakefile.toml | grep -E '^[-+]' | grep -vE '^(\+\+\+|---)' \
            | grep -vE '^\+(\[\[lean_lib\]\]|name = "(SpecExamples|Main)[A-Za-z0-9]*"|)$')
  if [ -n "$badlake" ]; then echo "FAIL: lakefile.toml changed beyond SpecExamples* lean_lib additions:"; echo "$badlake"; fail=1
  else echo "ok: lake config unchanged (or only SpecExamples*/Main* libs added)"; fi
fi

# 8. new files
newfiles=$(git diff --diff-filter=A --name-only "$base"..HEAD -- lean)
badnew=$(echo "$newfiles" | grep -v '^$' | grep -vE '^lean/(Yulang/[A-Za-z0-9_]+|Audit/[A-Za-z0-9_]+|(SpecExamples|Main)[A-Za-z0-9]*)\.lean$')
if [ -n "$badnew" ]; then echo "FAIL: unexpected new files:"; echo "$badnew"; fail=1; else echo "ok: new files are Yulang modules only"; fi
for f in $(echo "$newfiles" | grep -E '^lean/Yulang/[A-Za-z0-9_]+\.lean$'); do
  m=$(basename "$f" .lean)
  if ! grep -rqE "^import Yulang\.$m\b" lean --include=*.lean --exclude-dir=Audit --exclude-dir=.lake; then echo "FAIL: new module Yulang.$m is not imported by any built module (only audit parts import it, so lake build skips it)"; fail=1; fi
done

# 9. Audit.lean and lean/Audit/*.lean: insertions only at the end (existing files)
for af in lean/Audit.lean $(git ls-tree -r --name-only "$base" -- lean/Audit | grep -E '\.lean$'); do
  git cat-file -e "$base":"$af" 2>/dev/null || continue
  n=$(git show "$base":"$af" | wc -l)
  # Allowed: appending at the end, and inserting `import ...` lines before line 1.
  badhunks=$(git diff -U0 "$base"..HEAD -- "$af" | grep '^@@' | grep -vE "^@@ -$n(,0)? |^@@ -0,0 ")
  topbad=$(git diff -U0 "$base"..HEAD -- "$af" | awk '/^@@ -0,0 /{f=1;next} /^@@/{f=0} f && /^\+/ {print}' | grep -v '^+import ')
  if [ -n "$badhunks" ]; then echo "FAIL: $af changed other than by appending at the end:"; echo "$badhunks"; fail=1
  elif [ -n "$topbad" ]; then echo "FAIL: $af: lines inserted at the top must be import lines:"; echo "$topbad"; fail=1
  else echo "ok: $af only appended (plus top import lines)"; fi
done

# 10. supervisor-owned gate
if [ "$nobuild" != "--no-build" ]; then
  gate="$script_dir/AxiomGate.lean"
  ( cd lean && lake env lean --trust=0 "$gate" > "$log/gate.out" 2>&1 )
  if grep -q 'AXIOM-GATE-PASS' "$log/gate.out"; then echo "ok: $(grep -o 'AXIOM-GATE-PASS: [0-9]* declarations' "$log/gate.out")"
  else echo "FAIL: supervisor axiom gate (see $log/gate.out)"; tail -3 "$log/gate.out"; fail=1; fi
fi

if [ $fail -eq 0 ]; then
  tag=""; [ "${reviewn:-0}" -gt 0 ] && tag=" with $reviewn REVIEW item(s) above"
  if [ "$nobuild" = "--no-build" ]; then echo "verify-lean: PASS (diff checks only, NO build)$tag"; else echo "verify-lean: PASS$tag"; fi
else echo "verify-lean: FAIL"; fi
exit $fail
