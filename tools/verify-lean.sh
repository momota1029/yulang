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
#   5. no sorry / native_decide / new axiom in lines added to lean/ since <base-rev>
#
# Output: one "ok: ..." or "FAIL: ..." line per check, and a final "verify-lean: PASS|FAIL".
set -u
repo=${1:?usage: verify-lean.sh <repo-dir> <base-rev> [--no-build]}
base=${2:?usage: verify-lean.sh <repo-dir> <base-rev> [--no-build]}
nobuild=${3:-}
fail=0
log=$(mktemp -d)
cd "$repo" || { echo "FAIL: cannot cd to $repo"; exit 2; }
head_rev=$(git rev-parse --short HEAD)
echo "verify-lean: $repo @ $head_rev (base $base)"

if [ "$nobuild" != "--no-build" ]; then
  ( cd lean && lake build --wfail > "$log/build.out" 2>&1 )
  rc=$?
  if [ $rc -eq 0 ]; then echo "ok: lake build --wfail ($(tail -1 "$log/build.out"))"; else echo "FAIL: lake build exit $rc (see $log/build.out)"; fail=1; fi

  ( cd lean && lake env lean --trust=0 Audit.lean > "$log/audit.out" 2>&1 )
  rc=$?
  if [ $rc -eq 0 ]; then echo "ok: Audit.lean exit 0"; else echo "FAIL: Audit exit $rc (see $log/audit.out)"; fail=1; fi

  # Audit prints long lines wrapped; join then split per declaration.
  tr '\n' ' ' < "$log/audit.out" | sed "s/'Yulang/\n'Yulang/g; s/'SpecExamples/\n'SpecExamples/g" \
    | grep 'depends on axioms' > "$log/axiom-lines.txt"
  total=$(wc -l < "$log/axiom-lines.txt")
  bad=$(sed 's/.*axioms: \[//; s/\].*//' "$log/axiom-lines.txt" | tr ',' '\n' | sed 's/ //g' \
        | grep -v -E '^(propext|Classical.choice|Quot.sound|)$' | sort -u)
  if [ -z "$bad" ]; then echo "ok: axioms only propext/Classical.choice/Quot.sound over $total printed declarations"; else echo "FAIL: forbidden axioms: $bad"; fail=1; fi
fi

removed=$(git diff --numstat "$base"..HEAD -- lean | awk '$1!="-" && $2>0 {print $3" (-"$2")"}')
if [ -z "$removed" ]; then echo "ok: no removed lines in lean/ since $base"; else echo "FAIL: removed lines:"; echo "$removed"; fail=1; fi

forbidden=$(git diff "$base"..HEAD -- lean | grep '^+' | grep -v '^+++' | grep -nE '(^|[^A-Za-z_])sorry([^A-Za-z_]|$)|native_decide|^\+axiom ' | grep -v -E '^\S*\+\s*(--|/-)' | head -5)
if [ -z "$forbidden" ]; then echo "ok: no sorry/native_decide/axiom in added lines"; else echo "FAIL: forbidden constructs in added lines:"; echo "$forbidden"; fail=1; fi

if [ $fail -eq 0 ]; then echo "verify-lean: PASS"; else echo "verify-lean: FAIL"; fi
exit $fail
