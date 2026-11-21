#!/bin/bash
# usage: tools/dots-integrate.sh <repo-path|origin> <branch> <label>
#
# Integrate one dots report (or a batch of consecutive reports) onto
# integration/m1-final, then copy lean/ and notes/ onto yulang3.
#
#   1. In the verify clone ($DOTS_VERIFY_DIR), check out <branch> detached.
#      If origin/integration/m1-final is not an ancestor (supervisor inbox
#      notes moved it), merge it in. Any conflict aborts with exit 6.
#   2. Run tools/verify-lean.sh against origin/integration/m1-final.
#      Exit 5 on failure. Read the REVIEW lines in the output yourself.
#   3. Push HEAD to integration/m1-final (never force). Exit 7 on failure.
#   4. In the main checkout ($DOTS_MAIN_DIR, must be on yulang3 and clean),
#      fast-forward yulang3, check out lean/ and notes/ from integration,
#      run `cargo test -p yu-syntax --offline`, commit and push yulang3.
#      If the test fails, the checkout is reset and nothing is pushed (exit 9).
#
# Rules learned the hard way:
#   - <branch> must point at the cycle's report commit (the commit that adds
#     notes/handoff/dots-cycle-N.md), never at dots' live head: a live head can
#     hold a mid-cycle snapshot that dots later edits, which breaks the
#     append-only gate.
#   - Never run two integrations in the same verify clone at once.
#   - One run takes over two hours as of cycle 315 (about 1300 audit files are
#     re-run) and grows each cycle. If several reports are waiting, integrate
#     only the newest one: it contains the earlier cycles.
#   - If your job runner kills jobs after a fixed time, start this detached
#     (e.g. `setsid nohup ... > log 2>&1 &`) and wait on the log for the
#     final line, instead of chaining a wait and an integration in one job.
set -u
src=$1; br=$2; label=$3
R=${DOTS_MAIN_DIR:-$(cd "$(dirname "$0")/.." && pwd)}
V=${DOTS_VERIFY_DIR:-$R/../yulang-verify-dots}
LOG=${DOTS_LOG_DIR:-${TMPDIR:-/tmp}}
cd "$V" || exit 2
git fetch -q origin integration/m1-final || exit 2
base=$(git rev-parse FETCH_HEAD)
if [ "$src" = origin ]; then git fetch -q origin "$br" || exit 2; else git fetch -q "$src" "$br" || exit 2; fi
git checkout -q --detach FETCH_HEAD || exit 2
git log -1 --oneline
git status | tail -2
if ! git merge-base --is-ancestor "$base" HEAD; then
  if git merge -q --no-edit -m "Merge integration/m1-final into $label" "$base"; then
    echo "merged integration $base into $label"
  else
    git merge --abort; echo "$label rc=6 (merge with integration $base conflicts)"; exit 6
  fi
fi
bash "$R/tools/verify-lean.sh" "$V" "$base"; rc=$?
echo "$label rc=$rc"
[ $rc -eq 0 ] || exit 5
git push -q origin HEAD:integration/m1-final || { echo "push failed"; exit 7; }
echo "PUSHED $label"
cd "$R" || exit 8
[ "$(git rev-parse --abbrev-ref HEAD)" = yulang3 ] || { echo "sync skipped: main checkout not on yulang3"; exit 0; }
[ -z "$(git status --porcelain)" ] || { echo "sync skipped: main checkout dirty"; exit 0; }
git fetch -q origin yulang3 integration/m1-final
git merge -q --ff-only origin/yulang3 || { echo "sync skipped: yulang3 not fast-forwardable"; exit 0; }
git checkout origin/integration/m1-final -- lean notes
if [ -z "$(git status --porcelain)" ]; then echo "sync: nothing to do"; exit 0; fi
cargo test -p yu-syntax --offline -q > "$LOG/yusyntax-sync-$label.log" 2>&1; t=$?
echo "yu-syntax exit $t"
if [ $t -ne 0 ]; then git reset -q --hard origin/yulang3; echo "sync aborted"; exit 9; fi
git add -A lean notes
git commit -qm "yulang3: sync lean/notes from integration ($label)"
git push -q origin yulang3 && echo "SYNCED yulang3 $label"
exit 0
