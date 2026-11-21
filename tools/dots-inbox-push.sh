#!/bin/bash
# usage: tools/dots-inbox-push.sh <append-file.md> <label> <commit-subject>
#
# Append a supervisor item to notes/plan/dots-inbox.md on integration/m1-final.
# lean/ stays byte-identical to the already verified integration head, so only
# the diff checks of verify-lean (--no-build) run. Refuses any other change.
#
# Do not run this while tools/dots-integrate.sh is between its fetch and its
# push: the integration push would then be rejected as non-fast-forward.
# Run it before or after an integration.
set -e
src=$(realpath "$1"); label=$2; subject=$3
R=${DOTS_MAIN_DIR:-$(cd "$(dirname "$0")/.." && pwd)}
LOG=${DOTS_LOG_DIR:-${TMPDIR:-/tmp}}
cd "$R"
git fetch -q origin integration/m1-final
base=$(git rev-parse origin/integration/m1-final)
W=$(mktemp -d "$LOG/dots-inbox-$label.XXXX")
git worktree add -q --detach "$W" "$base"
cat "$src" >> "$W/notes/plan/dots-inbox.md"
cd "$W"
git add -A
git commit -qm "$subject"
changed=$(git diff --name-only "$base" HEAD)
[ "$changed" = "notes/plan/dots-inbox.md" ] || { echo "unexpected paths: $changed"; exit 9; }
set +e
cargo test -p yu-syntax --offline -q > "$LOG/yusyntax-$label.log" 2>&1; r=$?; echo "yu-syntax exit $r"; [ $r -eq 0 ] || exit 4
bash "$R/tools/verify-lean.sh" "$W" "$base" --no-build; r=$?; echo "verify-lean(no-build) exit $r"; [ $r -eq 0 ] || exit 5
git merge-base --is-ancestor "$base" HEAD || exit 6
git push -q origin HEAD:integration/m1-final; r=$?; echo "push exit $r"
[ $r -eq 0 ] && echo "PUSHED $label"
exit $r
