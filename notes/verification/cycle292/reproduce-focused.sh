#!/usr/bin/env bash
# Run from a clone with the Lean 4.35 toolchain and prior Yulang .olean files.
# Pass a content-equivalent base SHA if the published commit is not present.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
base=${1:-adf9fae11d8e29273a28751089db2499bcf205d2}
git cat-file -e "$base^{commit}"
git diff --check "$base" HEAD
git diff --exit-code "$base" HEAD -- crates spec notes/plan lean/Audit.lean lean/lakefile.toml lean/lean-toolchain
tmp=$(mktemp)
trap 'rm -f "$tmp"' EXIT
python3 - "$base" >"$tmp" <<'PY'
import pathlib
import re
import subprocess
import sys

base = sys.argv[1]
def git(*args):
    return subprocess.check_output(['git', *args], text=True)

old = git('show', f'{base}:lean/Yulang.lean')
barrel = git('show', 'HEAD:lean/Yulang.lean')
assert barrel.startswith(old), 'Existing barrel changed'
paths = [pathlib.Path(p) for p in git(
    'diff', '--diff-filter=A', '--name-only', base, 'HEAD', '--', 'lean/Yulang'
).splitlines()]
modules = {p.stem: p for p in paths}
allowed_additions = set(barrel[len(old):].splitlines())
assert not git('diff', '--diff-filter=MDR', '--name-only', base, 'HEAD', '--', 'lean/Yulang', 'lean/Audit').strip()
seen, active = set(), set()
def visit(name):
    if name in seen:
        return
    assert name not in active, f'import dependency cycle at {name}'
    assert f'import Yulang.{name}' in allowed_additions, name
    active.add(name)
    for dep in re.findall(r'^import Yulang\.([A-Za-z0-9_]+)\s*$', modules[name].read_text(), re.M):
        if dep in modules:
            visit(dep)
    active.remove(name)
    seen.add(name)
    print(name)
for name in sorted(modules):
    visit(name)
assert set(modules) == seen
PY
mapfile -t modules <"$tmp"
mapfile -t audits < <(git diff --diff-filter=A --name-only "$base" HEAD -- lean/Audit | sed 's|^lean/||')
cd lean
for name in "${modules[@]}"; do
  timeout 160s lake env lean --trust=0 -M 3200 -DwarningAsError=true -R . \
    -o ".lake/build/lib/lean/Yulang/$name.olean" "Yulang/$name.lean"
  echo "focused $name exit 0"
done
for audit in "${audits[@]}"; do
  if grep '^import ' "$audit" | grep -qv '^import Yulang\.'; then
    echo "Unexpected audit dependency in $audit" >&2
    exit 1
  fi
  timeout 160s lake env lean --trust=0 -M 3200 -DwarningAsError=true "$audit"
  echo "standalone $audit exit 0"
done
echo "Verified ${#modules[@]} focused modules and ${#audits[@]} standalone audits."
