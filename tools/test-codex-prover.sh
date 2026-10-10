#!/usr/bin/env bash
set -euo pipefail
root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
tmp="$(mktemp -d)"
trap 'rm -rf -- "$tmp"' EXIT
mkdir -p "$tmp/bin"
cat > "$tmp/bin/codex" <<'MOCK'
#!/usr/bin/env bash
printf '%s\n' "$@" > "$YULANG_ARG_CAPTURE"
MOCK
chmod +x "$tmp/bin/codex"

CODEX_BIN="$tmp/bin/codex" YULANG_ARG_CAPTURE="$tmp/argv" bash "$root/tools/codex-prover.sh" 'Prove relation replay soundness'
python3 - "$tmp/argv" "$root" <<'PY'
from pathlib import Path
import re
import sys
import tomllib
args = Path(sys.argv[1]).read_text().splitlines()
root = Path(sys.argv[2])
assert args[:3] == ['exec', '--enable', 'multi_agent'], args[:3]
assert args[-1].startswith('Yulang constructive proof task.')
assert 'Prove relation replay soundness' in args[-1]
assert 'generic worker' in args[-1]
assert len(args[3:-1]) % 2 == 0
assert all(args[i] == '-c' for i in range(3,len(args)-1,2))
settings = [args[i + 1] for i in range(3,len(args)-1,2)]
assert 'agents.default_subagent_model="gpt-6.1-sol"' in settings
assert 'agents.default_subagent_reasoning_effort="high"' in settings
files = sorted((root / '.codex/agents').glob('*.toml'))
expected_roles = set()
for f in files:
    role = tomllib.loads(f.read_text())['name']
    assert re.fullmatch('[a-z][a-z0-9_]*',role)
    expected_roles.add(role)
    assert any(s.startswith(f'agents.{role}.config_file=') and str(f) in s for s in settings), role
    assert any(s.startswith(f'agents.{role}.description=') for s in settings), role
config = tomllib.loads((root/'.codex/config.toml').read_text())
registered = set(config['agents']) - {'enabled','max_concurrent_threads_per_session','default_subagent_model','default_subagent_reasoning_effort','interrupt_message'}
assert expected_roles == registered, (expected_roles,registered)
for role in registered:
    conf_file = root/'.codex'/config['agents'][role]['config_file']
    assert tomllib.loads(conf_file.read_text())['name'] == role
print(f'PASS: CLI argv, fallback prompt, and {len(expected_roles)} registered roles')
PY
