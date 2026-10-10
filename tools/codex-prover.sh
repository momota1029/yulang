#!/usr/bin/env bash
# Start a fresh Codex proof session with project roles explicitly registered.
# Workaround for runtimes that do not discover project-local agent config.
set -euo pipefail

repo_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd -P)"
cd -- "$repo_root"

if (( $# == 0 )); then
  printf 'Usage: %s <proof task>\n' "${0##*/}" >&2
  exit 2
fi

codex_bin="${CODEX_BIN:-codex}"
if ! command -v "$codex_bin" >/dev/null 2>&1; then
  printf 'Codex CLI not found: %s\n' "$codex_bin" >&2
  exit 127
fi

toml_quote() {
  local value="$1"
  value="${value//\\/\\\\}"
  value="${value//\"/\\\"}"
  printf '"%s"' "$value"
}

args=(exec --enable multi_agent
  -c 'agents.enabled=true'
  -c 'agents.default_subagent_model="gpt-6.1-sol"'
  -c 'agents.default_subagent_reasoning_effort="high"')

found_prover=false
for file in "$repo_root"/.codex/agents/*.toml; do
  [[ -f "$file" ]] || continue
  name_line="$(grep -m 1 '^name = "' "$file")" || {
    printf 'Missing agent name in %s\n' "$file" >&2
    exit 2
  }
  description_line="$(grep -m 1 '^description = "' "$file")" || {
    printf 'Missing agent description in %s\n' "$file" >&2
    exit 2
  }
  role="${name_line#name = \"}"
  role="${role%\"}"
  description="${description_line#description = \"}"
  description="${description%\"}"
  if [[ ! "$role" =~ ^[a-z][a-z0-9_]*$ ]]; then
    printf 'Invalid agent name in %s: %s\n' "$file" "$role" >&2
    exit 2
  fi
  [[ "$role" == prover ]] && found_prover=true
  args+=(-c "agents.$role.description=$(toml_quote "$description")")
  args+=(-c "agents.$role.config_file=$(toml_quote "$file")")
done
if [[ "$found_prover" != true ]]; then
  printf 'No registered prover role found in .codex/agents\n' >&2
  exit 2
fi

prompt="Yulang constructive proof task. First attempt a real spawn_agent with agent_type=prover, a frozen source baseline and an exclusive proof-note lease. Do not merely announce a role or claim it ran without a tool result. If the named role is unavailable, immediately use a runtime-supported generic worker and supply the prover instructions from .codex/agents/prover.toml in its bounded task; if all subagent spawning fails, derive the proof in the primary. Never replace an executable proof obligation with environment-setup work or reclassify the claim as solved. Report the actual worker identity, observed model if available, a complete derivation or precise unresolved premise, and verification status. Do not alter language semantics or declare source-level soundness from a conditional lemma. Task: $*"
exec "$codex_bin" "${args[@]}" "$prompt"
