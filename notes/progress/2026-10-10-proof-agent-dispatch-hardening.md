# Proof agent dispatch hardening (2026-10-10)

Status: configuration and deterministic mock-launch checks only; no live Codex spawn in this change
Branch: `research/simple-sub-intrusion`
Baseline: `3b009bb28613990b3d0128408ea3089bc15ef957`
Authority: user request to make Yulang's internal `prover` operate even when custom-role discovery fails

## Failure and remedy

Previous sessions had two observed `prover` launches after adding `[agents.prover]`, but an available role in one session does not ensure that another session can spawn it. Standalone files in `.codex/agents` were present for eleven roles while only `prover` was registered in project configuration. All eleven are now explicitly declared under `[agents.<name>]` without changing existing role files, model pins, concurrency ceilings or compiler semantics.

Codex CLI and tool-backed sessions have reported custom-role discovery inconsistencies (upstream openai/codex issues #14579 and #15250). The optional `tools/codex-prover.sh` creates a fresh CLI session and explicitly supplies all role registrations and Sol/high defaults through native `-c` overrides. The normal primary is instructed to try actual `prover` delegation; on failure it must immediately use a supported generic worker with the prover's proof contract, or work the proof itself if subagent tools are unavailable. No environment-fix task, synthetic proof closure, or repeated failed role spawn is permitted.

## Verification and limits

`bash -n` passes for both launcher and test scripts. A mock Codex binary test checks exact CLI invocation, role paths/descriptions, the fallback prompt, the Sol/high defaults and consistency of the eleven registered TOML role identities (`bash tools/test-codex-prover.sh` on a representative eleven-role fixture). Neither this mock nor successful static configuration proves an actual running `prover` or an effective model/effort setting. This conversation's execution environment has no Codex CLI or Yulang checkout, so no authenticated live child launch, proof generation, Astra escalation, Cargo suite or GitHub Actions certification was run.

The next actual Codex session should exercise one real `spawn_agent(agent_type=prover)` and record its returned identity, or explicitly identify the generic fallback worker. Continue the existing mathematical proof gates; this configuration change does not close source reachability, general soundness, principality, termination or F5 adoption.
