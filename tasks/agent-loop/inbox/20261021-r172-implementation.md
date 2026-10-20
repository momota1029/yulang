# R172 implementation assignment candidate — source-keyed borrowed query

Status: **candidate, not assigned**; no write/probe lease until prospective CLEAN review and Luna activation.

- Contract: `tasks/agent-loop/sprints/source-fact-capture-construction-20261021-r172.md`.
- Baseline: `e6ffba08c`; owner hashes are pinned in the contract.
- Reuse R171 CLEAN source membership and successful candidate-inference output; fixture is read-only and unchanged. Do not rerun R171.
- Exact Luna write leases: `candidate_context.rs`, `candidate_scheme.rs`, `shadow_apply.rs`, new `tools/inference-playground/examples/r172_source_capture.rs`, `notes/theory/2026-10-21-r172-source-query.md`, this handoff, exact conditional probe receipts and `target/r172/`. No other paths.
- Build a bounded borrowed API keyed by authenticated source occurrence identities. Preserve relation to owner-authored source fact keys, origin candidates, same-provider Capture/shared anchor, that route's maps, ordered dependency/Replay alternatives and actual A_F consumer. Preserve all ambiguity. Select required evidence before display truncation and label component-wise completeness. Do not derive incidence from q equality or counts.
- If current owners cannot construct the association, freeze exact owner/falsifier and do not add persistent data, propagation, source admission or new leases. Conditional one-shot probe only after the query demonstrably exposes the discriminating association and exact command receives independent CLEAN review. Otherwise write NOT_RUN and stop.
- Proposed implementation grant 1500s plus conditional 300s probe within 4200s total; no Astra, descendants, retries, tests, Y2, evaluator or external execution. Luna owns independent review/adjudication/Git.
