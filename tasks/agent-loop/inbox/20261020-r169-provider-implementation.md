# R169 ordinary-provider observation — implementation assignment

Status: proposed Luna-owned path; no code lease granted until prospective CLEAN review and exact primary activation.

Sprint contract: `tasks/agent-loop/sprints/ordinary-provider-incidence-and-observation-20261020-r169.md`; proposed revision 1. Exact contract hash to be recorded at activation.

Goal: provide a bounded borrowed observation of already-retained ordinary FunctionPort dependencies, ordered Replay inputs, source Origins and provider-route references in the exact owners listed below. Preserve multiplicity/order and label absent associations explicitly. This is provisional evidence, not a semantic consumer or theorem closure.

Proposed exact code paths:

- `crates/yu-solver/src/candidate_context.rs`
- `crates/yu-solver/src/shadow_apply.rs`

Exact evidence outputs:

- `notes/theory/2026-10-20-r169-provider-observation.md`
- this handoff file

No new persistent production state, inference result changes, propagation/admission/rollback changes, public CLI/UI/API, external execution, tests/builds, Yulang2/Yulang3 activity, network, or scratch outputs. If an association is not already available through these owners, stop and return the missing owner; no lease expansion is implied.

Required evidence: exact before/after hashes and diff; bounded deterministic observation shape; explanation of borrowed ownership/lifetimes and explicit unavailable fields; static argument that observation cannot mutate solver state; cap/failure behavior; no unsupported historical-event uniqueness claim. Falsifiers include changed inference behavior/state, reordered or omitted existing routes, fabricated source joins, or an unbounded result.

Requested/observed settings UNKNOWN until activation. Proposed implementation budget 1200 seconds within R169 total 3600; no carryover. No Y2 or Y3 execution is authorized. Luna freezes outputs, assigns fresh independent review, records exact writer stop and owns Git integration.
