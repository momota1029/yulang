# R169 ordinary-provider observation — implementation assignment

Status at proposal: proposed Luna-owned path; superseded by the frozen implementation result receipt below.

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

## Frozen implementation result receipt — R169-ORDINARY-PROVIDER-OBSERVATION / revision 1

Owner/author: `/root` (Luna primary), current session `current-conversation-2026-10-20-r169`. Contract revision 1 SHA-256: `f0e71f7b3824075ad9ee5166b9999486a24ed8da44cc693a4259b93cb8269bb8`. The prospective reviewer was `/root/r157_contract_review`; the primary activated the exact leases after CLEAN review.

Exact frozen outputs and SHA-256:

- `crates/yu-solver/src/candidate_context.rs` — `d884c20a98140da2a737d65f61faa97491bd9a2af7870bf3f0ea7dd428e9ffeb`
- `crates/yu-solver/src/shadow_apply.rs` — `b9d5a1a1ddb013045723f258161d647a0dc1fe8cf39b772b89b6eadd2be15622`
- `notes/theory/2026-10-20-r169-provider-observation.md` — final review receipt/hash recorded after its status-only delta.
- This handoff — final hash recorded in the R169 closeout.

Result: exposes a bounded borrowed observation of retained FunctionPort dependencies, relation-local bound admissions/emissions and source Origins. Rows retain graph/root FunctionPort ordinal, relation, table ordinal and row kind. Total rows cap at 256 with explicit truncation; unavailable Lambda slot-2 source joins remain explicit. The view adds no persistent solver records and does not mutate inference. No unique historical Replay constructor event is inferred. This is research evidence only and does not add Yulang2 coverage.

Fresh independent code review by `/root/r157_contract_review`: **CLEAN** on the exact two-file lease, including the `function_port_ordinal` grouping-field delta. A second fresh status-only review of the evidence note was also CLEAN. Both reviews were static. `git diff --check` passed. No tests, builds, compiler/runtime, Yulang2/Yulang3, external Oracle, network or generated outputs were run.

Writer stop: Luna froze the exact source and evidence outputs after review; no descendant or further writer remains. The observation lease is closed. It exposes no substitute for `R169-SOURCE-FACT-CAPTURE-INCIDENCE-1`, which remains OPEN with the proof lane's source owner and falsifier. No inference, theorem or production gate is closed by this implementation.
