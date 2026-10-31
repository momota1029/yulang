# Sprint EFFECT-PERMISSION-CONSUMER-PREMISES/20261102-R121

Status: admitted continuation of the unchanged Rust/Lean soundness and effect-hygiene objective. Dispatcher selected this bounded dependency reduction after R120. It asks whether the successful consumer's local family-membership consequence depends on authenticating the first `.position` match. It must not claim complete source correspondence or weaken any parent theorem.

Branch `yulang3`; source identity is the R120 in-memory receiver composed from immutable baseline `d177c46ec61fcadd70a3d587c2f8934f6bc91f46`, R117 and R119, final SHA-256 `108a50b5ed8aaa4813fa42ec4372d72dab4f67d4a158e7f551b8672ca3b9f470`. Do not reconstruct or save it again. R120 source handoff `tasks/agent-loop/inbox/effect-permission-member-trace-r120-source.md`, SHA-256 `0c503338c144eab1feb2fce128227a7409f312b947876cd504f5b1af9fd1050e`; proof handoff `tasks/agent-loop/inbox/effect-permission-member-trace-r120-proof.md`, SHA-256 `2ce7eaba1483c4f9d5c190977421717125aa55b37c5764ee75b7b834d2da9415`; review record `tasks/agent-loop/inbox/effect-permission-member-trace-r120-review.md`, SHA-256 `ab6b4daa848196610986f62eebb7b5bbc3a32ba8bbdee0973954785b51ccc50b`.

## Fixed outcomes

1. Read the authenticated R120 source excerpts and determine the exact success-path short-circuit conditions around `same_permission.concrete.get(index) == Some(provider_family)`. Keep same borrowed record, registration uniqueness, packed permission slot, native view/member, concrete index and full family identity distinct. State what successful source evaluation implies locally, and what remains unproved about reaching that source state.
2. Inspect only existing R119/R118 Lean artifacts and derive the minimal premises needed to conclude membership from the existing `indexed_read_member` result. Decide whether this local membership conclusion can avoid first-match/`.position` correspondence while still depending on an authenticated same-record indexed-read relation. Preserve `[4,9,9]`, changed index 1→2, different-record, absent/out-of-range, R39 PRE-state, R45, R114 and parent gates as explicit boundaries. No new Lean module, assumed model, new isomorphic lemma or unapproved source semantics.
3. If the same-record Rust-to-Lean indexed-read premise itself lacks authority, report that exact blocker and end `NO_AUTHENTICATED_LOCAL_TRACE`; do not relabel a conditional Lean lemma as source closure.

## Lanes and boundaries

- Registered `researcher`, ≤240 seconds, reads only the frozen R120 source/proof/review handoffs and the exact pinned source excerpts referenced there. Writes only `tasks/agent-loop/inbox/effect-permission-consumer-premises-r121-source.md`.
- After source freeze, registered `lean_prover`, ≤300 seconds, reads that handoff plus exact R119/R118 Lean files and proof handoffs. Writes only `tasks/agent-loop/inbox/effect-permission-consumer-premises-r121-proof.md`.
- Fresh independent `compiler_referee`, ≤180 seconds after both outputs freeze, attacks missing premises, same-record identity, short-circuit behavior, duplicate/index counterexamples and scope. It returns a read-only report; primary records it at `tasks/agent-loop/inbox/effect-permission-consumer-premises-r121-review.md` because the role cannot write files.
- Primary ≤180 seconds adjudicates, updates compact state and pushes reviewed research records. Total cap ≤900 seconds; Astra 0.

No recomposition or source writes, patch application, Rust/Lean/Cargo/compiler/checker/build/test execution, environment/storage probe, cache, worktree, scratch, temp, mount or generated file. Do not read or alter dirty Rust files or quarantined paths. R111 compile gate, R39 PRE-state, R45 extraction, R114 transport, parent soundness/effect hygiene and production remain OPEN unless independently closed by authorized evidence. Only explicit R121 records may be committed/pushed.
