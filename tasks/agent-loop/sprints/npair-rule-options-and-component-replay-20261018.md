# Sprint `npair-rule-options-and-component-replay-20261018`

Status: AUTHORIZED successor to rev6 on 2026-10-18. Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN; preserve original quantifiers, source domain and the same fixed `c`. Theorem closure remains 0 and production remains unauthorized.

## Outcome

Advance both rev6 findings in parallel: (1) compare complete, source-owned candidate rules that could supply the original fixed-c Written `s1,j` premise at the actual complete Operation output, with accepted-language effects explicit and no rule adopted; (2) repair the replay fixture's `ComponentIdentityExhausted` failure by tracing the owning capacity boundary and producing the smallest real Module/Local two-sibling source fixture that fits existing limits. Do not change checker semantics or relax assertions.

### Proof/design lane — fixed-c rule completion options

Parent/source gate: `NPAIR-OP-SOURCE-WITNESS-20261017` (`?e_Op`), whose rev6 source-owner obstruction was independently reviewed CLEAN. Inputs are the active rev6 contract's 11 exact pins, plus supplier theory SHA `bfb632001946a5f425423478d4f6294ecc6caffbf75cbb2ed251e453be9d1e71`, supplier handoff SHA `07e03714f49b471a0627f67c198e36b88812cfcaab0f2c2615576361e3263fb9`, independent review CLEAN, and the adopted NPAIR construction.

Exact source pins (must all be revalidated before authoring):
- `notes/theory/2026-10-18-original-c-complete-output-elimination.md`: `0ab3061c26b1b5b081dcf931fb8b616d77b2d17a34ec7fe48f277b740f101b67`
- `notes/theory/2026-10-18-npair-fixed-c-source-selection.md`: `b3e8fb90bb425901c416ec4aeadcf141820a447fdb699c788897dd1afc440ba8`
- `notes/theory/2026-10-18-npair-fixed-c-source-selection-adversarial.md`: `ebfe5cc583851953f9253996774993c148b357a758446d020e5385cd483b61b0`
- `notes/theory/2026-10-16-choose-source-declaration-initial-installation.md`: `b27eed06d5a3eae63b2dfacb62a1f76d01b71f92a478402b452cd8a3b3346471`
- `notes/theory/2026-10-17-adopted-negative-pair-construction.md`: `6a3c6b5754448b38430ee368feb52d87ebd38c1b7050c3b33652132ead5f0fb2`
- `notes/theory/2026-10-16-choose-producer-full-source-certificate.md`: `5abbe5f849cbe3f92ba743e0a51c5928350cead62ed8d688766895c2035e1971`
- `notes/theory/2026-10-17-choose-operation-source-instantiation.md`: `6075d45f38787bd5a981a2da177504450239a05e6dbec6f19ccf526ca0d4a110`
- `notes/design/2026-10-05-source-contracts-and-common-allowance.md`: `1acc5bd069d14b6493cd279e54ca7db6d600347431fdac62f8fd199bdb32d186`
- `notes/design/2026-10-18-npair-native-introduction-correspondence-proposal.md`: `45c8331a5d76ff1701ee5f5aacec710a13bb0088495b1c682ae6e4024dfef9eb`
- `notes/design/2026-10-18-npair-source-admission-proposal.md`: `398b4f8683503d41e79d4d09b7a0a9591161a5673d48338c224037fae26d3158`
- `notes/progress/2026-10-05-source-contract-conditional-proof.md`: `c3b24cf9074d2557c078aa0f41a003737a42cdc52463beb72bad70b845b5b693`
- Rev6 supplier theory/handoff: `bfb632001946a5f425423478d4f6294ecc6caffbf75cbb2ed251e453be9d1e71` / `07e03714f49b471a0627f67c198e36b88812cfcaab0f2c2615576361e3263fb9`.

Produce a compact comparison of at least these routes, adding another only if grounded in the original rules:

1. An original-constructor interpretation that derives the existing fixed `c`'s occurrence at actual `out(d_A).Written[s1,j]` from already-present `Prim_alpha/T_alpha`, `A_decl`, and complete `Sigma.Lambda` evidence. State the exact identity/lineage witness and all R/W/Z, guard, world, scope, license, dependent-telescope and future-duty obligations.
2. A new source-owned complete-output constructor/bridge that explicitly links the parent's fixed `c` to the output field while preserving all original indices. Mark as a candidate semantic addition; enumerate every new admitted/rejected program and identify whether this preserves or expands the old theorem's premise.
3. The already recorded SWR1/OC interpretation only as a comparator, explaining why `c_star` without a proof of equality to original `c` does not discharge `?e_Op`.

For each viable route, state source-to-typed-observation meaning, consumer, consistency with the adopted complete typed-observation/independent-admission decisions, exact extra premise, accepted-language effect, a full same-c construction or a genuine admitted falsifier, and review/approval needed. Do not promote a proposal to authoritative semantics or claim theorem progress from a new rule alone. The user's prior authorization covers drafting and independent review of bridge-rule proposals; explicit rule adoption remains separate unless a matching existing approved answer is located and validated.

Exact write paths:
- `notes/design/2026-10-18-operation-fixed-c-rule-completion-options.md`
- `tasks/agent-loop/inbox/20261018-operation-fixed-c-rule-completion-options.md`

Author budget 600s, Astra0, no descendants. Fresh independent `architect`/compiler-semantic review 180s after freeze; primary integration 60s. No code, tests, Cargo, runtime, or Git.

### Implementation lane — replay fixture component budget

Parent implementation evidence remains provisional. Rev6's CLEAN-reviewed fixture source reached the filtered test but failed before route assertions: `ComponentIdentityExhausted` at `candidate_scheme.rs:2236`, when unwrapping `analyze_source(&text)`. Exact receipt is `tasks/agent-loop/runtime/20261018-replay-fiber-consumer-r6.helpers.meta.json` (stdout SHA `714c7c281cf95007a7db4834e7289e0ec2929659857a7ee4f898ece0a5f1223d`, stderr SHA `770caf82e9bcb1ee85aee5e39d89b5b1d3eb7095e6516671748d14c1ff70b1b3`, metadata SHA `7b798f261a5278aa73c19dadb6cb07c1c03975125d38aaaf4085aafb9cda58f1`). Commands 2 and 3 were not run. Rev6 runtime sequence is closed; this successor authorizes a new source-driven attempt, not a retry of the failed command.

Exact implementation baseline pins: `candidate_scheme.rs` `b0c0c27dd6eb5b67a204478b1cd2d5011b40bf0c5270562716578ffdaa746df8`; `candidate_context.rs` `67f831ac89800e065684cb3358e5b456d7e1b6e0b20f7cb9f3d4e1fc2f0e2b1a`; `shadow_apply.rs` `396b288b53be76631cd0a5d748b7f19c6d3a73fc42e35001c503bed468ecc996`; `src/tests/candidate_graph_call.rs` `7ff60ecb30e3815ba703463c87f053d66bf2d0c1833784dc64f993203fcdf5ef`.

Audit the component-identity allocation and exact `analyze_source` path, determine which fixture declarations/uses consume the exhausted IDs, and minimize the source while retaining all existing assertions and the actual Apply → Function lowering → Module/Local owner → two sibling Replay → consumer/four-port path. Keep both module and local positives and all negative mutation/restoration controls. Do not increase limits, alter checker/solver logic, suppress errors, weaken assertions, or change expected outputs. If the intended two-sibling trace is impossible under the accepted source and existing capacity, freeze the exact owner-level obstruction for Luna; do not improvise semantics.

Exact write paths:
- `crates/yu-solver/src/candidate_scheme.rs`
- `tasks/agent-loop/inbox/20261018-replay-component-budget-impl.md`

Author budget 300s (source/capacity audit then one fixture-only edit/freeze), Astra0. Fresh independent regression review 180s. Only after CLEAN, Luna may run the exact three commands once, sequentially, each capped at 120s; first nonzero stops all remaining commands and no retry is allowed in this contract. Output prefix: `tasks/agent-loop/runtime/20261018-replay-component-budget.{helpers,graph,example}` with full stdout/stderr and UTC/monotonic/exit/byte receipts. Runtime allocation 360s; primary integration 60s. No author tests/Cargo/runtime.

Commands after review:
1. `timeout 120s env YU_CALL_REPLAY_OBSERVER=1 cargo test --offline -p yu-solver --features shadow-apply-candidate authentic_demand_capture_tests --lib`
2. `timeout 120s env YU_CALL_REPLAY_OBSERVER=1 cargo test --offline -p yu-solver --features shadow-apply-candidate candidate_graph_call --lib`
3. `timeout 120s env YU_CALL_REPLAY_OBSERVER=1 cargo run --offline -p yu-solver --features shadow-apply-candidate --example research_scoped_formal_replay`

### Resources and stop conditions

Fresh tranche: proof/design 840s (author600, review180, integration60); implementation 900s (author300, review180, runtime360, integration60); total1740s. Prior cumulative ceiling10260s closed at charged6977.385s and expired3282.615s; no rollover. New cumulative ceiling12000s. Astra0; at most one heavy process. No reserve. Failure, dependency drift, a new semantic decision, or a genuine owner-level capacity obstruction stops only its dependent lane. A new candidate rule remains unadopted. Parent closure stays0 unless the full original theorem is independently established.
