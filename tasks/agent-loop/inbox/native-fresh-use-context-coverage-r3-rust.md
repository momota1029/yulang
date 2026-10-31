# NATIVE-FRESH-USE-CONTEXT-COVERAGE/r3 Rust handoff

Contract: `tasks/agent-loop/sprints/native-fresh-use-context-coverage-20261028-r3.md`, SHA-256 `d6fc97fde87e8c8a0c0eb0cb8afb140029a0428aedcde6f82b1f162c4bc21725`.

Amendment 01: `dc7389b53d773c4c742af556f4b6d5123821df84bdddb7df97afd7a0ac549fc4`. It did not change this worker's source dependencies, scope, or leases. Requested role/model/effort: implementer, Luna/high. Observed runtime model/effort: UNKNOWN. Assignment ended at its finite 500-second bound; no escalation or transfer occurred.

## Frozen implementation

Exact source output: `isolated/native-fresh-use-context-coverage-r3/crates/yu-solver/src/candidate_scheme.rs`.
Frozen source SHA-256: `9279fcb9bd1580655b7db4541c27338cc3a48ac711f06197cd3ee250b5315923`.

The source adds test-only `ContextMapCoverageObservation` instrumentation to `FreshUse`. At preparation it captures every pre-rename `relation_context` root independently from `context_remap`, and records the source Context/weight closure using the pinned `context_payloads` traversal. After rename it records actual map keys, values, and weight-map keys. At each FreshUse bound admission it records the newly read `relation_context` root; the existing map lookup already returns an error if that root is absent.

At completed module and local FreshUse consumers, the test-only path seeds pinned `State.retained_input` with the graph's relation roots. It derives Context constructors and their child/weight closure from the borrowed `CircuitEvidence.contexts()` and `.weights()` observations, including shared children, identity, Replay, and BothFromRight nodes. It rejects a non-exact source Context key domain, missing source weight mapping, an admission root absent from the map, or any target/child/weight not observed after bound completion. Empty/no-relation routes have an empty exact domain. A suspended pre-bound local route has no completed readback marker, so it cannot be counted as covered.

The test-only mutation fixture covers deleted and extra Context keys, changed independent roots, omitted target/shared-child observations, missing weights, a later admission root outside the map, identity, and empty roots. Cargo/tests/builds were not run; these checks remain unexecuted pending frozen independent review acceptance.

## Source evidence and limits

Reused r2's independently reviewed existing-API route: `State.retained_input` exposes borrowed Context/weight observations; its incompleteness flags belong to broader certificate duties. Reused the pinned rename traversal and FreshUse transport construction. Rejected r1's unconditional validator and r2's blanket `NO_SAFE_CODE_SLICE` conclusion.

On the pinned source path, preparation reads `relation_context` before map construction (`candidate_scheme.rs`, former line 4422); each later bound admission re-reads it (former line 4701), then requires the resulting root in `context_remap`. Therefore an intervening discharge that changes the root to an unmapped residual fails before that bound is admitted. This patch records admission roots and does not assume stability. It establishes coverage only for completed routes passing that existing fail-closed lookup and the post-bound readback check; it does not prove `relation_context` stability across restorations.

Parent/source/native correspondence is limited to the concrete path: captured graph bounds with relation IDs -> independently read source Context roots -> rename traversal/map -> roots consumed by each FreshUse bound admission -> borrowed post-bound dependency closure. This does not authenticate payload transformation, candidate-map constructor selection, Contribution/View identity, source semantics, or the returned root. It is not a full FreshUse validator, root-image theorem, parent theorem, or production authorization.

The observation is `#[cfg(test)]` only and provisional. If primary review accepts this slice, Luna owns cleanup or retention when integrating the next gate. No other paths were created or modified; no Cargo/Lean scratch or generated outputs were created by this worker. No Git operation was performed.

## Review state

Independent review and all executable checks remain pending. The implementation is not self-certified.
