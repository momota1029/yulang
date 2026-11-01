# R140 — bind one successful formal constructor to ordered permission output

Status: proposed for primary admission after dispatcher recommendation.  
Parent: `YulangClosure.SourceProblem.InferenceSoundness` and its effect-hygiene H obligation remain OPEN.  
Baseline: `4c1d58a646a1101c080659ebfed6ae7862d8aded` (`origin/yulang3`).

## Objective and fixed outcome

Construct and independently review a test-only/read-only Rust candidate that binds the source annotation rows traversed by **one exact formal constructor invocation** to the ordered `FormalPermission` suffix successfully appended by that same invocation. Keep `FormalEntryPermission` as a separate root-entry output. A constructor error returns no completed snapshot. Do not infer source/native equality from a table alone.

The source traversal must follow the native constructor's accepted order: argument value, result value, argument effect row, result effect row, recursively preserving polarity and `FormalPortStep` path. Preserve row filtering, `FormalContext`, source row and concrete-member order/multiplicity. Capture the pre-call permission length and the post-success suffix from the same `State`; do not combine outputs from different calls or snapshots. Use the same complete tagged Rust `Eq` identity table for source and native identities. `SourceNodeKey` table equality is not a claim of injectivity into syntax occurrences; accepted-source uniqueness remains OPEN unless separately established.

## Governing inputs and frozen boundaries

- R137 structural constructor map: `tasks/agent-loop/history/effect-permission-hir-decoder-20261102-r137-outcome.md`, SHA-256 `82fd775010eb1b865928510bed1d34d282c0d46768f6ee93054ca0d670748231`.
- R138 failed-session publication envelope: `tasks/agent-loop/history/effect-permission-formal-publication-envelope-20261102-r138-outcome.md`, SHA-256 `2cfe94f5dd822c4df4619fa194186c2537393c1c3ed8340e244f56b6e93ac480`.
- R139 bounded review and unchecked proof status: `tasks/agent-loop/history/effect-permission-id-encoding-20261102-r139-review.md`, SHA-256 `f40a05d3c791cdf4d10c98f283938e9347a5f1dbc68e6943d70a956c86d6b508`.
- R139 source handoff, Lean artifact and outcome are historical inputs; none establishes successful source/native equality.

Read only immutable baseline blobs. Do not inspect or edit dirty diffs, quarantined paths or unrelated untracked work. No Rust production source edits, build, tests, Cargo, Lean execution, new environment or solver integration. No allocation guarantee beyond explicit `try_reserve` and checked-width errors; do not label infallible clone allocation as `EncodeError`.

## Assignments and evidence

**Rust source candidate:** Luna/high implementer; 900 seconds; exact output `tasks/agent-loop/inbox/effect-permission-ordered-snapshot-r140-source.md`. Trace the exact source constructor entry, its source-value/effect-port recursion, permission-vector before/after boundary and every success/error return. Supply a complete in-memory test-only wrapper candidate, exact source equations and dependency hashes. Compare the resulting filtered ordered rows with R136's native inventory schema. If the mapping fails, identify its first mismatching constructor branch and preserve the counterexample.

**Lean candidate:** registered `lean_prover`; 600 seconds; exact outputs `notes/theory/lean/YulangClosure/FormalPermissionOrderedSnapshotR140.lean` and `tasks/agent-loop/inbox/effect-permission-ordered-snapshot-r140-proof.md`. Prove only constructive order/filter/path properties actually represented by the candidate. Do not assume native output equality or hide a Rust-to-Lean premise in a typeclass. Account for all eight Rust identity tags, including `FormalPosition`, or label the unmatched case OPEN. No checker retry is authorized by this contract; report constructed declarations separately from checked declarations.

**Review:** one fresh independent reviewer; 240 seconds. Review the frozen source and Lean handoffs against exact immutable dependencies. Reject different-call suffixes, preorder/native-order substitutions, lost paths/polarity, root/nested mixing, unsupported injectivity, or failed-call snapshot publication.

Total envelope: 1,800 seconds. Astra, Cargo and environment probes: zero. Luna owns integration, state and Git.

## Gates and stop conditions

R140 succeeds only as a reviewed research candidate with a same-call successful suffix and matching filtered order. It does not close the original theorem, A/B, H, consumer/capture/copy/arrival correspondence or production. Stop at the first source/native divergence and record exact fields and owner. Preserve R139's Lean result as **CONSTRUCTED_BUT_UNCHECKED**; a new executable verification method requires a separate reviewed resource decision.
