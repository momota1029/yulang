# R42 independent review — bounded PASS

Sprint: `EFFECT-PERMISSION-NATIVE-INCIDENCE/20261031-R42`, contract SHA-256 `ec6a621e575b0406e6722de87c6bb021c856c38bb4033aa2ce7750fd93e21e28`.

Reviewer `/root/r41_independent_review` was not an R42 author. Review was read-only; changed paths none. The live roster confirmed both R42 authors completed before review. No build, test, Cargo, Lake, Lean/checker invocation, scratch, cache, target, worktree, environment, or descendant was used by the reviewer.

## Source trace

At `candidate_scheme.rs:453–494`, the adapter selects an incidence from the route's retained records, requires a positive graph Function, child ordinal 1, its exact child node and graph-row coordinate, checks the same route's mapped `RowKey::Effect`, and reads both native Terms through the same route's retained `terms`. It calls `BranchTermArena::term_view(function)` and compares the actual positive Function `argument_effect` field with that reconstructed child Term. The emitted certificate carries the registration/Lambda labels, mapped row, cloned route `DefinitionUseId`, and that FreshUse's `context_use`. Missing coordinates, wrong node kinds, lookup errors, foreign arena handles, and mismatches return `None`; routing and inference are unchanged.

The pinned accessor is substantive: `term.rs:856` reaches `lookup(term).map(TermNode::view)`, lookup at `:831` checks arena branding, and `TermNode::view` at `:279` exposes stored positive Function fields. The adapter adds no retained allocation; certificate clones share existing `Arc` backing. No partial certificate is published.

Dirty-baseline isolation was independently verified in memory: removing only the adjacent R42 certificate declaration and adapter, including insertion whitespace, reproduces exactly the admitted `candidate_scheme.rs` baseline SHA-256 `3cd9dd2d0f55412636dc88bc658d7cfbc23aad6304b90f2ba95247f8d58e1d22`. All pre-existing dirty bytes and committed R41 code remain.

## Proof audit review

The reviewer inspected all eight actual theorem declarations, proofs, complete printed types and recorded transitive axiom sets. No checker was independently rerun, as assigned.

| Theorems | Complete recorded axioms |
|---|---|
| `extraction_iff`, `accepted_fields`, `reject_mismatch`, `accepted_r41_image`, `shared_images_distinct_labels`, `shared_native_witness`, `foreign_and_native_mismatch_witness` | `propext` |
| `constructed_entry_to_native` | `propext`, `Quot.sound` |

The producer's pinned Lean 4.35.0 stdin audit recorded exit 0, empty stderr, and input SHA-256 `10764f9143e7abe94fab29e3d96863a323a283cc2a211740140bc5f1e51743fc`. It is producer execution evidence, not an independent rerun. `constructed_entry_to_native` preserves R39 validation and nonempty permission premises and composes R41 with the same permission witness. Successful extraction and exact lookup/image equations remain explicit hypotheses; the finite `Reads` functions and richer source label are not proved Rust instances.

The shared-image witness uses Function node 2, child node 7, row 5 and retains separate registrations under identical native images. Foreign definition-use/context and mismatched native-field/child probes are rejected in the model. Rust emits its own route identity; applying a certificate to a different use still requires identity checking. The generic Lean `Row` omits Rust's stronger effect-row-kind guard.

## Workflow deviation and adjudication

The proof handoff discloses two startup commands, `lake --version` and `lake env lean --version`, which the R42 contract prohibited. This is a **minor procedural nonconformance**, not an established semantic defect. No evidence indicates a build or cache was created, and no claim is made that Lake was never invoked. The primary records and accepts this deviation for this bounded research packet; future packets retain the no-Lake rule from process start.

## Frozen identities and limits

| Artifact | SHA-256 |
|---|---|
| `candidate_scheme.rs` | `c14f6cecb38fbf54b15e808f7385d9782dec1a784a12eac1315e1c32becd8429` |
| `NativeIncidenceAdapterR42.lean` | `61bb9ced2a80a75c2e952c3f5198a36ad7b9ae10f06df1a7996d38851107d4d6` |
| Rust handoff | `b31bbb2128c54216871f02c7750cc8e9524c8e08323eab976f2fb3bfe8809c26` |
| Proof handoff | `4fe33969962148e7483c6d90d57adcc81f4df43a274fd09d2e92c6d50e49d70a` |
| `term.rs` | `d253cd9a77ad91c523b413b25a503ef0c6bef47ee4b1f5b8492766531fe493a1` |
| `lib.rs` | `b1dac8bd244e282ff42a2d580e237393153f9b912c6ac0adf110367def5c79ce` |
| `candidate_context.rs` | `030fcb4b6571c0db8a670d12d8a67fe8fcf465484502fe5b11b6d057e8026c38` |

Bounded PASS covers static native extraction correspondence under explicit source projection premises. Mechanically verified Rust execution, full rich-label realization, route availability/completeness, provider arrival, permission consumption, Catch/residual subtraction, original A/B, whole-language hygiene and production promotion remain OPEN.

Reviewer STOPPED. No writes, Git operations, builds, tests, checkers, scratch, caches, targets, worktrees, environments, or descendants.
