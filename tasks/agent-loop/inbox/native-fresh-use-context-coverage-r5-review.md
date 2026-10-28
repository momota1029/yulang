# Independent review — NATIVE-FRESH-USE-CONTEXT-COVERAGE/r5

Verdict: **REJECT sprint acceptance; preserve R5 as provisional unchecked research and close the fixed outcome `CLOSED_INCOMPLETE`.** No reachable successful counterexample was established. Do not run R5 checks under the rejection rule.

Reviewer: `/root/native_fresh_use_context_coverage_review_r5`, compiler_referee, requested Sol/medium, observed model/effort UNKNOWN. The reviewer ACKed contract `6f488e11f0d1e7eb8d86fec5fc30e7fbca454faca6691255d11a71120ddab6fa` before any body read, then inspected frozen Rust and Lean source before producer handoffs. Read-only; no writes, Git, checker, Cargo, build, tests, Lean/Lake, or descendants.

## Findings

1. **BLOCKING — Successful native interpretation and restoration attachment remain unproved.** `run_exact_verified` establishes equality with a model `RenameRun`'s verified list, but no theorem derives the actual successful Rust driver interpretation, equality with original transitive reachability, or readback selection of every prepared image. Native interner facts from `context_keys` history and the restoration dependency/view/bound closure remain absent. Earlier restoration can execute Replay children, reuse a full relation key, and alter discharge/residual state before a later bound rereads the parent. The finite Replay/Prefix configuration has no authentic source capture, exact alias-key equality, completion, or exclusion of alternate selected images. It is not a reachable counterexample.

   Required closure: derive full successful-driver interpretation, completed source-domain equality, and actual restoration/readback attachment, or provide the exact reachable successful trace.

2. **MAJOR — Logical identity is incorrectly required to appear as a physical readback row.** `observed_context_closure` inserts `ContextId(0)` into `target_contexts`, while `CircuitEvidence::contexts()` emits allocated rows starting at 1. The predicate then requires all targets in the physical post-bound set. An identity closure `{0}` therefore fails with `ReceiptMismatch`; nonempty well-founded DAGs reach identity. `stored_targets ⊆ target_contexts` is tautological and does not repair this.

   Required closure: distinguish logical identity coverage from allocated-row coverage and require physical evidence only for nonidentity IDs, with authentic identity and nonidentity consumer specimens.

3. **MAJOR — Prepared map images are not authenticated; the required image mutation survives.** `context_map_coverage_closed` never reads `map_values`. Replacing an image with the foreign ID selected by the mutation helper leaves all predicate conditions unchanged, so `context_coverage_rejects_authentic_mutations` returns false for an otherwise eligible route. Key/image sets also discard associations, so swapping images between keys preserves both sets; key mutation exercises one arbitrary HashSet key rather than every required key.

   Required closure: retain and authenticate key→image associations against unchanged construction/readback evidence, enforce observation of each prepared nonidentity image, and enumerate all key/mutation categories non-vacuously.

4. **MAJOR — Readback observation conflates mutable effective roots with retained raw roots and loses bound ownership.** Final admission roots come from `relation_context` (discharge residuals), but `retained_input` traverses raw `relation.key.context`. Discharging an attached mapped Prefix to identity can make the observer reject even though raw evidence retains the Prefix and weight; that is not proof of image omission. Root-set equality plus relation count loses source-bound multiplicity and association (for example prepared `[a,a,b]` versus observed `[a,b,b]`). The predicate does not use `source_bound`, antecedent, or mapped-relation ownership to distinguish this.

   Required closure: retain each original bound identity, prepared image, mapped relation, and later effective root independently; authenticate admission ownership from cause data and distinguish root changes from image loss.

5. **MAJOR — Required authentic specimens are absent or unestablished.** Display/where requires shared children and weights but does not establish discharged-parent temporal restoration. Identity asserts completion only. No dedicated successful-empty specimen exists. `context_completion` is assigned Partial for a pause but no test reads/asserts it; the handoff leaves the authentic pre-bound pause as TODO. Required identity, empty, pause frontier/continuation, shared DAG selected child/weight, and discharged-parent restoration cases are not all demonstrated.

   Required closure: explicit authentic module/local cases with assertions over the actual relevant construction, completion, restoration, and readback states. Execution requires a subsequently accepted packet.

The source footprint analysis usefully narrows the mechanism: Context/full relation-key interning reuses or appends; inspected discharge writes preserve existing raw constructors and keys; Replay can reuse relation identities and `use_origin` is absent from `RelationKey`. It does not resolve reachability or attachment.

Original inference-soundness quantifiers and shared source witness remain intact. No whole effect-hygiene, A/B, principality, termination, executor, or production theorem is closed. The selected effect policy remains unchanged. All 31 authored Lean theorem terms are **UNCHECKED**; kernel acceptance, printed types, and complete axiom audits are **NOT_RUN**. The core artifact is comment-only. No `sorry`, `admit`, project axiom, or checker bypass was observed; this is not an axiom audit.

## Authenticated artifacts

| Artifact | SHA-256 |
|---|---|
| Contract | `6f488e11f0d1e7eb8d86fec5fc30e7fbca454faca6691255d11a71120ddab6fa` |
| Rust source | `7fd3e16f2a6f856b925e2675d8a485fc25b90775a4b5a81f39d027c71874ef4a` |
| Rust handoff | `ef7589f15d1a163c994a792362491ca011976cf3729bbe09a42a439d16a8f9a5` |
| Lean source | `3878c3c4039f33eb938bc2450f9ae5ee5329309f5ac711891869e9986c773146` |
| Proof handoff | `0d4ea0a63bfcd7b41e076b2e0afd9c29715fb3908615e15e06b98dbdd0acb0cf` |
| Core artifact | `af8b87e064db2063cb2f2561f88986102271bc44a3e94e12e6df5759a02ea5d6` |
| Core handoff | `f3668e20dca09c53662babf263a15c4d1dc7e9b3869aed61fbeed316966219c0` |

All explicitly listed Rust dependencies/manifests, Lean inputs/configuration, seven authority/correction pins, and eight R4 pins matched. The baseline scheme hash matched `31ae5b9466a0f7bbd501c81e4401049ad9782636ba57ed89e8232e9149e8b707`; executable changes in the isolated diff are test-gated.

**STOP.** One read-only verdict. Parent, native, effect, and production gates remain OPEN.
