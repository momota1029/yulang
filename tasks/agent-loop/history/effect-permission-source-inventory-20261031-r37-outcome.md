# R37 outcome — source-use inventory correspondence

Status: **CLOSED_PASS (bounded gate)**. Luna adjudication after frozen outputs and fresh independent review.
Sprint: `EFFECT-PERMISSION-SOURCE-INVENTORY/20261031-R37`
Contract SHA-256: `33c4c4f1d60e69c11a1a082cbe10a91728888bcdcbf2e11b8f735aa5d14dc756`
Manifest SHA-256: `ca60bdfaf7a2f4e41946a3bb96cd20bd0d223be5f15820bab4843fb99e1d2dae`
Baseline: `ce922eed506e1471abe9a0f6823674da7ba55039`; R37 admission checkpoint `e706684c5`.

## Adjudicated result

**PASS.** Rust constructs a unique occurrence/index map from the retained source vector, validates every Apply-callee edge before filtering, emits direct formal uses in source-vector order, and preserves duplicate uses. It distinguishes `Err(TryReserveError)` from `Ok(None)` semantic rejection and `Ok(Some(vec![]))` valid empty inventory. Luna repaired the R35 row collection and authentication paths so this API propagates their fallible reservation errors; the earlier Option/bool wrappers remain only for the existing caller. No runtime semantics or accepted source domain changed.

Lean defines the explicit finite indexed inventory and proves checked lookup/uniqueness, all-edge validation, guard equivalence, complete ordered enumeration, multiplicity, empty success, and application to the same R36/R35 source model. All 27 theorem types and complete axiom sets passed producer and independent pinned Lean 4.35.0 stdin audits. Fresh independent review found no open blocking/major/minor correctness issue in this bounded scope.

Artifacts:

- `program.rs`: SHA-256 `d648e2f180cbe4690d70ee0813d92759929678eb10b4e0973e7b6f7833da91b4`.
- Rust handoff r1: SHA-256 `f7189a06126c9cb32d483e267d7b293c194f05cf5afc2f8bd25b66c23a7460fb` (its source hash is historical; primary allocation/authentication deltas are detailed in the stage ledger and independent review).
- `SourceUseInventoryR37.lean`: SHA-256 `4981f8c20dc5d9c932d9f4a843f2245c034daaa015e7fc7b97aa7a343bb7ea30`.
- Proof handoff r1: SHA-256 `ded40d8ce118b1403528de519d41ea6c59d7e61d514f8c4b86e1033d8e6f0054`.
- Independent review receipt: SHA-256 `a82a806fd419224285ffa19f42d043360379598966081636eeb1c22849fc6937`.

Reviewed artifacts are checkpointed in `d00417851` (`feat: prove complete source-use inventory`). Central outcome/current receipt follows in a separate exact-path commit. Inspect the full outbound range and push before reporting it published.

## Verification and limitations

Independent Lean audit used Lean 4.35.0 commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, read-only stdin under `bwrap`; final input SHA-256 `fa172640ba999ff373c314e249c9559abbaae686dacc8858264b4039c5bddad6`; exit 0, empty stderr, no diagnostics, 9.336047 seconds. All 27 theorem types and complete axiom sets are listed in the review handoff. Three audit invocations occurred; two orchestration captures were discarded, and only the final retained output counts as evidence. No proof holes or project axioms.

No Rust build, Cargo, tests, formatter, Lake build, scratch, cache, target, worktree, copy, extraction, or new environment was used. Rust compilation/execution therefore remain unobserved. `Err` models explicit fallible reservation failure; this does not prove allocator internals, timing, error identity, or survival of fatal OOM.

The R36 unauthorized broad-search read incident remains explicitly unauthorized and preserved. Independent review required no quarantined data; neither quarantined runtime path is released or read in R37.

## Open parent and runtime gates

R37 proves a finite model correspondence; it is not a mechanically verified Rust interpreter. Native root selection, Arc/HashMap internals, HIR construction, constraints, propagation, runtime Name receipt/entry/invocation, permission/Grant consumption, Catch subtraction/residual provenance, native Step/History, original Simple-sub A/B, whole-language hygiene/soundness, principality, progress, termination, and production remain OPEN.
