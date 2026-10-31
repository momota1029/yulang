# R55 independent review — BLOCKING

Assignment: `EFFECT-PERMISSION-SOURCE-INTERNAL-CONTEXT/20261031-R55`  
Reviewer: `/root/r37_inventory_review`  
Both authors were STOPPED before review. This report records the complete returned findings; the reviewer made no writes.

## Findings

### B1 — BLOCKING: Internal construction block is in the wrong constructor

`OwnedResidualProjection::capture` begins at `candidate_receiver.rs:1697`. Lines 1716–1759 construct `internal_incidence`, `internal_root_join`, and `internal_function_witness` inside that R54 constructor. The block references `batch` without a binding there. `SourceInternalProjection::capture`, beginning at line 2081, uses those locals in its initializer around lines 2156–2157 and its `internal_incidence` field, but binds none of them.

This is a lexical scope/name-resolution failure. It also makes the existing R54 constructor depend on successful Internal incidence extraction. Minimum repair: move the complete Internal construction block into `SourceInternalProjection::capture`, after its exact `batch` binding and before its initializer. Preserve the unique registration→LambdaRecipe→root-component join and actual Function-child validation. Adding a `batch` binding to the R54 constructor alone does not repair the cause.

### B2 — BLOCKING: permission referenced before binding

In `SourceInternalProjection::verify_owner_round_trips`, line 2370 reads `permission.entry_effect`, but `let permission = &self.internal_incidence.permission` occurs at line 2375. The earlier permission-loop binding is out of scope. Bind the selected incidence permission before the Function-child comparison, or access that exact field directly.

These are the two established source blockers. This static review is not a completeness certificate for compiler diagnostics; no build or type-check was run.

## Frozen hashes

| Input | SHA-256 |
| --- | --- |
| R55 contract | `6583202e628a854dfeade9834788de76f2fad8422335383dd54884e9c35646bc` |
| Admission | `cc5e0a773bdd2b60f43eb3dcc79b32485f86b430043f3f71df30247d37348f59` |
| `candidate_receiver.rs` | `befdb77ea88becca357f83914f61ade7e09bf93bd33e5adb2ee017d0e51a76aa` |
| `candidate_effect.rs` | `75267bd1a195121ca79addb62b2a446a4b1b26afcc11e8c70aa1fa732c9e2909` |
| Rust handoff | `5ae6b5a37a88b3d02099352a9bb0c77ad4392cba13e306a86ec9c81ec22f936e` |
| `SourceInternalContextR55.lean` | `7aaecdd3d358d769123f00acb4b19b4d7d61ccfef98fee4eb53179da4a105123` |
| Proof handoff | `bc849f0e95533a5e231358fee503da4e556e8422b4738de4d48b962004648c47` |

All match the frozen submission. Read-only context, scheme, source, call, and four specified HIR-source hashes also match the contract pins.

## Source inspection and attacks

- **Foreign HIR/state:** the projection starts from the existing R54 owner. HIR lookup uses that batch's `hir_for_source_root`; LocalSource round trips check the HIR Arc and source pointers. Existing `lib.rs:1582` verifies actual HIR root ownership. The batch already retains HIR Arcs, so no producer change is needed.
- **Duplicate owner/lambda:** the complete registration inventory is captured before selection. The submitted code rejects repeated `(owner, lambda index)` coordinates.
- **LocalSource versus schedule:** registration validation uses the retained LocalSource expression at `registration.lambda`, checks its Lambda constructor and parameter identity, and separately retains execution schedules. The Lean fixture distinguishes source Lambda occurrence 17 from schedule 999.
- **Catch order and identity:** construction borrows the original Catch expression, scrutinee, and ordered arm slice. Selected operation source/declaration joins use exact identities and Arc equality. Existing `assemble` admits only its bounded two-arm source shape; no general Catch-domain completeness follows.
- **Parameter versus registered root:** the intended construction takes `registered_root` through the unique LambdaRecipe and exact `root_component`, retaining the parameter `native_root` separately. The distinction is sound in design, but B1 prevents the submitted constructor from compiling.
- **Complete inventories:** owner vectors are enumerated before filtering, including permissions, registrations, recipes, origins, routes, and admitted semantic facts. Owner-index round trips reject omissions from those captured vectors. Historical producer completeness is not established.
- **Function and route:** inherited `lib.rs:18270` authenticates the exact DefinitionUse, unique Internal route, admitted slot-0 fact, unique constructor/recipe, source Lambda, slot-2 fact, and actual positive Function argument-effect child. The new validation intends to retain these joins; B2 breaks its implementation.
- **KnownUnmatched:** no Forward-decision implementation changed. The optional observer query does not participate in ordinary inference. Lean Forward retains its independent provider/native-reader premise.

No additional established correctness finding arose from these attacks.

## `candidate_effect.rs` delta

The reviewer reversed the submitted changes in memory: restore private visibility of `FormalEntryPermission` and its fields, then remove the new feature-gated `owned_projection_entry_permissions` iterator. The reconstructed bytes hash to the exact admitted dirty baseline:

`2a86befde95581decef8fe01698961062bd22388cff2459e9611570a20b9fba3`

Thus the R55 delta is limited to visibility and an unfiltered borrowed iterator. Pre-existing dirty contents are preserved.

## Lean audit and theorem boundary

The actual definitions and theorem bodies were inspected. `sourceInputs` constructs R39 readers from primitive formal/source/owner records. `internalInputs` constructs R45 readers using unique recipe/component, plan, fact, and TermView lookups. Its `registeredRoot` comes from the LambdaRecipe component term, not `Formal.nativeRoot`. `catchInputs` constructs R49 Catch and operation readers from complete ordered primitive arm records; an unresolved unselected operation arm makes `catchRecord` unavailable.

`constructed_internal_application` assumes successful R45 extraction on constructed inputs and derives actual Function-child/raw-entry equations; the concrete primitive fixture separately discharges that extraction. `constructed_known_unmatched_forward` retains selected-arm reads, the independent provider `sourceOperation` read, declaration inequality, and an independent `providerCandidate` result. `withSource` updates only the source/selection fragment of an independently supplied parent context. No theorem constructs a complete Rust-derived R49 Context or R50 interpretation.

### Complete axiom census

Namespace prefix: `YulangClosure.SourceInternalContextR55.`

**Exactly `[propext]` — 19 roots:**

`native_reader_equations`, `local_source_lookup`, `source_lambda_reader`, `complete_permission_inventory`, `catch_reader_equation`, `resolved_operation_reader`, `constructed_internal_characterization`, `constructed_internal_application`, `constructed_known_unmatched`, `concrete_existing_internal_extraction`, `concrete_parameter_and_lambda_roots_distinct`, `concrete_complete_fragment_and_duplicate_formal_rejection`, `concrete_same_native_parent_application`, `concrete_missing_duplicate_internal_rejected`, `concrete_owner_index_and_raw_identity_rejected`, `concrete_missing_foreign_native_reads_rejected`, `concrete_complete_catch_and_arm`, `concrete_source_classification_application`, `concrete_missing_reordered_foreign_source_rejected`.

**Exactly `[propext, Quot.sound.{u}]` — 2 roots:**

`formal_reader_equation`, `constructed_known_unmatched_forward`.

**No axioms — 1 root:**

`concrete_unresolved_unselected_arm_rejected`.

All 22 source roots, full printed types, and axioms reconcile in source order. No final warnings, `sorryAx`, project axioms, `Classical.choice`, or native-evaluation dependency appears.

## Archived receipt verification

All six archived stdin/stdout/stderr payloads were decoded in memory; recorded byte counts and hashes match. Audit4 remains rejected failure evidence. Earlier accepted but source-inaccurate converters remain historical evidence, not final correspondence evidence.

Audit6 contains each complete current module exactly once, removing only local imports: R39, R45, R47, R48, R49, and R55.

- Input: 147755 bytes; SHA `5ba1a0a818dc64256213a23288d00b47584422f9e7070b468752e2b7bc1ce980`.
- Stdout: 56588 bytes; SHA `c4725bdb6dc45206be6fae7fd4c064863493932e377f46881f1d8b99b3287c71`.
- Empty stderr SHA: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- Archived exit 0, wall 6.090806426000199s, peak RSS 897136 KiB.
- Six-audit total wall 51.19317017299909s, maximum RSS 952836 KiB.

These authenticate producer checker receipts; the reviewer did not rerun Lean.

## Adjudication and STOP

**Submission BLOCKED by B1 and B2.** The Lean bounded fragment and final receipt audit pass within their explicit conditional scope.

Full Rust-to-Lean field encoding, successful native extraction, full R48/R49 candidate extraction, complete Context/R50 interpretation, R51 primitives, runtime, original parent A/B, soundness, principality, termination, complete hygiene, and production remain OPEN.

Reviewer STOPPED; writes STOPPED. No builds, tests, checker reruns, Git, scratch/cache/worktree, or quarantined-file access occurred.

## Lexical repair delta re-review

A bounded repair was admitted after the initial review. The delta reviewer found:

- **B1 CLOSED:** the complete Internal construction block moved into `SourceInternalProjection::capture`, after owner/batch bindings, and was removed from `OwnedResidualProjection::capture`.
- **B2 BLOCKING:** `verify_owner_round_trips` still reads `permission.entry_effect` at line 2371 before its method-local binding at line 2376. A capture-local alias does not bind the name in this verifier.

The reviewer reconstructed the rejected receiver SHA exactly: `befdb77ea88becca357f83914f61ade7e09bf93bd33e5adb2ee017d0e51a76aa`. The repaired attempt contained only the block relocation and capture-local alias substitutions; selections/checks were otherwise preserved.

Re-reviewed hashes:

- Receiver: `7b0698e6ac26ec1ba983d83006ef14d14a600b37e805ec0455120f24e2f6f224`
- Updated Rust handoff: `db9e9a2fcd545502f501e103d40a66fa41343c7906e44efca4e1d72087f48b4f`
- Unchanged `candidate_effect.rs`: `75267bd1a195121ca79addb62b2a446a4b1b26afcc11e8c70aa1fa732c9e2909`
- Unchanged Lean module: `7aaecdd3d358d769123f00acb4b19b4d7d61ccfef98fee4eb53179da4a105123`

The dispatcher specified a one-line alias move, capped by the original 180-second repair allowance. An authenticated time audit measured 172 seconds charged from the RUNNING receipt commit timestamp and 8 seconds remaining. The author stopped without further edits, reporting that 8 seconds was insufficient to apply the exact move safely. R55 therefore remains BLOCKED; the repaired receiver is not accepted or staged as a coherent source checkpoint.
