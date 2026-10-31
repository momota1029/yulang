# R73 independent review

**Verdict: BLOCKING — the frozen Rust submission calls a nonexistent `ConstraintStore` method.** The finite Lean owner/replay construction has no additional correctness finding within its explicitly stated model. The combined R73 gate cannot pass with the frozen Rust bytes.

Reviewer: `/root/r73_review`, fresh independent compiler review. Review remained read-only; this report is persisted by the primary because the reviewer role returned it inline. No author contact, descendants, tests, builds, Lean/Lake commands, or Git mutations occurred during review. The reviewer returned STOPPED / WRITES STOPPED; the live roster was synchronized after completion.

## Blocking Rust finding

At `crates/yu-solver/src/candidate_receiver.rs:1058` and `:1573`, new expressions call `hir_for_occurrence` on `ConstraintStore`:

```rust
session.store.hir_for_occurrence(occurrence.occurrence)
store.hir_for_occurrence(cause_occurrence)
```

The second `store` is bound from `&self.session.store` at line 1523. `ConstraintStore` is declared in `crates/yu-solver/src/lib.rs:3386` and its implementation begins at line 3444. That implementation defines `require_owned` at line 3887, but has no `hir_for_occurrence`. The only solver definitions are methods on `FrozenInferenceData` at `lib.rs:7787` and `InferenceSession` at `lib.rs:20350`. No applicable trait or deref adapter supplies the method. The reviewer did not run a compiler; source inspection shows these calls fail Rust method resolution with `shadow-apply-candidate` enabled.

Minimum closure: resolve the artifact using the actual `ConstraintStore` admitted inventory, or add an explicitly leased store-owned accessor. Preserve `require_owned`'s indexed lookup plus inventory fallback, complete artifact identity, and the retained artifact coordinate. Replacing the receiver with an `InferenceSession` lookup alone is insufficient without proving correspondence to the exact `store.hirs` inventory. The Rust handoff must be corrected to describe the repaired lookup. Freeze repaired bytes and obtain independent delta review; Rust compilation remains outside this review authorization.

## Lean result and R72 repairs

The R73 Lean finite model has no additional correctness finding within its stated boundary.

- `InputChecks` asserts `componentPositions = componentRows.zipIdx.map (fun row => (row.1.1,row.2))` before replay. The exact equation and duplicate/reorder rejection attacks are present.
- Experiment, completed-view, and HIR artifact identities are distinct. `decodeOwner` selects the view, checks its experiment pairing, selects the experiment rows, validates readbacks, then calls `decode`.
- Readbacks compare complete ordered facts, provenance, and both representative lists with the selected owner rows. They no longer authenticate an owner by agreement with independent free mirrors.
- `requireOwned` is membership in the admitted artifact inventory, matching the extensional `ConstraintStore::require_owned` fallback semantics and `HirModule::owns_occurrence` full artifact identity. It does not impose global artifact uniqueness or conflate artifact identity with experiment identity.
- Foreign-view rejection occurs before provenance processing; the empty-provenance shared-artifact attack exercises the owner boundary.
- Complete returned-field checks preserve provenance multiplicity, endpoints and order. `accepted_competitors` preserves complete ordered competitor lists and reader results.
- `owner_r66_same_witnesses` applies the existing R71 theorem through the same unchanged source, native, request, genuine R66 `Root`, use/lambda identities and request-coordinate premises. It does not construct the `Root`.

The finite `same_fact_distinct_occurrences` theorem is a structural example, not a successful reifier fixture; the substantive preservation evidence is the complete readback equation, R71 returned-field equations and R67 competitor preservation. No further missing attack was found that invalidates the bounded finite result.

## Frozen inputs and retained Lean audit

All five assigned frozen hashes matched:

| Input | SHA-256 |
|---|---|
| R73 contract | `4a5f60480983ee6303125651d1e9a059e5b6dccef95f6f0b61dec278d06a9c55` |
| Rust receiver | `eb35c73ead829ed439a347d3cb665d52d3aa4b45b242c1155cfd4377a68d6415` |
| Rust handoff | `6e2e7e1961ed4f0a22e8615bbdf48e932e05d163b72ce304ef0b3adb5eca40f1` |
| Lean module | `afed53ee5ebb82bbe87c171c6ac2808919976046df4cb2e0fdeb774f618a6e87` |
| Proof handoff | `44bb2f9cbaea9a641f01cc9402d9383da2fd703a5d5e39dd653b5f94c9081a53` |

All 43 unchanged manifest entries matched; the receiver's baseline Git blob matched the 44th input pin. The reviewer decoded the four retained compressed stdin receipts in memory without execution or scratch writes. Input/stdout hashes matched their receipts; exits were `0,1,1,0`; failed diagnostics and `sorryAx` recovery output remain retained. Probe 4 contains the exact final Lean source body. Its dependency-prefix hash is `ad8bb292b45eb6d2fc43a05e6421fe513af733ddfb78c87f86b19dd64df1f3fe`; prefix comparison found pruning of theorem/fixture material, not replacement of semantic definitions or constructors.

The final source has 29 theorems, matching 29 queried theorem types and 29 transitive axiom reports. The final output has no errors or `sorryAx`; no theorem uses `Classical.choice`, project axioms, or proof holes. Axiom inventory:

- `propext` only (17): `term_coordinate`, `accepted_package_fields`, `accepted_order_and_endpoints`, `accepted_component_positions`, `positions_mismatch_rejected`, `foreign_occurrence_rejected`, `owner_selected_readbacks`, `foreign_view_rejected`, `substituted_readback_rejected`, `admitted_occurrences`, `shared_artifact_does_not_identify_experiment`, `duplicated_positions_rejected`, `reversed_positions_rejected`, `duplicate_component_rows_rejected`, `reversed_component_rows_rejected`, `empty_provenance_shared_artifact_foreign_view_rejected`, `any_substituted_owner_readback_rejected`.
- `propext`, `Quot.sound` (11): `namespace_identity`, `accepted_replay`, `finite_decode_replay`, `accepted_all_return_fields`, `accepted_table_fields`, `accepted_r66_same_witnesses`, `accepted_competitors`, `owner_replay`, `finite_owner_decode_replay`, `owner_r66_same_witnesses`, `owner_complete_returned_readbacks`.
- No axioms (1): `same_fact_distinct_occurrences`.

Final stdin SHA-256: `c947bc0005cf1eee354b3f849d4d6ea1c78a0ee2d193d252d116ef5301838f61`; stdout SHA-256: `c85a90f44d2257b3be6f9891ce24573bbc195720984625f2156e5b805a87001a`. Retained evidence supports in-memory kernel acceptance, not imported-module/Lake integration or an independently rerun check. The reported pinned Lean binary hash matches the binary at `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.

## Open boundaries and procedural deviation

The Lean schema does not authenticate physical completed-view/experiment identities or registry extraction, slice/allocation identities, accelerator maps, fact/edge pointers, admitted-Arc reference identity, completed-edge `fact_index`, redundant identity/lower/upper fields, or native finite-width/resource behavior. Extracting the modeled `World` from Rust remains OPEN. Genuine R66 `Root` construction, original A/B, the original joint strategy, whole-language hygiene/soundness/principality/termination and production remain OPEN.

The proof author invoked `lake --version`, violating the contract's categorical No Lake rule. It is recorded as a deviation; no build/environment/update command is claimed, and no filesystem trace establishes absence of incidental writes. The reviewer did not repeat it. The deviation does not erase the retained Lean proof terms.

Relevant existing tests were read, not run. No compiler was run. **Disposition: reject the frozen combined R73 submission pending the store-owned lookup repair and independent delta review. Preserve the accepted finite Lean evidence and every OPEN boundary.**

**Reviewer STOPPED / WRITES STOPPED.**
