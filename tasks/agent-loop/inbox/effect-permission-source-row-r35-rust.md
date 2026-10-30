# R35 Rust source-row handoff

Sprint: `EFFECT-PERMISSION-SOURCE-ROW/20261031-R35`  
Contract SHA-256: `b222bb668f9c8f872dfc83a19c48c8ed937a6c5894f6e8ab5b50c5ef468ce570`  
Assignment / handoff revision: `/root/effect_permission_r31_rust` / `r2` (Luna polarity repair)  
Parent: effect hygiene and soundness research; this packet contributes source-owned annotation-row provenance only. Original A/B obligations remain open.  
Baseline: `yulang3` / `90fd99073fa03da2cc1ba6aed3bff8e578b34020`.  
Input manifest SHA-256: `a9ef98acf98751e603046fe0c4f64ad107373513d6dd0c33c483a2ff235e1205`.  
Admission SHA-256: `64e0ff5f8549a30d6a7d0df6134924bccb7ae0e27ec2daad25d8547283e4a4e8`.  
Stage ledger SHA-256: see the current authenticated R35 ledger.

## Assignment and runtime receipt

Original producer: `/root/effect_permission_r31_rust`; polarity repair by Luna `/root` after independent review. No descendants. The bounded repair changed only the formal-context seed; no builds/tests/runtime were run.

Exact write leases used: `tools/inference-playground/src/runtime/program.rs` and this handoff. No other path was written. No scratch, copy, extraction, environment, target, cache, log, or external directory was created.

## Source-to-witness contribution

`RuntimeProgram` now creates one `HirSnapshotToken` from the same `Arc<HirModule>` passed to `from_hir_with_roots` (source line 770; sole `RuntimeProgram` initializer at lines 1475 onward). Both public construction routes funnel there: `from_hir` at lines 753–758 and `from_candidate_world` at line 659. The lambda lowering arm (lines 1035–1060) requests a witness using that retained token, the exact `SourceRootId`, and the Lambda occurrence.

`SourcePermissionRowWitness::from_lambda` first looks the occurrence up in `hir.local_source_for(source_root)`; it rejects missing or mismatched roots, a foreign owner token/occurrence, or a mismatch between `occurrence_source_key` and the retained expression source. It then requires an actual `LocalSourceForm::Lambda`, the contained formal's `HirParameterId.source_root()` to equal that root, and the formal annotation owner to equal it. Missing annotations, annotations with no effect rows, failed identity queries, and fallible row-payload reservations withhold the witness. An `authenticates` method reconstructs the expected witness by this root-plus-occurrence lookup and compares every stored coordinate and row field; no consumer currently calls it.

The witness retains the snapshot token; source root; Lambda `SourceSite` occurrence/range; formal ID/source/range; annotation owner/position; and every effect row found through the annotation type. Each row stores an exact `Argument` / `Result` / tuple-element index path, polarity, `SourceEffectRow.position`, ordered typed `SourceEffectId` values, and all symbolic variable entries. Argument descent flips polarity; result and tuple descent preserve it. Traversal starts contravariantly at the Lambda formal, matching Lean's `pathPolarity true` convention; Argument descent flips polarity, while result and tuple descent preserve it. Thus `cb: () -> [signal] int` is retained under `Function.result` with contravariant polarity instead of being missed by looking only at `annotation.ty.effects`. Concrete vectors are copied without sorting or deduplication, so identity, order, and duplicate occurrences remain. Symbolic strings are copied entry-by-entry without filtering. No full `SourceAnnotation` is copied.

This code records all source effect rows and their structural paths; it does not decide that any row authorizes a Grant or select a runtime permission policy. Downstream selection and rejection when the selected row contains unrepresented symbolic entries remain open. `parse_row` currently rejects unsupported/ambiguous concrete members and rows with more than one symbolic variable as unsupported before a `SourceAnnotation` is available; it does not expose a partial row. A no-annotation inline lambda therefore receives no witness. Named binding formals lower from their admitted parameter annotation through `parse_annotation`; source-member parameters without an admitted annotation and unsupported lowering routes likewise receive no witness. Rows rooted in a different HIR allocation cannot be bound to this `RuntimeProgram` token and are withheld.

## Inspected source routes and pins

- `crates/yu-hir/src/module/local_source.rs:1146–1182`: named formals select their source/optional annotation, parse it with the same `SourceRootId`, then place that `LocalSourceParameter` directly in `LocalSourceForm::Lambda`.
- `crates/yu-hir/src/module/local_source.rs:2092–2122`: inline lambda lowers its exact binder/source/range and parameter ID, with `annotation: None`; it cannot manufacture a permission witness.
- `crates/yu-hir/src/module/source_annotation.rs:446–472`: annotation owner and exact annotation source key are retained. `parse_type_source` at lines 543–599 stores function argument/result structure; row-bearing `SourceAnnotationType` nodes keep their rows at their own structural positions. `parse_row` at lines 630–687 stores its exact source key and pushes each resolved concrete member and symbolic variable in encounter order.
- `crates/yu-hir/src/module.rs:2062–2067, 2095–2100`: occurrence-to-source-key and parameter-origin queries are bound to the owning HIR artifact. `SourceNodeKey` identity is typed parse/green/start identity, not rendered text.

Baseline `program.rs` SHA-256: `9823cd8d5c972e0c6ec2766d66f9d21c6564727317bc2646d2480a9e85132f74`.  
Pre-repair `program.rs` SHA-256: `483073deba4619e82e6ff821108c23b45bca9b14cbf2065570f7e5fca38273bc`.  
Pre-repair source diff SHA-256: `c27285e43fa9e2a747780b09b6abfeae29b027a2f23704d9854b4a30b48345d6`.

Pinned unchanged dependencies: `source_annotation.rs` `409ce491bc216c6963bf76d20810790aa2756edf260ecc35e76d5cfc05d24b3f`; `local_source.rs` `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1`; `module.rs` `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`; `full_parse.rs` `dd92603f8f5549b8b3f6e45ab6cb39b6598480b7f1cda7897e27b5113107db93`. R34 source-owner baseline remains pinned by the manifest.

## Checks, evidence class, and limits

Outcome class: implementation / provisional, uncompiled. Source inspection confirmed the HIR annotation-to-formal route, both Lambda construction/lowering routes above, the R34 Arc token owner, and the single `RuntimeProgram` initializer. No Cargo, build, compiler, test, runtime, Lean/Lake, `git diff --check`, or quarantined-file read was run, as required by the packet. No independent review is claimed; this producer does not certify its own output.

Not established: semantic selection of the callback-result row when multiple rows occur; downstream row representability or R32 acceptance; source-to-Grant/request wiring; selected-arm provenance; authenticated observations; invocation lifetime; native `Step`/`History`; original A/B closure; whole-language hygiene/soundness/principality/progress/termination; or production authority. Source authenticity and downstream application remain with the proof/review and Luna gates.

Luna repair state: writes stopped; no descendants. The R35 polarity finding is addressed by anchoring traversal at the formal contravariantly, consistent with Lean. Independent re-review remains required. Rust compilation, Rust↔Lean vector simulation, callback selection, and downstream consumers remain open.
