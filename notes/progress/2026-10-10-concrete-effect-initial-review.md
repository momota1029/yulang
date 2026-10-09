# Concrete/co effect annotation: initial frozen review

Date: 2026-10-10
Branch: `research/simple-sub-intrusion`
Committed baseline: `29f645c56d62cd18ae15557ca612c52c549fb620`
Status: implementation repair active; not integrated or certified
Authority: [concrete annotation gate](../design/2026-10-10-concrete-effect-annotation-implementation.md)
Mode: M3, three independent reviewers (semantics, conformance, resources)
Measurement budget: zero benchmark processes/samples

## Frozen artifact and actual evidence

The first implementation froze twelve HIR/solver files, including the new source
annotation constructor, private effect kernel and four integration tests.
The frozen kernel hash was
`7d2b0575a80d9fa3f335c56e2ccd133866c06b200751b97c4566e66179b5bb1d`;
solver lib hash was
`f81e527ec783fe1dfefe88ffbcd9ecf469417202ab95f036e72adbeedc3eea69`.
All assigned reviewers finished before a single fresh producer received repairs.

Primary checks used `RUSTC_WRAPPER=`, `timeout 180`, `--offline`, `-j 2`:

- `cargo check -p yu-solver --features shadow-apply-candidate`: failed with
  three unresolved `yu_syntax` references. Syntax is a dev dependency only.
- `cargo test -p yu-solver --features shadow-apply-candidate --lib candidate_effect::tests -- --test-threads=1`:
  three passed, 483 filtered, no warnings. Test-mode dependencies permit those
  imports, so this result does not negate the owning build failure.
- Initial scoped diff checks passed. Integration tests and broad checks have
  not run; the three passing kernel tests do not cover the counterexamples below.

## Accepted repair bundle

1. Reexport the retained `SourceNodeKey` through `yu_hir::shadow` and use that
   existing HIR dependency from the solver. The architect confirmed this
   compilation repair; no direct syntax dependency or provenance wrapper is needed.
2. Remove processing-pair → retained-origin diagnostic edges. Link the current
   processing pair and retained creator directly to their actual comparison.
   Otherwise a forbidden F lower followed by an allowed E lower at an E allowance
   replays F's earlier conflict under E's successful request. Add successful-after-
   failure, distinct forbidden sibling causes and future-lower cached-root tests.
3. Perform recovery validation once and protect recursive annotation construction
   with the explicitly measured depth-128 formation envelope. Per-recursion
   descendant scans were quadratic and the expression limit did not bound types.
4. Share view reconstruction by original view and mapped tail within each
   freshening/extrusion operation. Copying an A-member view for A member operands
   retained quadratic payloads. Preserve member tail dependencies and correctly
   freshened coordinates; add clone-count and correlation checks.
5. Charge extrusion scratch during traversal and failing paths. Successful-end
   accounting missed coexistence with nested view/origin samples. Add a failure
   after view construction and verify peak inclusion, rollback and charge release.

The conformance reviewer found no additional issue in actual source identity,
whole-binding checking, paired exposure, operand branding or protected existing
test expectations. Those clean areas are carried forward unless the repair
changes their dependency cone. Semantic/resource repair closure and runtime
verification remain pending; no finding is silently closed by this record.

## Active ownership and next step

The fresh implementer owns the same twelve paths exclusively: HIR `module.rs`,
`module/local_source.rs`, `shadow.rs`, `module/source_annotation.rs`; solver
`lib.rs`, `candidate_source.rs`, `candidate_extrusion.rs`, `candidate_scheme.rs`,
`candidate_intrusion.rs`, `shadow_apply.rs`, `candidate_effect.rs` and
`tests/candidate_effect_annotation.rs`. It does not own manifests, records,
committed intrusion tests or Git. Primary owns checks, adjudication and integration.

After the repair freezes, repeat the failed owning build, run the new integration
and kernel tests and the bounded intrusion/local-source/Call regressions, then
assign independent delta review of the accepted findings and changed dependency
cone. Synchronize implementation evidence before committing the code.
Actual source operation emission, contravariant attachment, complete Call,
public schemes, soundness/principality and F5 cutover remain open.
