# Shadow pending structural source-core projection

Date: 2026-10-07
Baseline: `475036233`
Status: frozen default-off structural implementation; compiler-referee and regression-auditor review passed after test repair
Claim class: retained syntax-to-core-shape encoding with unresolved semantic premises
Authority: user-authorized shadow/experimental lane; no inference or production authority

## Result

`PendingStructuralProjection::from_raw` separately projects the validated raw
HIR inventory into flat source-core-shaped nodes for retained unary Lambda,
Bind, Use, Integer, Group and Apply forms. It preserves the body and all
retained Lambda entries, including declarations outside `Skeleton::body()`,
using same-arena child offsets. Apply nodes borrow only their own `RawCall`,
including its pending rows, optional source/capture joins and captured-only
locator input. Annotation occurrences remain borrowed metadata.

Use nodes remain `PendingUseNormalization`; the original `Gamma`-dependent
normalization is not guessed. Unsupported forms and inventories without a
retained unary Lambda fail atomically. Missing multi-parameter declarations
are not reconstructed. The prior exact-candidate `IncompleteDerivation`
constructor remains unchanged.

The projection is structural only. It emits no typing derivation, Value or
Computation judgment, callable role/entry, slot/profile, admission, inferred
scheme, source-acceptance theorem or production inference result. Construction
and drop use flat vectors rather than recursive child ownership. For `n`
retained nodes, the projection adds O(n) time and O(n) node/declaration
storage.

## Review and verification

The compiler-referee review found no semantic-boundary or identity issues. The
regression auditor's minor finding requested a captured-candidate regression
covering Lambda/Bind children and call-local capture/locator retention. The
test was added; a later minor requested explicit failure on mismatched form
pairs, which was also added. Delta review passed with no residual findings.

Focused verification:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-core --features shadow --test shadow_derivation -- --test-threads=1
rustfmt --edition 2024 --check crates/yu-core/src/shadow_derivation.rs crates/yu-core/tests/shadow_derivation.rs
git diff --check
```

The final focused run passed all 7 tests, including exact-candidate legacy
coverage, ordinary unary calls, per-call pending-row separation, unresolved
annotation/use normalization, retained Group, multi-parameter rejection,
captured-source joins and a 256-Apply flat chain. Earlier attempts exposed a
test helper name collision, test reference-type mismatches, and an invalid
pointer-equality expectation for equal branded IDs stored in distinct slots;
those test defects were repaired. The final run was one Cargo process with
two build jobs and one test thread. No broad suite, feature-off build,
performance sample, Oracle execution or semantic inference differential was
run.

After the review/repair round, the complete `yu-core` shadow integration suite
also passed: `RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-core --features shadow -- --test-threads=1`
(31 tests across 8 integration targets; one Cargo process, two build jobs, one
test thread). This is regression evidence for the package shadow surface, not
semantic or production parity.

## Open boundaries

The supported projection is not a generic typed source-core derivation.
Annotation interpretation, Gamma, exact source normalization, complete
call-view formation, `beta/Slots`, original `xi`, `OriginalAssocType_X`,
profile/admission, role resolution, soundness, principality and source
adequacy remain open. Production inference is not routed through this lane.
