# Shadow Apply to source-position crosswalk

Date: 2026-10-06
Status: implemented and independently reviewed; default-off structural plumbing only
Baseline: `1a5596ac87bd7ff0f19ee83bd9f36142dae5dc59`

## Result

The existing borrowed `SkeletonSourceCrosswalk` now looks up a retained shadow
`Form::Apply` by its exact CST call-tail `PositionId`. For a direct `Use`
callee, a second accessor returns that already retained `UseId` and `BinderId`.
Grouped and computed callees return no direct-use link. The crosswalk creates
no expression, binder, use, or production HIR identity.

This lookup is shadow lexical/source plumbing, not production
`NameResolution`. It supplies no typed path, owner, receiver, beta, slot,
profile, role, annotation interpretation, Q result, or semantic evidence.
Unsupported skeleton projections retain an empty crosswalk; foreign positions
are rejected. Existing pending premises remain unchanged.

## Review and verification

The implementer reports this focused check passed (4 tests):

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-hir --features shadow shadow_resolved_application_identity -- --test-threads=1
```

The implementer also reports rustfmt and `git diff --check` passed. Independent
compiler-referee review found no identity/authority/failure-boundary issues;
regression review found no production-path, feature-isolation, pending-premise,
diagnostic, or observable-lowering regression. Reviewers did not rerun tests.

Coverage includes direct/nested/grouped/computed callees, distinct Apply
occurrences through the same binder, exact retained object identity, foreign
and unrelated positions, unsupported projections, unchanged pending rows,
and unchanged production lowering outputs/errors/diagnostics.

## Scope boundary

This establishes a checked structural correspondence from an exact source
position to an already retained shadow Apply and its existing direct lexical
callee identities. It does not create production `ResolvedExpr::Apply`, alter
source acceptance, or discharge call-view, type, admission, adequacy,
soundness, principality, or production-cutover gates. No performance sample or
broad test suite was run.
