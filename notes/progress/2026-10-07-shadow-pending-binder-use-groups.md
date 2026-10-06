# Shadow pending binder-use groups

Date: 2026-10-07
Baseline: `a8b97aaeb2eebdc51021eb5c79e12a2cd07feb5f`
Status: frozen default-off shadow implementation; independently regression-audited, no blocking or major findings
Claim class: borrowed structural identity projection only
Authority: user-authorized shadow/experimental lane; no production or semantic authority

## Result

`RawStructuralArena::pending_binder_use_groups()` exposes a lazy borrowed
`PendingBinderUseGroups` view. A query validates the artifact-branded
`BinderId`, scans the retained node inventory once, and yields only existing
`PendingSourceCallRegistration` values whose direct-use input has that exact
binder. It preserves retained-node order and the existing Apply, Use,
annotation, capture, and pending-row references. It creates no registry,
fresh identity, semantic contract, slot inventory, or judgment.

The grouping covers only registrations already emitted for direct resolved-Use
calls. Grouped/computed callees and absent registrations are not interpreted as
semantic absence or as proof of use completeness. Repeated calls retain
distinct Apply/Use identities while sharing the already resolved binder.

## Review and verification

A regression auditor checked identity branding, direct-use scope, missing-data
handling, order, surface exposure, sibling registration paths, and scan cost.
The sole minor finding was corrected: iteration is documented as retained-node
order, not source-span order. No production path reaches the new API.

Focused verification passed:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-core --features shadow --test shadow_binder_use_groups -- --test-threads=1
```

Four tests cover repeated same-binder calls, distinct binders and annotations,
grouped/computed callee boundaries, and foreign-artifact rejection. Changed-file
rustfmt and `git diff --check` also passed. One Cargo process used two build
jobs and one test thread; no broad suite, feature-off build, Oracle run, or
performance sample was used.

Per exhausted binder query, the view costs O(E) over retained nodes and O(1)
additional space. It retains no group table or allocated query result.

## Open boundaries

This projection does not establish formal applicability, complete source-use
coverage, annotation interpretation, callable role/entry, typed path, beta or
Slots identity, original shared `xi`, `OriginalAssocType_X`, profile/admission,
receipt, Flow, or licensing. All soundness, principality, source adequacy and
production cutover gates remain open.
