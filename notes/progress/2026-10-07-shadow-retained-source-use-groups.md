# Shadow retained source-use groups

Date: 2026-10-07
Baseline: `28650389ce9738b8dc76432210fb8fb017a90cc4`
Status: frozen default-off shadow implementation; regression-audited, no blocking or major findings
Claim class: borrowed structural identity inventory only
Authority: user-authorized shadow/experimental lane; no semantic or production authority

## Result

`RawStructuralArena::source_binder_use_groups()` exposes every retained
`Form::Use` occurrence grouped lazily by an exact artifact-branded `BinderId`.
Each result borrows the original source `ExprId`, binder and `UseId` and
preserves retained-arena order. This inventory includes uses which are not
direct callees and therefore have no `PendingSourceCallRegistration`.
`pending_binder_use_groups()` retains its narrower existing meaning.

The projection adds no use-completeness or semantic-absence claim and assigns
no typing, call role, annotation interpretation, beta, slot, profile or
judgment. A valid binder with no retained uses yields an empty iterator. A
foreign binder is rejected. Each exhausted query scans O(E) retained nodes
with O(1) additional memory.

## Review and verification

A regression auditor passed the bounded structural review with no blocking or
major findings. The reviewer noted that the tests use distinct parameter
spellings and suggested same-spelling lexical binders as optional additional
coverage. The implementation directly compares artifact-branded `BinderId`s;
no code defect was found, so this suggestion does not block the frozen slice.

Focused verification:

```text
RUSTC_WRAPPER= CARGO_BUILD_JOBS=2 cargo test -p yu-core --features shadow --test shadow_binder_source_uses -- --test-threads=1
```

The first run had two passing tests and one failed test because an unsupported
nested fixture was outside the retained projection. After replacing that
fixture with the supported nested-block candidate, the rerun passed all three
tests. Changed-file rustfmt and `git diff --check` passed. Two sequential
Cargo processes used two build jobs and one test thread each; no broad suite,
feature-off check, benchmark, Oracle execution or performance sample was run.

## Open boundaries

This inventory does not establish complete source-use coverage, declaration
applicability, call-view formation, annotation meaning, typed paths, owner or
receiver evidence, beta/Slots identity, original shared `xi`,
`OriginalAssocType_X`, profile/admission, receipt, Flow or licensing. Soundness,
principality, source adequacy and production cutover remain open.
