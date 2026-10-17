# NPAIR source-entry second HIR failure

Sprint: `npair-source-admission-correspondence-20261018`.
Parent: `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017`; original domain and
quantifiers unchanged. Original-condition closure remains 0.

## Exact runtime evidence

The first source-entry test attempt used an operation declaration whose own
signature contained a nested function annotation. A direct invocation of the
compiled unit-test harness ran one test and failed before solver entry because
`lower_module_with_local_source` returned `StructuralProjection`.

After the dispatcher-selected +600-second bounded fixture continuation, the
fixture was reduced to a bare declared effect and the same nested negative
result/result formal port:

```yu
act ctrl
my receive (f:() -> (() -> [ctrl] int)) = ()
```

The correctly selected one-test command was:

```sh
cargo test -p yu-solver --features shadow-apply-candidate \
  candidate_source::formal_concrete_negative_source_tests::source_entry_admits_only_nonempty_concrete_negative_formal_rows \
  -- --exact --nocapture
```

It ran **one** test and failed at
`crates/yu-solver/src/candidate_source.rs:490`, where
`lower_module_with_local_source(...).unwrap()` received
`HirAvailabilityError::StructuralProjection`. `CandidateInference::solve`,
candidate preflight, and the newly modified predicate did not run. The test
therefore provides no evidence of source acceptance or source-level refusal.
The preceding Cargo invocation omitted the full module path with `--exact`,
selected zero tests, and is build-only evidence.

## Current artifact state

`candidate_source.rs` has a candidate implementation of the adopted predicate
plus the focused regression, but the regression does not reach that predicate.
This code delta is unreviewed, unintegrated, and uncommitted. Preserve it for
adjudication; do not treat the clean design-contract reviews as code approval.
The error's precise HIR/source owner has not yet been isolated. Existing read
leases cover `yu-hir/src/module.rs`, `module/local_source.rs`, and
`module/source_annotation.rs`; source parser implementation paths were not
read or leased. No HIR/syntax write is authorized.

## Resource boundary and next evidence

The original 1500-second sprint envelope and the dispatcher-selected 600-second
continuation are fully charged/reserved: **2100/2100 seconds**, Astra0. The
continuation's two candidate source inputs both stopped at the same HIR result.
No further runtime, test, implementation, or review work is charged to that
envelope. A source-owner read continuation needs a fresh exact lease and
versioned budget decision before new access or execution.

Next evidence must identify the first concrete `StructuralProjection` producer
for this valid-looking source shape, or find a minimal already-supported source
form that retains the exact adopted row. If no authentic HIR carrier can be
formed without changing HIR/source semantics, report that as the exact
implementation obstruction. Do not broaden the accepted row class, edit HIR or
syntax in this continuation, or weaken the parent theorem.
