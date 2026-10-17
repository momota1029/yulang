# NPAIR source-admission failure continuation

Sprint: `npair-source-admission-correspondence-20261018`, revision 1.
Original parent and source domain are unchanged; parent closure remains 0.

## Observed failure

The source-entry regression was first written with an `act ctrl:` operation
declaration whose signature itself contained a nested annotated function. The
focused test process reached `lower_module_with_local_source` and returned
`HirAvailabilityError::StructuralProjection` before `CandidateInference::solve`
or the modified solver preflight ran. The direct test harness reported this at
`candidate_source.rs:490`. Thus the initial input established neither HIR row
retention nor source admission. The preceding Cargo invocation selected zero
tests because its `--exact` filter omitted the `candidate_source::` module
prefix; it is recorded as build-only evidence, not a test pass.

## Bounded continuation adopted by Luna

Keep the approved predicate change unchanged. Replace only the regression
fixture with the minimal source form using a bare declared effect family and a
negative result/result port:

```yu
act ctrl
my receive (f:() -> (() -> [ctrl] int)) = ()
```

This isolates formal-row lowering from an unused operation declaration while
preserving the adopted concrete-only negative port. If HIR forms and retains
the exact row, continue through normal `CandidateInference::solve` and all
accepted/refused neighboring rows from the frozen contract. If lowering fails
again, stop code changes at that exact owner; do not repair HIR or syntax in
this continuation.

The frozen HIR proof (`930f99d168ede5e5592a6348ffc4a6f84ccd40c8d78128befaf91297816bafc2`)
is retained as a conditional argument, not runtime evidence. No syntax or HIR
implementation owner is added to the write lease. The initial source and exact
failure remain preserved in this receipt.

## Resource and review amendment

Luna adopts the dispatcher's one-time resource extension of **600 seconds** for
this bounded fixture/failure continuation, raising the sprint ceiling from
1500 to 2100 seconds. Charge the full extension at issue: primary diagnosis and
fixture repair 240s, one focused source-entry verification 120s, fresh
independent compiler review 120s, spec-delta review and contingency 120s.
Astra remains 0. Existing UNKNOWN reservations are unchanged. No new worker is
started for the fixture repair.

The exact verification command is one Cargo test invocation using the full
module-qualified `--exact` name. A zero-test result is a failed selection, not
coverage. A passing HIR/source-entry test still closes no original theorem
condition by itself. The final code/proof pair requires fresh review before
integration; any additional HIR or parser source access is a separate exact
read-lease decision.
