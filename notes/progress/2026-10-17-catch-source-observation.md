# Catch source observation run receipt

Sprint: `catch-exit-incidence-and-source-observation-20261017`, contract rev3
SHA-256 `22c4f14f883c6b7bb0d35c43f2195b3565e0744c4bfe22ed09523042786ccb75`.
Primary run by Luna after CLEAN frozen code review and CLEAN feature-command
pin review. Requested worker implementation model/effort was Luna/high;
observed author settings remain UNKNOWN/UNKNOWN.

## Frozen inputs and command

- Example: `crates/yu-solver/examples/research_catch_source_export.rs`
  SHA-256 `243bb0d1e328ed951576ff37eda70007e708cc461a81e9999e69bd38dae41abb`.
- Exact source literal: 138 bytes; SHA-256
  `9a86d2e0d0004cbdbd4be96dcdc284b6648287a203518c93211c43705f8ed8d3`.
- The implementation pre-run review was CLEAN; all 60 immutable dependency
  pins matched, with only the leased example differing from its baseline.
- Rev3 added the `shadow-apply-candidate` gate owner pin and command review.

Invocation (first of at most two; one actual example execution cap):

```sh
timeout 120s env CARGO_BUILD_JOBS=1 cargo run -p yu-solver --features shadow-apply-candidate --example research_catch_source_export
```

Exit code 0. Cargo reported the `yu-solver` compile finished in 1.64 seconds,
then launched and completed the example. The primary's total shell wall time
was not separately measured. No other Cargo/build/test invocation ran.

## Observations

Parsing reported no structural recoveries. HIR lowering returned a value, but
also reported two errors:

- `UnsupportedItem` at bytes `0..44` for the `act signal` item;
- `UnsupportedExpression` at bytes `75..138` for the Catch expression.

The example did not stop on `hir.errors`; it proceeded. It authenticated the
`id` and `result` definition roots and source keys, Catch/source occurrence
keys, `signal::ping` declaration and arm binder/use identities, and three Apply
occurrences. Ordinary `CandidateInference::solve` returned a candidate with
`observes_hir=true` and zero candidate conflicts. It reported three exact
`source_call` to Apply matches, one exact `fresh_use` for `id`, and borrowed
graph exports from authentic `id` and `result` roots (10 and 3 nodes).

Because HIR contains the unsupported-item and unsupported-expression errors,
these observations do **not** establish that the exact source program was
accepted or fully represented by HIR, and they do not establish source typing.
The zero-conflict candidate and exports describe only the partial HIR/local-
source object that this lowering returned. The missing
`CATCH-EXIT-INPUT-1` matcher-input correspondence is untouched. No handler
adequacy, detached export, runtime semantic execution, or F1 closure follows.

This example did execute. Under rev3, that ends execution authority even though
it returned exit 0. Cargo invocation 2 is therefore forbidden; no source repair,
second run, or runtime-driven update is authorized in this sprint. The existing
source and frozen review target remain unchanged after execution.

## Reviews, costs and remaining gates

- Pre-run regression review: CLEAN for the exact two-borrow change and static
  source/API associations; compilation and HIR results remained unobserved then.
- Feature-command delta review: CLEAN; confirmed `shadow_apply` is gated by the
  pinned feature. Requested cap 10 seconds; conservatively charged 10 seconds.
- First Cargo invocation: exit 0; compiler output and candidate observations
  above. It is the sole actual example execution.
- Fresh post-run receipt review: pending. This review can verify the receipt and
  boundaries; it cannot convert partial HIR into accepted source evidence.

The proof artifact remains independently reviewed CLEAN as a bounded,
conditional supplier obstruction. `CATCH-EXIT-INPUT-1`, F1, FK1,
FIRST-RESULT-ADEQUACY, H1-H2, JOINT_DEC, F5, source-Generalize/export,
principality, production and the other listed parents remain OPEN.

Post-run receipt review: fresh independent `regression_auditor`, CLEAN within
bounded scope, STOPPED; conservatively charged 60 seconds, requested model and
effort UNKNOWN/UNKNOWN. The reviewer verified the receipt, output and contract
hashes; HIR error limitation; no-second-invocation boundary; and open parent
gates. The runtime output and sole-invocation history remain Luna-supplied; the
reviewer did not rerun them.
