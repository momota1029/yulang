# Concrete NPAIR producer compile validation

Sprint: `npair-concrete-producer-compile-validation-20261017`, contract
revision 1, SHA-256
`6eb81e84fbf8fafe2dec7dd6cbb63cacacc00005f72e9a8602151b5c151221ee`.
Validation baseline: `f2f95913cdcff78c4482b3556830483614c06e87`; command was run
after the contract/current-state checkpoint at `5d423a334e583895d34a0212ade6e610261fd108`.

## Result

One primary invocation completed successfully in 5.63 seconds (charged 6s):

```sh
timeout 120s env CARGO_BUILD_JOBS=1 cargo check -p yu-solver --features shadow-apply-candidate --tests
```

Exit status: 0. Cargo reported `Finished dev profile`. Test targets compiled;
no tests executed. No retry, repair, example, probe or second Cargo invocation
occurred. The raw combined output is
`/tmp/yulang-npair-concrete-producer-check-20261017.log`, SHA-256
`71ec35a9d0da40c342b6cfae94a2208fce02eb9970031cc643c58dd376451e34`.

This establishes compile success only for the pinned workspace/dependency state
and selected feature. It says nothing about runtime behavior, resource-boundary
behavior, source admission, authentic `At`, transport, receive consumption,
subtraction or parent theorem closure. `CHOOSE-SOURCE-2 /
RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN.

## Frozen inputs

The exact approved producer, accounting repair and source/build dependency hashes
are in the sprint contract. The corrected applied `candidate_effect.rs` hash is
`11a1477ff2c35c03dccb70bdc6121d89d3ced9fadb1921cb8cf8cd5c093b07fb`; the
`f1b…` hash names only its preserved failed pre-repair snapshot. Approval and
implementation limits remain in their frozen receipts.

Proof lane remains WAITING for the exact independently justified Operation/Call
contribution clause at its actual declaration/reference: same complete `w` at
the exact source port and predecessor context, plus its correspondence to the
native Operation instance, emission and admission. This sprint did not repeat
the source census or authorize source changes.

No source or test files changed. The foreign dirty sprint JSON, three historical
UNKNOWN worker reservations and board quarantine remain preserved. Fresh
independent compiler-referee review is pending; no parent or production gate is
closed.
