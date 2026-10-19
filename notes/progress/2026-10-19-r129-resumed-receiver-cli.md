# R129 probe — nested receiver permission across continuation resumption

## Hypothesis and executable witness

I combined two existing public behaviors: a helper receives a computation with
`[io]`, handles `io::tick`, and resumes the captured continuation with `9`.
The helper catches its own `pending` parameter. The exact stdin CLI invocation
(`--run main --steps 30000 -`) completes with stdout `9\n` and empty stderr.

The paired negative source differs only in catching the captured outer `thunk`
instead of `pending`. It exits unsuccessfully, publishes no stdout and reports
`runtime unavailable: HandlerEvidence` on stderr. That outcome matches the
existing constructor-owned receiver rule in `runtime/receiving.rs`: a nested
helper cannot borrow its caller's received permission.

This is finite executable evidence for one nested helper, one `tick` request,
and one continuation resumption. It does not establish expiry after arbitrary
resumption, arbitrary continuation behavior, source/native soundness, or any
Simple-sub/evaluator theorem. It does not change accepted semantics or close a
parent gate. A falsifier is either a positive case failing to publish exactly
`9\n`, or the negative case succeeding or publishing a value.

## Verification

The public binary was run directly on both exact fixtures. Then:

```sh
cargo test -p yu-playground --test cli_resumed_receiver_permission -- --exact resumed_continuation_uses_the_receivers_own_permission_through_cli
```

Result: exit 0; 1 passed. The test artifact SHA-256 is
`9a5fd48d1f89ae064960554d8ece36d6b9b437ae6cc91504a1e7c035aec9257a`.
Compiler warnings were the existing dead-code warnings in HIR and solver.

The current R128 candidate remains review-pending. This R129 probe has no
independent review receipt and is recorded as a provisional candidate, not a
closed sprint or proof.
