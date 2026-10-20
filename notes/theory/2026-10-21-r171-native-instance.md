# R171 bounded native observation — formal-Name forwarding candidate

Status: **frozen provisional source/native and candidate-inference evidence; final independent result review pending**.

## Scope and source membership

Contract `tasks/agent-loop/sprints/formal-name-forwarding-instance-20261021-r171.md`, revision 1, SHA-256 `2491bcdc3dc7b09f8aeb06754ebe635b1dae4b8c1e8cef5f526c7517ea667241`. Baseline code HEAD `e27d00039`; R170 result was integrated before this sprint.

Fixture `tools/inference-playground/examples/r171-formal-name-forwarding.yu`, SHA-256 `cb2fff33a1ab983a932064cc1699d9f4f4a8d5e00d52986525884d42bc58234f`:

```yu
act signal:
    our ping: () -> int

my terminal (t:[signal] int) = t
my relay (t:[signal] int) = terminal t
my answer = relay (signal::ping())
```

The CLEAN-reviewed proof artifact `notes/theory/2026-10-21-r171-forwarding-instance.md` (SHA-256 `d19b5ceb2c1ace95ce2cc49bdd6c35ef4bd4de223f07e181a472a037a35a133b`) gives the occurrence-qualified membership table. It distinguishes `terminal`'s resolved body Name from `relay`'s forwarding Apply `terminal t`; the argument resolves to `relay`'s own formal. The outer `relay (signal::ping())` is an initial call, not the forwarding edge. It separately derives the initial Unit→Int operation typing under the original parent's base typing contracts. This review establishes source membership and conditional source typing only; it does not establish parse, lowering or candidate-inference success by itself.

## Code and exact invocation

Harness `tools/inference-playground/examples/r171_provider_incidence.rs`, SHA-256 `b8d9afd91154c7b0df1d1192ad1567a0e25fac7ef4ff4b698d989acd1c205e75`. It reuses the R170 borrowed observer without solver edits. Independent source/harness review and exact invocation review are CLEAN (`/root/r157_contract_review`); exact invocation and host executable pins are frozen in implementation handoff revision 2, whose SHA-256 is `dc7afac5b53acfd33371205a6e525a8c531984aa502adb9d72351a0c9e57cbca`.

The single authorized `cargo run --offline --locked --manifest-path tools/inference-playground/Cargo.toml --example r171_provider_incidence` completed after parsing/lowering this fixture and `CandidateInference::solve` succeeded. It was run in this repository under the reviewed bwrap/timeout boundary; no Yulang2, web demo, evaluator, test suite, external runtime, nested CLI, retry, alternate checkout or background service was used.

- `probe_status=0`; `process_group_status=0`; `process_scan_status=0`.
- Stdout SHA-256 `5c47875a6bdb59da380772df81660ec71ac59b9317030de149e26599c883fff5`.
- Stderr SHA-256 `46e3e404c5231180c92d1562b3ec380c135cf9901ea7638640c01b9627d06be5`.
- Status SHA-256 `68c10920ac9b4b082ad35849d64232dd27adbe99c2c22f108f9104548d052cad`.

## Observation and exact limit

The bounded output reports FunctionPort parent q values `27`, `77`, and `95`, with corresponding FunctionPort ordinals `43/45`, `123/125`, and `156/158`; incoming Replay dependency rows are printed for those parents. It also reports module Capture route occurrences 8 and 13, with `context_use=1` and `context_use=2`, and their captured-bound/snapshot/map records. The observer reports `lambda_slot2_source_join=NotJoinedToContextRecord`.

The shared 64-row selection cap was reached: `rows_truncated=true`. At least one rendered Capture graph/Terms record also shows its 480-byte record cap marker. Therefore the output does not enumerate every route/row, and any affected individual record is partial. The differing displayed provider and Capture relation IDs are not a counterexample and do not establish a missing semantic bound; the observer has not joined those IDs by source identity.

**Parent application:** this is a successful Y3 candidate-inference example over a CLEAN-reviewed §6 source member. It is not runtime evaluation, a Yulang2 compatibility result, or a native incidence proof. The exact first remaining native association is source occurrence/CauseId/FactId/Terms → the same forwarding Apply provider's Capture or justified shared anchor → that provider's own maps → all justified ordered transport/Replay alternatives → the same A_F consumer q with current residual/scoped payload. The existing observer does not expose a source join for that target occurrence, and the bounded output is truncated. `R169-SOURCE-FACT-CAPTURE-INCIDENCE-1` therefore remains OPEN. R70/R71/R165/R166/Replay residual, original A/B and production gates also remain OPEN. No retry, row-cap increase, source rewrite or instrumentation expansion is authorized here.

The proof producer stopped before this run. Luna has frozen the result for independent delta review; final review and Git closeout remain pending.
