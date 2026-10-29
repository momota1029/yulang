# R28 Rust handoff — R2 source-only candidate

Status: STOP. Candidate is frozen for independent exact-hash source review; no source gate acceptance is claimed. The frozen additive evidence map is SHA-256 `37d36c35fce7988bc0387422f992f0dae81a1f97815fa768cb904a0d1801eacb`.

## Exact current targets

- `isolated/ep-owner-certificate-r28/project/tools/inference-playground/src/runtime/machine.rs` SHA-256 `c66d325fd14cf5d94094c9e09568950949405bf67b6924a513a2cceab3c90975`
- `isolated/ep-owner-certificate-r28/project/tools/inference-playground/src/runtime/receiving.rs` SHA-256 `fbc664f166e2500208ba8e8598a078bbbcf2a3a72f620a5d40576750bca5bf81`
- This leased handoff is the only path written in the final 30-second handoff allowance. Recompute its SHA after this write.

## Work completed

- `CallbackRouteEvidence.use_handle` carries typed `CallbackUseHandle`. The actual handle read from `ViewKind::CallbackResult` is passed to `callback_grant`; validator recomputation also uses that typed identity. `CallbackEntryHandle` remains separate.
- Captured Catch consumer evidence now includes dynamic `HandlerInstallation.occurrence`, `installation.owner`, and an authentication marker. `validate_handler_installation` runs before evidence capture; the handler source-site occurrence remains separate.
- `Observation` carries the bound assigned by `Receiving::observe`. Callback route evidence retains that observation and the ordered execution-table projection. Construction/validation joins observer and bound, event, execution occurrence, view, receipt, callback use, and table row; observed occurrence replaces first-match search.
- JSON edits are additive; schema R1 and language/solver semantics were not edited.

## Incomplete and unverified

No compile, test, runtime, Cargo, or Lean execution occurred. Existing R1 mutations were not extended with R2-specific observation/table/Catch-installation mutation cases; target-present/changed/rejected evidence for those new fields is therefore absent. Runtime JSON/schema conformance and source/native correspondence remain unverified. The candidate is not compile-authorized and awaits independent source-only review.

## Resource accounting

The parent observed the R2 launch at approximately 22:54 UTC; current checkpoint is 22:58:58 UTC, about 298 seconds elapsed wall time since that notice, including tool and coordination time. This exceeds the packet's 150-second repair target; record that overrun plainly. With the previously reserved 250 seconds conservatively charged, estimated total Rust charge is about 548 seconds of 1,150, leaving about 602 seconds. No Git operation or process launch occurred. Stop here pending independent review.
