# R98: reuse one raw continuation under distinct current receivers

Status: ACTIVE; finite continuation capture/resumption evidence slice.
Primary: Luna `/root`. Runtime outcomes are candidate observations, not a general Resume theorem.

## Frozen positive fixture and paired falsifiers

Add one new three-cell test to `tools/inference-playground/tests/runtime_resume.rs`, using current helpers and no production change. Freeze this exact positive source first:

```yu
act io:
    our tick: int -> int
    our other: int -> bool
my first (thunk:[io] bool) = catch thunk { io::other(p), _ -> true }
my second (thunk:[io] bool) = catch thunk { io::other(p), _ -> false }
my relay (thunk:[io] bool) = catch thunk { io::tick(p), k -> { my before = first (k 11); if before: second (k 23) else: true } }
my main = relay { my result = io::tick 7; io::other result }
```

Positive candidate prediction: `Completed(Boolean(false))`. The same captured `k` is applied once as `k 11` under `first`, then again as `k 23` under `second`. The saved suffix issues `io::other` in each resumption.

Two paired negative variants start from those exact bytes and change only one operation pattern:

- In `first`, replace `io::other(p)` with `io::tick(p)`. Prediction: outward `UnhandledRequest` for declaration-owned `io::other`, Int payload `11`.
- In `second`, replace `io::other(p)` with `io::tick(p)`. Prediction: outward `UnhandledRequest` for `io::other`, Int payload `23`.

These are falsifiable candidate observations. They do not prove handler restoration in the source language, arbitrary continuation safety, static/native projection, or a universal Resume theorem. Any preparation failure, wrong outcome/identity/payload, stale receiver use, source mismatch, dependency drift, or blocking/major review stops R98. No repair/retry.

## Proof obligation

Give a finite source-to-candidate correspondence for the exact positive and two variants: actual local formal/annotation/name/operation identities; original Catch ordering and bodies; one captured raw continuation at the initial tick; original saved suffix; two applications with distinct response values; actual TemplateNode constructor induction and control/owner/view remapping; current receiving invocation observations; exact Catch selection or forwarding. Separate static source premises from runtime observations, and preserve raw continuation, current state and handler boundaries as distinct identities. Reuse `notes/theory/2026-10-16-source-raw-continuation-capture-projection.md` only under its stated premises; bind this fixture to authentic constructors before applying it.

Proof note: `notes/theory/2026-10-19-r98-continuation-current-context.md`; proof handoff `tasks/agent-loop/inbox/20261019-r98-proof.md`.

This slice adds no native K,D or residual projection evidence and does not close `R78-NATIVE-HYGIENE-1`, arbitrary foreign continuation behavior, original Simple-sub/evaluator quantifiers, A/B, R50/R85 or production adoption.

## Leases and verification

- Luna primary only: this contract, current.json, R98 review inboxes and closeout.
- Implementation lane only: add one three-cell test and implementation handoff in `runtime_resume.rs`; preserve all existing tests and helpers. No production edits or execution.
- Proof lane only: the two proof artifacts above; no source edits/build/test/CLI/Git.
- Fresh spec review before edits; after source/proof freeze, spec delta confirmation and fresh compiler/source review. Reviewers are read-only; Luna preserves their reports.

After frozen bytes and CLEAN spec delta, Luna runs exactly once:

`CARGO_BUILD_JOBS=2 timeout 120s cargo test -p yu-playground --test runtime_resume same_raw_continuation_reuses_suffix_under_each_current_receiver -- --exact --nocapture`

No retry under R98. The one test must execute all three cells. A failure or surprising result is recorded without repair.

## Budget and remaining fronts

Total cap 1,800 seconds: proof 600; implementation 360; spec 180; one command 120; compiler/source review 240; integration/closeout 300; Astra 0. Do not exceed six live assignments. Preserve unknown inherited identities, capacity reservations and board quarantine.

The other fronts stay independently open: ordered handler priority; wrong/sibling permission; §21 Value/Computation entry; unmatched outward request plus suspended suffix; static-to-runtime projection. R95 method/role source identity, R97 ordinary entry and R92 runnable effectful source remain bounded evidence only. No semantic or parent gate changes.
