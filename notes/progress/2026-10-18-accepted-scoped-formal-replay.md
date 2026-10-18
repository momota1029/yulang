# Accepted scoped formal Replay fixture

Sprint `npair-operation-rule-completion-and-accepted-replay-20261018`,
contract revision 1, SHA-256
`e9ea1ebb5db72ebcf7348e512206a1b39b8e60232d2bff5459f0bc394f7526f0`.
Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR-20261017` remains OPEN; original
conditions closed: 0.

## Prior failure diagnosis

The frozen test run compiled and passed the five existing selected tests, then
failed at the new test's `hir.errors().is_empty()` assertion (line 460 in the
frozen test). The captured output reports only the boolean assertion; it does
not print the `HirError` vector, kind, attachment, or source range. The prior
test artifact is named by SHA-256
`6610fc337dad7d417ae227d12b7c74978741f7d4d2222f6a4c2d6005f2a62529`, but those
bytes are no longer present in the workspace. The previous handoff records the
source literal, but not enough lowering-call detail to identify which HIR error
producer ran. I therefore cannot recover the exact prior diagnostic kind or
span without repeating the stopped command, which this contract forbids.

The prior handoff records the source literal
`my invoke f = f 1; my id x = x; my received = invoke id`. The matching
source-owner history in
`notes/theory/2026-10-17-accepted-call-hir-projection.md` traces the accepted
HIR helper path: the prior `lower_module_with_local_source` route formed a
LocalSource carrier but projected each non-atom Apply body as
`SimpleBodyProjection::Unsupported`; `module::lower_body` then emitted
`HirErrorKind::UnsupportedExpression`, attached to `Value(def_id)` over the
body-chain range. For this literal, source-static ranges are `[14,17)` for
`f 1` and `[46,55)` for `invoke id`. The predicted errors are therefore the
`invoke` body's formal Apply and the `received` body's outer Apply. This
explains why that helper failed the zero-HIR-error gate.

The accepted route is ordinary `lower_module`, as in
`crates/yu-solver/tests/research_accepted_call_vertical.rs::module`. Its
approved ordinary-application admission returns an Apply-shaped HIR with no
structural application error while also forming ordinary source-carrier
outcomes. The replacement uses that HIR for scoped candidate inference, so it
does not disable the zero-HIR assertion or substitute a separate source parse.

The prior runtime log still did not serialize the error records, IDs, or
observed ranges. The two kinds/owners/ranges above are static producer/source
predictions from the recorded literal and reviewed owner path, not runtime
captured diagnostic entries. The old assertion exposed no payload, so exact
runtime records cannot be claimed without the prohibited rerun.

## Replacement source-to-propagation path

The focused regression and example now use the accepted source:

```yu
my invoke f = f 1
my id x = x
my received = invoke id
```

The regression uses the ordinary accepted `lower_module` route, checks syntax
and HIR diagnostics with their full payloads on failure, and uses one resulting HIR
for the scoped inference run. It authenticates `invoke`'s formal Apply against
the retained omitted-formal introduction and exact native demand. It separately
authenticates the outer `received = invoke id` Apply by its source owner and
occurrence. The candidate graph must show the integer lower propagating to the
`received` result.

The existing typed Replay observer is opt-in and unchanged. The example prints
`invoke`'s formal Apply call index; the authorized runtime capture must show a
typed Replay row for that index, matching that call's native demand root and
both ordered endpoint checks. `received`'s outer provider Apply has a distinct
call index and must not be used as the Replay key. A missing/mismatched runtime
row remains a falsifier.

This fixture is provisional source/native candidate evidence. It does not prove
original Call typing, source-domain admission, the fixed-c theorem, parent
closure, or production readiness. No compiler implementation, solver
semantics, source admission, or expected output changed.

Falsifier: either authorized command fails, no typed Replay row is emitted for
`invoke`'s formal Apply, the row's native root differs from that Apply's demand,
or either ordered endpoint check is false. Luna owns cleanup of this provisional
fixture/evidence path if the row fails owner correspondence or semantics-neutral
checks.

## Checks and boundary

No new command was run by this author. The frozen previous test command failed
once and its contract prohibited retry; the example was not run. The new exact
focused test and example commands remain pending a frozen independent CLEAN
review and a fresh primary-owned capacity measurement/release of at least 120
seconds. Any command failure stops the packet without retry.

Requested model/effort: Luna/high. Observed model/effort: UNKNOWN/UNKNOWN.
Parent theorem conditions closed: 0. No provisional output has been promoted.
