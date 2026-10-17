# Actual-argument source-path experiment

Sprint `npair-actual-argument-ingress-20261018`, contract revision 1,
SHA-256 `c0754dc6de94c15e923ce24cc58b8208d0934dcf7bc92abcae34589185ec9d32`.

## Outcome

The authorized line `my received = receive f0` parses without structural
recovery, but this source addition is refused at HIR lowering. This records
only that the experiment did not produce an HIR call site; it is not negative
evidence against the parent theorem or the proposed `s1 -> D` edge. The printed
HIR errors include `UnsupportedExpression` for `received` at range `372..382`
and for `f0` at `147..162`, plus `UnsupportedItem` at `80..130` and
`UnsupportedExpression` for `receive` at `328..356`. The example then returns
exit code 0 after running the candidate experiment on the partial HIR; that is
not acceptance of the added binding. The `received` expression is absent from
HIR local-source output, so it has no collector coverage and no source-to-call
constraint edge.

The partial HIR does retain `receive`'s body: `f ()` is Apply occurrence 10
(callee parameter `f`, argument Unit), its result is bound as local `g`, and
`g ()` is Apply occurrence 13 (callee local `g`, argument Unit). This is the
existing body shape, not an invocation of `receive` with `f0` and not evidence
that either Apply's returned Function field reaches a Permission negative port.
The `ctrl::choose` use in `f0` resolves to the lowered `choose` declaration
(`Arc::ptr_eq` was true); that resolved declaration is also unrelated to the
missing outer binding.

## Source-owner correspondence inspected

All seven read-only pins matched their contract SHA-256 values before the run.
In `candidate_source.rs`, each lowered `LocalSourceForm::Apply` visited by the
collector retains a generic `CandidateRelation::Apply` and an
`ApplySourceInput` with callee, argument, result, and effect endpoints. The
experiment also has a scoped collector gate for some Apply shapes. Since HIR
did not lower `received`, neither this generic capture nor the gate covers its
proposed Apply.

In `candidate_call.rs`, `CandidateSourceCall` authenticates an existing Apply
and its source endpoints, but construction requires `input.native` to already
be present. Its `PendingCallConstruction` exposes original Gen-Call-0 inputs
and lists `OriginalGenCall0` among suppliers; these are requests for missing
construction inputs, not a constructed Call for this binding. No inspected
owner associates the proposed call's actual `f0` with the formal `f`, or
compares the returned Function's written `s1` against `D`.

`candidate_context.rs` has generic Function-port admission, which chooses
Swap/Preserve by `FunctionField`, and generic ordered Replay construction from
`lower_input` and `upper_input`. `candidate_extrusion.rs` also creates generic
replay inputs from admitted bounds. No inspected source path supplies the
actual `s1` and `D` bound keys for this proposed call, identifies the Function
comparison that owns them, or connects both ordered Replay inputs to it.
`candidate_scheme.rs` and `candidate_effect.rs` provide no such bridge for the
added binding in the inspected owners. Thus the `f0 -> actual Apply -> receive
formal` edge, its Call/Function comparison, `s1 -> D`, both Replay inputs,
propagation, and execution remain unestablished.

## Receipt and disposition

Exact command, run once:

```sh
timeout 120s cargo run --offline --manifest-path crates/yu-solver/Cargo.toml --example research_source_registration --features shadow-apply-candidate
```

Exit code: 0. The command compiled the example and printed
`parse.structural_recoveries=[]`, the HIR errors above,
`candidate.observes_hir=true`, `candidate.conflicts=[]`, and an export only for
the `f0` definition root. It did not print an export for `received` or expose
its call to candidate collection. These are partial-run observations, not
evidence that the refused HIR route was solved.

After recording this receipt, the fixture was restored byte-for-byte to its
pinned baseline SHA-256
`969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0`.
No other input, code, harness, expected output, test, manifest, or API changed.

The next discriminating owner is the HIR lowering implementation that emits
the observed `UnsupportedExpression` for the added module binding (source
range `372..382`; likewise the existing fixture's ranges `147..162` and
`328..356`). Its exact file was outside the six pins and was not read. Luna
must identify and pin that owner before any further source experiment. Once
HIR exposes the outer Apply, a later separately leased source trace must still
establish collector coverage, actual argument/formal routing, the same R1,
the Function field comparison to `D`, and both ordered Replay inputs. The
present result does not establish `s1 -> D`, a hidden `s1 -> D` premise, an
`At`/N-Subtract edge, H0/L2 completion, or parent closure.

## Bounds and runtime

Requested role/model/effort: `Luna/implementer/high`. Observed model and effort:
`UNKNOWN` in current sprint state; no model introspection is available to this
worker. One Cargo process ran, below its 120-second timeout. No other check or
build ran. The fixture writer stopped after restoration. This assignment
produced a source-path probe, not an implementation or production change.
