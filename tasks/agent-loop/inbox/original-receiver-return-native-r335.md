# R335 native response and selected receiver Return — revision 2

Assignment `R335-NATIVE-RECEIVER-RETURN`; baseline `55b636b69f2327904021ecc370cf4cb4f62bcf19`.
Worker `/root/r335_native`; requested model/effort Luna/high; observed model,
effort, and runtime launch receipt UNKNOWN to this worker. The exact writer
lease was `tools/inference-playground/src/runtime/machine.rs`, this handoff,
and `/tmp/yulang-r335-native`. No child agents or Git operation.

## Outcome and parent application

Outcome: **provisional source/native evidence**. The focused R323 fixture now
records the exact `ReceivedValue` delivered at the live continuation `Hole`,
then joins it against the prior `ResumeArgument` observation by request,
template, run, node and exact value/view/interface/dispatch identity. This
closes the observed exporter gap where a different valid `ViewHandle` for the
same `ValueHandle` passed `matches_value` and could be serialized as the
response.

The same fixture records the actual `Frame::ReceiverReturn` result after its
Value-interface construction, including activation, prior/current owner,
source call/provider sites and result value/view/dispatch. The exporter selects
this result by the authenticated source Call's `call.invocation`, checks that
its call site equals the selected call and that it returns after the response
Hole, and retains it separately from the R323 response execution owner. In this
run those are distinct roles: the resumed response owner is not used as the
selected source Call receiver activation. The artifact records response owner
`Invocation(5)`, Hole owner `Invocation(7)`, and selected source Call receiver
`Invocation(8)` at source occurrence 12; the selected provider is `make` at
occurrence 7. The actual selected Return is runtime value `7` at value/view
handles `4/5`, with Value interface and no dispatch. The exported receiver
result includes the actual runtime value constructor.

Independent review then found that this receiver Return observation could itself
be altered to another valid view of the same value. Revision 2 joins its entire
`ReceivedValue` tuple to an independently captured selected-definition result:
the cached result tuple consumed by `complete_selected_definition` immediately
before it emits `RuntimeOutcome::Completed`. The exporter requires exact
value/view/interface/dispatch equality, the same selected definition, and a
later step. The final artifact records selected-definition result value/view
`4/5`, owner `ModuleRun`, at step 73, preserving the receiver Return tuple.

This is finite runtime evidence only. It does not interpret the original
`Current`/world, establish the original Request/resume law, typed response/world
admission, lawful whole-tuple action, provider/future closure, original
`Inputs` instance, EI/Checking, or R293/R159. No source behavior, semantic
assumption, public API or production runtime decision changed. The added
observations are `#[cfg(test)]` only; the `ReceivedValue` used for normal state
propagation is constructed with the same fields as before.

## Reproduction and final checks

Before adding the Hole join, the existing accepted R323 fixture was temporarily
extended with this mutation: create `alternate = machine.receiving.ground(actual
response.value)`, assert `alternate != actual response.view`, replace only
`r323_resume_observations[0].response.view`, and ask the exporter to build its
artifact. The targeted Cargo command passed with an assertion that the exporter
accepted that same-value/different-view mutation, reproducing the defect.
That positive assertion was replaced with a rejection check in the final source.

Final ordinary-build command:

```sh
CARGO_TARGET_DIR=/tmp/yulang-r335-native/target cargo check --locked --offline -p yu-playground --lib
```

Result: **passed**, exit 0. This confirmed the test-only observations and their
initializers are excluded from the normal library build.

Final focused command (with revision-2 witness output):

```sh
CARGO_TARGET_DIR=/tmp/yulang-r335-native/target YULANG_R323_LEAN_WITNESS=/tmp/yulang-r335-native/r335-operation-source-r2.lean cargo test --locked --offline -p yu-playground r313_accepted_source_callee_returns_after_request_and_observes_value_name --lib
```

Result: **1 passed; 94 filtered out**. The focused test includes mutation
rejections for a different response value, same-value/different-view response,
altered or missing Hole evidence, wrong/missing selected receiver activation,
wrong source Call, wrong run, and missing receiver Return. It also checks the
emitted Hole and selected receiver result fields. It rejects same-value
alternate-view mutations of either the receiver result or selected-definition
result, and rejects a missing selected-definition completion receipt. `git diff
--check` passed for the two leased repository files. `rustfmt --check`
on the whole leased source file reports extensive pre-existing formatting
differences throughout the file, so no whole-file formatter was applied.

The revision-2 command regenerated the full artifact. Its SHA-256 is
`6783f166e8da158d2bb8047300999bc6eb60284a8027d3bf236905291306b5e7`. The exact
artifact was inspected for response value/view `14/16`, response owner 5, Hole
node 0 and owner 7, selected receiver activation/owner 8 and returned
value/view `4/5`, plus selected-definition result value/view `4/5` at step 73.
Lean elaboration of this regenerated artifact was not run.

Independent review of revision 1 found two blocking evidence defects. First,
two test-only Machine fields had `#[cfg(test)]`, but their initializers did not;
revision 2 guards both initializers. Second, `matches_value` alone could not
authenticate the receiver result's view identity; revision 2 joins it to the
selected-definition completion tuple as described above. A first attempt to
join against a frame-empty Return failed because the selected-definition driver
publishes completion from its cached result cell instead; that candidate was
removed and replaced by the actual `complete_selected_definition` boundary.
The final ordinary-build check and focused test above pass on revision 2.

One earlier transient compile failure came from a typo in the first version of
the test mutation (`ReceivedValue.response`); it was corrected before the
successful revision-1 reproduction and test. Lean elaboration was not run. The
leased scratch contains the isolated Cargo target tree and revision-1 regenerated
`.lean` witness. CPU/RSS were not instrumented.

## Frozen inputs and limits

| Path | SHA-256 | Use |
| --- | --- | --- |
| `tools/inference-playground/src/runtime/machine.rs` | `3727e1f4f32b9bed251a30224bd63b87a575d9ef84b97564f95e5774800a11c5` | revision-2 changed artifact |
| `tools/inference-playground/src/runtime/program.rs` | `2c03ff8681c50520e0527f139a86ac8427097c27aeafcf247e76673310be4b0c` | read-only source/program owner |
| `tools/inference-playground/src/runtime/receiving.rs` | `476ef914bb11449f106c900a233e9677025830e6923cd5db6a1dc6edbcc6d613` | read-only receipt/view implementation |
| `tools/inference-playground/src/runtime/continuation.rs` | `194e925c2e19816e05e8d0cdf773123f205dce47d36d83a70385daa07a77e2b3` | read-only template constructors |
| `tools/inference-playground/src/runtime/dispatch.rs` | `d99acad3e344bc06970faf0486ff7d10ba92bc7514cfb7eec58df8bbb28f6360` | read-only source dispatch |

Reused the reviewed R323/R324 structured request, template, response and owner
trace. Rejected prior inferences from same-value `matches_value` to exact
response/receiver-return view identity. Both identity falsifiers now fail closed
through independently recorded later source transitions. The outer-return join
uses the selected source Call identity, not the response's resumed execution
owner. Independent review remains required.

Changed repository paths: this handoff and `machine.rs`. Disposable scratch:
`/tmp/yulang-r335-native/target`. Cleanup owner: Luna after review and artifact
intake. Next in-envelope step: fresh source/native review of the frozen diff;
then have the original source-semantics owner consume the exact native IDs while
keeping the original world/action premises open until separately derived.
