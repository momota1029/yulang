# R313 native source-callee witness — handoff revision 2

Revision 2 supersedes frozen revision 1, SHA-256
`9285bcdb9de3725055eebd6845fb56275b235da16767f00e1dd093a35dc2e6d8`, to
repair the independent regression review findings below.

Sprint contract: `tasks/agent-loop/sprints/source-callee-witness-r313.md`
SHA-256 `fbcc6748d0fcb2459670109f254064f64efce648cc020ad6b9a044700fbde1a9`.

Assignment: `/root/r313_callee_native`; parent gate is the unchanged R159
Simple-sub obligation and the R313 native source/return evidence edge.
Baseline `2bcca07070de18415abde1515cbfaa38e09bfb35`. Requested model/effort:
`gpt-6-luna/high`; observed model/effort and current runtime session:
`UNKNOWN`. No runtime metadata accessor was available to this worker.

## Outcome

Outcome class: **provisional source-native evidence**, test-only. The accepted
fixture parses and lowers the exact source below, runs `CandidateInference`
with no candidate conflicts, builds one `RuntimeProgram` from that HIR, then
runs one `Machine`. The test observes the same HIR and program throughout. It
does not claim source-to-constraint propagation completeness or close a parent
theorem.

```text
act io:
    our tick: int -> int
my make seed = { io::tick seed; \argument -> argument }
my relay value = make 1 value
my handle (thunk:[io] int) = catch thunk { io::tick(p), k -> handle { k 10 } }
my main = handle { relay 7 }
```

For the outer source Apply `make 1 value`, the retained source form decodes to
`Apply(callee=Label(9), argument=Label(10))`. Both labels are checked against
the actual source child occurrences and owner in the same HIR. Label 9 is the
inner `make 1` Apply; label 10 is the source `Name(value)` with
`NameConsumption::Observe`. Foreign HIR and swapped/other Apply labels are
rejected. The Name lookup occurs exactly once after callee selection and has
one Observe receipt; it returns integer 7 without a Force.

The run records one Request while the exact Apply's Callee frame is pending.
The same run-local frame token `F2` is consumed after resumption. Request owner
`Invocation(2)` and Return owner `Invocation(6)` are preserved separately;
they are not asserted equal. Immediately before the Callee frame creates its
argument Delay or dispatches the returned closure, the actual Return records
value 15, view 17, interface Value, dispatch None, and the closure provider
SourceSite. The received fields match the subsequent selection record.

At that Return point, the source argument is still an unexecuted Observe Name.
The snapshot resolves its caller environment 2 through the retained source
parameter to the already-populated Value cell 5 (value 4, view 5). A separate
actual ValueEntry bind event records that original caller initialization:
pre-bind cells 5/environments 2, bound cell 5/environment 2, Value value 4/view
5. The selected returned closure's own ValueEntry bind is separately retained
(cell 10/environment 7); it is not substituted for the original caller bind.
The actual post-Return Delay retains code label 10, caller environment 2 and
view 18. One Request total excludes resumed-suffix replay in this fixture.

The raw evidence uses intern aliases `H0/S0/A0/C0/G0/N0` joined in-process to
the nonserializable HIR/parse owners and to source text plus original ranges,
scope and CST keys. These aliases and runtime pointer text are fixture evidence
only; they are not stable cross-run HIR identities. The artifact separately
labels the complete cloned cells/environment/value vectors and Receiving view
vector at actual Callee Return. Final post-run counts are labeled separately.

## Artifacts and checks

Leased production path changed: `tools/inference-playground/src/runtime/machine.rs`
SHA-256 `9e74fe2e071df6c8e723707f608fdbe069dea45a55589bc26b102ec6b7c32ae7`.
`tools/inference-playground/src/runtime/program.rs` was inspected and remains
at its baseline SHA-256
`9c280992897b5664fef12e38df8161c4f1561a2d69654b1f5e1146339a3ca903`.

Generated source evidence:
`/tmp/yulang-r313-native/source-callee-witness.txt`, SHA-256
`7e98da35f51301ff0524cc7ea8b332532e17deb42afc80e029ab4a07e7443ea7`.
It includes exact source text, child and instruction labels, frame event order,
actual return fields/provider, separate request and return owners, original
caller bind, Callee Return arena snapshot, Delay and Name receipt/readout.

Direct inputs reused: R312 implementation baseline machine SHA-256
`caa627ce1829122a22034d83eecdb258a161410444a390d786d4e7a3a8ac281c`;
`program.rs` SHA above; R312 independent review
`tasks/agent-loop/history/20261103-callee-argument-history-r312-review.md`
SHA-256 `88fbaeb27447f3b234c8a204f4abed17e0ed759b97d46a69fd8e1bf95fe142b3`;
R312 applied Lean packet
`notes/theory/lean/YulangClosure/OriginalCalleeArgumentApplicationR312.lean`
SHA-256 `4bab607556ba9d0f89cb61db17ce8894fd87b9c0d14d44bc98437be9c03d4a26`.
R312 established conditional constructors and consumers, but its runtime
fixture used Execute and did not authenticate this actual source Return.

Focused offline checks after R1 repair:

- `env -u YULANG_R313_NATIVE_WITNESS cargo test --offline -p yu-playground r313_accepted_source_callee_returns_after_request_and_observes_value_name --lib` — **1 passed**. The existing scratch file hash was unchanged before and after this run, confirming the default test performs no export.
- `YULANG_R313_NATIVE_WITNESS=/tmp/yulang-r313-native/source-callee-witness.txt cargo test --offline -p yu-playground r313_accepted_source_callee_returns_after_request_and_observes_value_name --lib` — **1 passed** and refreshed the explicit evidence file above.
- `env -u YULANG_R313_NATIVE_WITNESS cargo test --offline -p yu-playground callee_argument_history_r312 --lib` — **2 passed**, preserving the old Execute fixture.
- `git diff --check -- tools/inference-playground/src/runtime/machine.rs tools/inference-playground/src/runtime/program.rs` — **passed**.

Revision 2 also puts the R313-only callee code/interface/dispatch observation
fields and their initializers behind `#[cfg(test)]`. The focused assertion now
checks that the original caller bind's value, view, Value interface and dispatch
agree with the Callee Return snapshot, verifies its before/after cell and
environment counts and parent link, and rejects a truncated Receiving vector.

The compiler emitted existing warnings from `yu-hir`, `yu-solver` and
`yu-playground`; no warning was promoted to an error. During development, one
compile-only borrow error and one overstrong Request-owner-equals-Return-owner
assertion were corrected. The latter contradicted R312's documented distinction
between the saved frame and resumed current owner; the final test retains both
owner observations and joins the same dynamic frame token instead.

Budget grant: 1800 seconds, fixed by contract. Exact accrued worker-active
seconds are `UNKNOWN` in the available runtime; no renewal or carryover is
requested. Heavy checks were serialized with the proof lane after Luna's slot
notifications.

## Parent application and remaining premises

This packet provides a concrete native instance for the source owner/Apply,
both child labels, initialized caller Value Name in Observe mode, pending
Callee frame, actual resumed Return value/view/provider, Delay and subsequent
Name readout edges. It supplies evidence that may be reified against R312
`Preparation`, allocation/capture/readback and the R311/R293 consumers when
their premises apply. It does not infer general semantics from one run.

Independent premises remain open: All-Reach world/license/observation/future,
callee membership, source-to-original-event correspondence, `q_c`/arms,
Checking, R159 admission, arbitrary-source quantification and every original
alternative. Source qualification of this single fixture, a test pass and the
frozen artifact do not close those obligations.

Mutual TODO for the R313 proof owner: reify the exact source text and the
artifact-local owner/child/range equations; apply the captured original caller
bind `(env 2, cell 5, Value value 4/view 5)` and Callee Return snapshot as
evidence to the unchanged parent edge; keep the selected closure bind
`(env 7, cell 10)` distinct; record any premise that prevents that application.
Falsifiers are an owner/child/label mismatch, a non-Observe Name, an
uninitialized/non-Value caller cell, different frame token, Return/provider
mismatch, early Name lookup, different Delay/view, foreign HIR, or replayed
Request suffix.

## Provisional boundary and stop

All R313 observation fields, state, hooks and export logic are behind
`#[cfg(test)]`; the witness file is written only when the test runner explicitly
sets `YULANG_R313_NATIVE_WITNESS`. Ordinary Cargo test runs never write to a
fixed `/tmp` path. No production runtime semantics or public API changed.
Cutover remains OPEN. Luna owns review,
integration and eventual cleanup of the provisional test instrumentation after
the source/proof evidence is adjudicated or superseded. This writer has stopped
all writes after freezing this revision; no Git operation was performed.
The independent source-fidelity verdict remains pending; this producer does
not self-certify that review gate.

Exact leased repository outputs: this inbox handoff and
`tools/inference-playground/src/runtime/machine.rs`. Exact leased scratch output:
`/tmp/yulang-r313-native/source-callee-witness.txt`. The scratch directory
contains only this source evidence file; no other generated or disposable
scratch files remain. An explicit export requires the directory/path to exist
and be writable; omitting the environment variable performs no file write.
