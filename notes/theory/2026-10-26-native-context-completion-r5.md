# Native Context completion r5: concrete child enqueue callbacks

Status: constructed and kernel checked; independent review pending. Parent
MERGE-EXPANSION-COVER-1 and SourceProblem.InferenceSoundness remain OPEN.

## Frozen inputs and scope

Repository baseline: 97788357754a57562607dd8ff41ac55ffcb3c9b8. The leaf uses
NativeContextExpansion, NativeDrainOwnership, NativeReplayCurrent,
NativeExecutionHistory and NativeReplayAcknowledgement. The frozen predecessor
NativeContextReadback.lean was copied read-only from the earlier workspace;
SHA256: 321d087c8d2df5099f67beb75e4316d44114806bbfae2aa64ebda22a34bd83f2.
Its existence and this check do not establish independent acceptance.

The governing inference principles remain the authoritative 2026-10-11 design.
No source restriction, completion axiom, semantic callback, compiler edit,
dependency/configuration change, or scheduling/Git mutation is introduced.

## Substantive reduction

The old seam was Availability.enqueue child = true without an actual issued
work occurrence. NativeContextCompletion.enqueueChild now computes the child
using NativeReplayCurrent.admittedChild, checks the complete interned relation
and raw task entries, and retains the actual working caller/processing identity.
Successful insertion constructs NativeDrainOwnership.Step.enqueuePlain and the
existing NativeContextReadback.Step.control from the same input state. The
returned Receipt has a genuinely queued and issued Work with no Replay ticket.
The Context is the child's source-local Context, and the source set and whole
transformer are inherited from the original parent. Existing relation IDs still
produce fresh work serials; no pair memo suppresses this callback.

The callback keeps admission/dependency before queue reservation. Failed
reservation returns no receipt, preserves the queue/caller/memo, and retains the
already emitted dependency. enqueueChildren traverses in order, constructs one
forward readback Run, and returns both completed receipts and the exact unrun
suffix. Earlier receipts remain issued if a later callback fails.

finish_after_callbacks composes that actual forward run with the existing
completed owner constructor. callbacks_settled_readback applies its actual
issued occurrences to the existing later quiescent history: every emitted child
has a resolved receipt and RouteValid readback; all transferred Replay tickets
have diagnosed acknowledgements. Later history is explicit and can contain
merges and duplicate exits. Its existence is NOT proved by this module.

## Source owners and preserved ordering

- candidate_context.rs candidate_context_admit: source-local Context, relation
  interning, Derived attachment, resource sample, successful relation return.
- candidate_effect.rs candidate_enqueue_evidence: delegates to that admission.
- lib.rs enqueue_item: evidence admission, reserve_worklist, Replay transfer
  when present, queue journal, infallible front/back insertion.
- lib.rs dispatch_live_item: pair-current check follows Context execution;
  memo admission precedes operand execution. An admitted memo is not completion.
- lib.rs step_typed_drain: Context precedes Dispatch; current clears only after
  the dispatch owner completes; Diagnostics precedes acknowledgements.

The selected relation/task IDs and resource-success bit are raw operational
inputs, not proofs of typing or completion. intern_child_event constructs the
fresh interner case using its actual vacant-slot and uniqueness guards.

## Explicit omissions and first remaining premise

The frozen predecessor has no child-admission Derived event. Therefore callback
dependency emissions are returned in CallbackState.derived separately from its
actual readback Run projection. No theorem claims they already appear in
NativeContextReadback.State.edges. This is a concrete missing admission-owner
integration event, not an assumed native refinement.

Whole-body emitted-list equality is explicit in finish_after_callbacks. It is a
raw constructor/list correspondence premise, not a current-child or recursive
coverage law. The next local reduction is to derive that list from the exact
collect/admit construction, and to cover Replay-bearing queue callbacks.
Actual HashMap ID selection/allocation and Rust-to-event extraction remain
separate source obligations. Physical bound/replay callbacks, Value structured
ports, table lifetime across cancellation, and whole-language typing are not
closed here. Nested settlement can retain an outer active owner, as the
predecessor explicitly records; no universal completed-owner claim is made at
such a cut.

## Verification, stage 1

Task-local official Lean 4.35.0 / Lake 5.0.0-src+eb6cafb. The first sandboxed
lake env lean --version failed with 'could not detect the configuration of the
Lake installation'; the exact isolated checker commands work with the permitted
execution escalation. No installation or dependency change was used.

Isolated immutable-baseline project:
/workspace/scratch/c10e953a5453/context-completion-r5/project.
Each Lean command has -j1 -M1024 and a 120 second bound. At most one Lean process
was active. Five focused builds plus the all-authored-root checker were used at
this checkpoint; one early build failed on conjunction association, front-queue
membership simplification, and Nat zero-add simplification, then was repaired.
All 24 authored theorems passed the skill's type/kind/full-transitive-axiom audit.
Full log: context-completion-r5/audit-stage1.log in task scratch.

Axiom lists: native_step_issued_retained and native_run_issued_retained use
[propext]; callbacks_settled_readback uses [propext, Classical.choice, Quot.sound];
all other stage-1 authored roots use [propext, Quot.sound]. No sorry, admit,
custom axiom or checker bypass was introduced. Default-root build and independent
review were not run by this leaf; root integration owns them.

Stage-1 Lean SHA256:
5bc4bb4151087462cfbede6f0d6accece70c41ea5061f1ef100ad081e28344b4.

The leaf continues only in its scratch project pending the next coherent
checkpoint; leased delivered source bytes above are frozen for primary intake.
