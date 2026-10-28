import YulangClosure.OriginalDrainBoundary
import YulangClosure.OriginalReplayDrain

/-!
Apply the actual first-empty boundary to the computed Replay/port consumers.
The previous stack-depth premise is derived from the unchanged control
constructors and the same frame's immutable birth/index identity.
The conclusions are actual processing facts, not semantic subtyping or
global inference termination.
-/
namespace YulangClosure.OriginalReplayBoundary

open NativeDrainOwnership
open OriginalDrainBoundary
open OriginalReplayDrain (Indexed Processed BeforeReturn indexed_member run_indexed)
open NativeValuePorts (Key Pair)

/-- The still-owned-drain condition follows from the first-boundary property
and real frame preservation; it is no longer an independent history premise. -/
theorem first_boundary_before_return {owner : Owner} {start last : State}
    (past : BeforeBoundary owner start last) (live : Working owner start)
    (indexed : Indexed start.frames) : BeforeReturn owner.index start last := by
  induction past with
  | nil => exact BeforeReturn.nil _
  | snoc history step absent ih =>
    have kept := before_boundary_working history live
    have ordered := run_indexed (before_boundary_run history) indexed
    have depth := working_depth kept (fun frame member => indexed_member ordered member)
    exact BeforeReturn.snoc ih depth step

/-- Queue membership is supplied by the actual enqueue producer. No final
processing fact, consumed-cursor equality or empty whole stack is assumed. -/
theorem queued_at_first_boundary {owner : Owner} {start last : State} {work : Work}
    (past : BeforeBoundary owner start last) (live : Working owner start)
    (indexed : Indexed start.frames) (queued : work ∈ start.queue)
    (boundary : EmptyBoundary owner last) : Processed last work := by
  obtain ⟨frame, rest, top, same, phase, current, empty⟩ := boundary
  have ordered := run_indexed (before_boundary_run past) indexed
  rw [top] at ordered
  have position := congrArg Owner.index same
  change frame.index = owner.index at position
  have floor : rest.length = owner.index := ordered.1.symm.trans position
  exact OriginalReplayDrain.queued_before_empty_transport
    (first_boundary_before_return past live indexed) indexed queued empty top floor current

/-- Ordinary Replay leaves the frames themselves unchanged, even though it
extends operation state, the issued history, the worklist and exact tickets. -/
theorem ordinary_drive_frames (start : State) (task : Nat) (children : List Child)
    (resources : State → OriginalReplayDrain.Resources)
    (active : ∃ frame rest, start.frames = frame :: rest ∧ frame.phase = .working) :
    (OriginalReplayDrain.ordinaryDrive resources start.nextOperation
      (OriginalReplayDrain.begin start task children)).1.frames = start.frames := by
  have computed := OriginalReplayDrain.ordinary_drive_batch
    (OriginalReplayDrain.begin_at start task children) resources active
  exact computed.2.1

/-- This applies first-boundary preservation to the executable, fuel-free
ordinary Replay loop. All output occurrences retain their real task, raw
RelationId and birth/operation/index/relation ticket. -/
theorem ordinary_children_at_first_boundary
    (start : State) (task : Nat) (children : List Child)
    (resources : State → OriginalReplayDrain.Resources) (owner : Owner)
    (active : ∃ frame rest, start.frames = frame :: rest ∧ frame.phase = .working)
    (live : Working owner start) (indexed : Indexed start.frames)
    {last : State}
    (normal : (OriginalReplayDrain.ordinaryDrive resources start.nextOperation
      (OriginalReplayDrain.begin start task children)).2 = .complete ∨
      (OriginalReplayDrain.ordinaryDrive resources start.nextOperation
      (OriginalReplayDrain.begin start task children)).2 = .queued)
    (past : BeforeBoundary owner
      (OriginalReplayDrain.ordinaryDrive resources start.nextOperation
        (OriginalReplayDrain.begin start task children)).1 last)
    (boundary : EmptyBoundary owner last) :
    ∀ index, index < children.length →
      ∃ child, children[index]? = some child ∧
        ∃ work, work.task = child.task ∧ work.relation = child.relation ∧
          work.ticket = some ⟨start.nextBirth, start.nextOperation, index, child.relation⟩ ∧
          Processed last work := by
  have issued := OriginalReplayDrain.ordinary_return_issues_all start task children resources active
  have kept := ordinary_drive_frames start task children resources active
  have postLive : Working owner (OriginalReplayDrain.ordinaryDrive resources start.nextOperation
      (OriginalReplayDrain.begin start task children)).1 := by
    change WorkingFrames owner _
    rw [kept]
    exact live
  intro index bound
  obtain ⟨child, found, work, _, pending, taskMatch, relation, ticket⟩ :=
    issued.2.2 normal index bound
  exact ⟨child, found, work, taskMatch, relation, ticket,
    queued_at_first_boundary past postLive (run_indexed issued.1 indexed) pending boundary⟩

/-- The production Replay stores one task and a raw RelationId vector. This
specialization keeps exactly that representation throughout the native run. -/
theorem ordinary_relation_at_first_boundary
    (start : State) (task : Nat) (relations : List Nat)
    (resources : State → OriginalReplayDrain.Resources) (owner : Owner)
    (active : ∃ frame rest, start.frames = frame :: rest ∧ frame.phase = .working)
    (live : Working owner start) (indexed : Indexed start.frames)
    {last : State}
    (normal : (OriginalReplayDrain.ordinaryDrive resources start.nextOperation
      (OriginalReplayDrain.begin start task (OriginalReplayDrain.replayChildren task relations))).2 = .complete ∨
      (OriginalReplayDrain.ordinaryDrive resources start.nextOperation
      (OriginalReplayDrain.begin start task (OriginalReplayDrain.replayChildren task relations))).2 = .queued)
    (past : BeforeBoundary owner
      (OriginalReplayDrain.ordinaryDrive resources start.nextOperation
        (OriginalReplayDrain.begin start task (OriginalReplayDrain.replayChildren task relations))).1 last)
    (boundary : EmptyBoundary owner last)
    {index relation : Nat} (found : relations[index]? = some relation) :
    ∃ work, work.task = task ∧ work.relation = relation ∧
      work.ticket = some ⟨start.nextBirth, start.nextOperation, index, relation⟩ ∧
      Processed last work := by
  have childAt := OriginalReplayDrain.replay_child_exact task relations index relation found
  have bound := (List.getElem?_eq_some_iff.mp childAt).1
  obtain ⟨child, actual, work, taskMatch, origin, ticket, processed⟩ :=
    ordinary_children_at_first_boundary start task (OriginalReplayDrain.replayChildren task relations)
      resources owner active live indexed normal past boundary index bound
  have same : child = ⟨task, relation⟩ := by simpa [childAt] using actual.symm
  subst child
  exact ⟨work, taskMatch, origin, ticket, processed⟩

namespace V
export NativeValueRelationExecution (Funding Store State start origin drive)
end V

/-- Derive frame preservation from the same computed physical admission and
enqueue run. It is not a supplied frame-equality postcondition. -/
theorem physical_drive_frames
    {resources : Nat → V.Funding} {views : Nat → Option (Option Nat)}
    {qv qe : Nat → Nat} {parent : Key} {post : Nat} {derived : Bool}
    {store : V.Store} {children : List NativeValuePorts.Child} {control : State}
    {tasks : List Pair} {fuel : Nat} {emitted : V.State}
    (history : NativeRelationInterner.NativeHistory store.native)
    (active : NativeValueDrain.Active parent
      (NativeValueDrain.start (V.origin store children control tasks)))
    (computed : V.drive resources views qv qe parent post derived fuel
      (V.start store children control tasks) = some emitted) :
    emitted.control.frames = control.frames := by
  obtain ⟨_, pure⟩ := NativeValueRelationExecution.drive_refines_emit history computed
  rw [NativeValueRelationExecution.start_decoded] at pure
  have initial := NativeValueDrain.start_invariant views qv qe parent post derived
    (V.origin store children control tasks) active
  obtain ⟨run, _⟩ := NativeValueDrain.emit_constructs_run initial pure
  exact (NativeValueDrain.run_invariant run initial).frames

/-- All exact physical keys and port admissions are retained. The only
continuation premise is the actual finite prefix to this same owner's first
empty boundary; its old depth condition is derived, not assumed. -/
theorem physical_children_at_first_boundary
    {resources : Nat → V.Funding} {views : Nat → Option (Option Nat)}
    {qv qe : Nat → Nat} {parent : Key} {post : Nat} {derived : Bool}
    {store : V.Store} {children : List NativeValuePorts.Child} {control : State}
    {tasks : List Pair} {fuel : Nat} {emitted : V.State} (owner : Owner)
    (history : NativeRelationInterner.NativeHistory store.native)
    (indexed : Indexed control.frames) (live : Working owner control)
    (active : NativeValueDrain.Active parent
      (NativeValueDrain.start (V.origin store children control tasks)))
    (computed : V.drive resources views qv qe parent post derived fuel
      (V.start store children control tasks) = some emitted) :
    ∃ jobs : List NativeValueDrain.Issuance,
      jobs.map (fun job => job.port.source) = children ∧
      (∀ job ∈ jobs,
        job.matches emitted.tasks ∧
        NativeValuePorts.AdmissionResult emitted.store.arena views qv qe parent post derived
          job.port.source job.port.receipt ∧
        emitted.store.native.store.readback job.port.receipt.relation = some job.port.receipt.child) ∧
      ∀ last, BeforeBoundary owner emitted.control last → EmptyBoundary owner last →
        ∀ job ∈ jobs, Processed last job.occurrence := by
  obtain ⟨_, run, jobs, sources, every, _⟩ :=
    OriginalReplayDrain.physical_children_before_empty history indexed active computed
  have frames := physical_drive_frames history active computed
  have postLive : Working owner emitted.control := by
    change WorkingFrames owner emitted.control.frames
    rw [frames]
    exact live
  refine ⟨jobs, sources, ?_, ?_⟩
  · intro job member
    have supplied := every job member
    exact ⟨supplied.1, supplied.2.1, supplied.2.2.1⟩
  · intro last past boundary job member
    exact queued_at_first_boundary past postLive (run_indexed run indexed)
      (every job member).2.2.2 boundary

/-- All four original Function ports, including both Effect ports, reach
real processing at the same first-empty boundary. The physical Request key
is not replaced by its Value endpoints or a semantic equivalence class. -/
theorem function_four_ports_at_first_boundary
    {resources : Nat → V.Funding} {views : Nat → Option (Option Nat)}
    {qv qe : Nat → Nat} {parent : Key} {post : Nat} {derived : Bool}
    {store : V.Store} {control : State} {tasks : List Pair} {fuel : Nat}
    {emitted : V.State} (owner : Owner) (terms : NativeValuePorts.TermEndpoints)
    (lower upper : NativeValuePorts.FunctionTerms)
    (history : NativeRelationInterner.NativeHistory store.native)
    (indexed : Indexed control.frames) (live : Working owner control)
    (active : NativeValueDrain.Active parent (NativeValueDrain.start
      (V.origin store (NativeValuePorts.functionChildren terms lower upper) control tasks)))
    (computed : V.drive resources views qv qe parent post derived fuel
      (V.start store (NativeValuePorts.functionChildren terms lower upper) control tasks) = some emitted) :
    ∃ jobs : List NativeValueDrain.Issuance,
      jobs.map (fun job => job.port.source) = NativeValuePorts.functionChildren terms lower upper ∧
      jobs.map (fun job => job.port.source.port) =
        [.function .argument, .function .argumentEffect, .function .resultEffect, .function .result] ∧
      jobs.length = 4 ∧
      (∀ job ∈ jobs,
        emitted.tasks[job.occurrence.task]? = some job.port.source.task ∧
        job.occurrence.relation = job.port.receipt.relation ∧
        emitted.store.native.store.readback job.occurrence.relation = some job.port.receipt.child ∧
        job.port.receipt.child.pair = job.port.source.task.rename qv qe) ∧
      ∀ last, BeforeBoundary owner emitted.control last → EmptyBoundary owner last →
        ∀ job ∈ jobs, Processed last job.occurrence := by
  obtain ⟨jobs, sources, every, processed⟩ :=
    physical_children_at_first_boundary owner history indexed live active computed
  refine ⟨jobs, sources, ?_, ?_, ?_, processed⟩
  · have ports := congrArg (List.map NativeValuePorts.Child.port) sources
    simpa [List.map_map, Function.comp_def, NativeValuePorts.functionChildren] using ports
  · have size := congrArg List.length sources
    simpa [NativeValuePorts.functionChildren] using size
  · intro job member
    obtain ⟨matched, checked, readback⟩ := every job member
    exact ⟨matched.1, matched.2.1, by simpa [matched.2.1] using readback, checked.pair_exact⟩

end YulangClosure.OriginalReplayBoundary
