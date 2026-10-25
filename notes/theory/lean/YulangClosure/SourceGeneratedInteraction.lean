import YulangClosure.HandlerGraphRecursiveTrace

/-! Candidate source-generated histories for the existing research machine.
The initial guard and each allocation's finite fresh-cycle criterion construct
the final guard. No final graph typing, rank, or guard is a history premise.
This does not strengthen generic Run or establish full-paper/native coverage.
Author: /root/source_generated_proof_20261025. Checker/review owned by primary. -/
namespace YulangClosure.HandlerGraph.Combined.SourceGenerated
open HigherOrder (Ty Context emptyContext OperationInstance)
open YulangClosure.HandlerGraph.Extension
open YulangClosure.HandlerGraph.Recursive

/-- Data retains the actual finite allocation history, so its guard can be
constructed without choice. Old references may have any Type; each fresh family
has arbitrary finite size, including zero. Publication and answering have exactly
the existing Run interfaces; only its unrestricted extension is specialized. -/
inductive History (B : Type) (initialGraph : Graph B) (initialTypes : B → Ty)
    (initial : Comp B Empty) :
    (R : Type) → Graph R → (R → Ty) → Comp R Empty → List (Saved R) → Type 1 where
  | start : History B initialGraph initialTypes initial
      B initialGraph initialTypes initial []
  | internal {R : Type} {graph : Graph R} {xi : R → Ty}
      {current next : Comp R Empty} {event : Event R} {arena : List (Saved R)} :
      History B initialGraph initialTypes initial R graph xi current arena →
      Step graph current event next →
      History B initialGraph initialTypes initial R graph xi next arena
  | publish {R : Type} {graph : Graph R} {xi : R → Ty}
      {arena : List (Saved R)} (saved : Saved R) :
      History B initialGraph initialTypes initial R graph xi saved.suspended arena →
      History B initialGraph initialTypes initial R graph xi saved.suspended (saved :: arena)
  | allocation {R : Type} {graph : Graph R} {xi : R → Ty}
      {current : Comp R Empty} {arena : List (Saved R)}
      {n : Nat} {nu : Fin n → Ty} {env : Context}
      (rhs : Fin n → Value R Empty) (capture : Nat → Value R Empty) :
      History B initialGraph initialTypes initial R graph xi current arena →
      (∀ s, ValueTyped xi emptyTy (sourceContext nu env) (rhs s) (nu s)) →
      CapturesTyped xi env capture → FreshNoCycle (sourceFresh capture rhs) →
      History B initialGraph initialTypes initial (Sum R (Fin n))
        (allocate graph (sourceFresh capture rhs)) (joinTy xi nu)
        (mapComp Sum.inl current) (arena.map (Saved.map Sum.inl))
  | answer {R : Type} {graph : Graph R} {xi : R → Ty} {saved : Saved R}
      {current next : Comp R Empty} {arena : List (Saved R)}
      {operation : OperationInstance} {response : Value R Empty} :
      History B initialGraph initialTypes initial R graph xi current arena →
      saved ∈ arena → Answer saved operation response next →
      ValueTyped xi emptyTy emptyContext response operation.responseType →
      History B initialGraph initialTypes initial R graph xi next arena

variable {B R : Type} {initialGraph : Graph B} {initialTypes : B → Ty}
  {initial : Comp B Empty} {graph : Graph R} {xi : R → Ty}
  {current : Comp R Empty} {arena : List (Saved R)}

theorem History.graphTyped
    (history : History B initialGraph initialTypes initial R graph xi current arena)
    (typed : WellTyped initialGraph initialTypes) : WellTyped graph xi := by
  induction history with
  | start => exact typed
  | internal _ _ ih => exact ih
  | publish _ _ ih => exact ih
  | allocation rhs capture _ hrhs hcapture _ ih =>
      exact source_allocation_typed ih hrhs hcapture
  | answer _ _ _ _ ih => exact ih

/-- This is data, not Nonempty followed by a choice oracle. Every local rank
comes from allocationGuard's existing finite algorithm. -/
def History.graphGuard
    (history : History B initialGraph initialTypes initial R graph xi current arena)
    (guard : GuardedValueGraph.Guarded (projectGraph initialGraph)) :
    GuardedValueGraph.Guarded (projectGraph graph) := by
  induction history with
  | start => exact guard
  | internal _ _ ih => exact ih
  | publish _ _ ih => exact ih
  | allocation rhs capture _ _ _ cycle ih =>
      exact allocationGuard ih (sourceFresh capture rhs) cycle
  | answer _ _ _ _ ih => exact ih

/-- The packet's cycle falsifier is ruled out on the actual final projection,
including paths crossing allocation boundaries. Typing is not used here. -/
theorem History.no_transparent_cycle
    (history : History B initialGraph initialTypes initial R graph xi current arena)
    (guard : GuardedValueGraph.Guarded (projectGraph initialGraph)) (r : R) :
    ¬ GuardedValueGraph.TransparentPath (projectGraph graph) r r :=
  GuardedValueGraph.no_transparent_cycle (history.graphGuard guard) r

/-- Erasure supplies the target typing demanded by generic Run.extension from
the source constructor's RHS/capture derivations, rather than assuming it. -/
theorem History.erase
    (history : History B initialGraph initialTypes initial R graph xi current arena)
    (typed : WellTyped initialGraph initialTypes) :
    Run B initialGraph initialTypes initial R graph xi current arena := by
  induction history with
  | start => exact .start
  | internal _ step ih => exact .internal ih step
  | publish saved _ ih => exact .publish saved ih
  | allocation rhs capture prior hrhs hcapture _ ih =>
      exact run_source_extension ih (prior.graphTyped typed) rhs hrhs capture hcapture
  | answer _ member matched responseTyped ih =>
      exact .answer ih member matched responseTyped

theorem History.invariant
    (history : History B initialGraph initialTypes initial R graph xi current arena)
    (typed : WellTyped initialGraph initialTypes)
    (initialTyped : CompTyped initialTypes emptyTy emptyContext initial result) :
    WellTyped graph xi ∧ CompTyped xi emptyTy emptyContext current result ∧
      ∀ s, s ∈ arena → SavedTyped xi s result :=
  run_invariant typed initialTyped (history.erase typed)

/-- An actual immutable chain retains every original node and its type, not
only the values referenced by the current computation or latest arena entry. -/
def History.chain
    (history : History B initialGraph initialTypes initial R graph xi current arena) :
    Chain B initialGraph initialTypes R graph xi := by
  induction history with
  | start => exact .refl
  | internal _ _ ih => exact ih
  | publish _ _ ih => exact ih
  | allocation rhs capture _ _ _ _ ih =>
      exact .snoc ih (sourceEmbedding _ _ _ capture rhs)
  | answer _ _ _ _ ih => exact ih

theorem History.old_nodes
    (history : History B initialGraph initialTypes initial R graph xi current arena)
    (r : B) :
    graph (history.chain.embedding.refs r) =
      mapValue history.chain.embedding.refs (initialGraph r) ∧
    xi (history.chain.embedding.refs r) = initialTypes r :=
  ⟨history.chain.embedding.nodes r, history.chain.embedding.types r⟩

/-- Every entry has reached-root provenance and an origin typing derivation.
The existing generic provenance theorem is consumed after source erasure. -/
theorem History.saved_origin_typed
    (history : History B initialGraph initialTypes initial R graph xi current arena)
    (typed : WellTyped initialGraph initialTypes)
    (initialTyped : CompTyped initialTypes emptyTy emptyContext initial result)
    (saved : Saved R) (member : saved ∈ arena) :
    ∃ (V : Type) (originGraph : Graph V) (originTypes : V → Ty)
      (origin : Saved V) (originArena : List (Saved V)),
      Run B initialGraph initialTypes initial V originGraph originTypes
        origin.suspended (origin :: originArena) ∧
      SavedTyped originTypes origin result ∧
      ∃ chain : Chain V originGraph originTypes R graph xi,
        saved = origin.map chain.embedding.refs :=
  run_saved_origin_typed typed initialTyped (history.erase typed) saved member

theorem History.prefix_safety
    (history : History B initialGraph initialTypes initial R graph xi current arena)
    (typed : WellTyped initialGraph initialTypes)
    (initialTyped : CompTyped initialTypes emptyTy emptyContext initial result)
    (guard : GuardedValueGraph.Guarded (projectGraph initialGraph))
    (steps : Prefix graph current trace last) :
    CompTyped xi emptyTy emptyContext last result ∧ CanProgress graph last ∧
      (∀ s, s ∈ arena → SavedTyped xi s result) :=
  run_prefix_safety typed initialTyped (history.erase typed) (history.graphGuard guard) steps

theorem History.prefix_four
    (history : History B initialGraph initialTypes initial R graph xi current arena)
    (typed : WellTyped initialGraph initialTypes)
    (initialTyped : CompTyped initialTypes emptyTy emptyContext initial result)
    (guard : GuardedValueGraph.Guarded (projectGraph initialGraph))
    (steps : Prefix graph current trace last) :
    (∃ v, last = .ret v) ∨ (∃ op p k, last = .request op p k) ∨
      (∃ reason, last = .fail reason) ∨ ∃ event next, Step graph last event next :=
  run_prefix_four typed initialTyped (history.erase typed) (history.graphGuard guard) steps

/-- Each independently typed response to ANY saved entry enjoys the same
all-prefix result. No restriction to the newest entry or old-world responses. -/
theorem History.all_saved_responses
    (history : History B initialGraph initialTypes initial R graph xi current arena)
    (typed : WellTyped initialGraph initialTypes)
    (initialTyped : CompTyped initialTypes emptyTy emptyContext initial result)
    (guard : GuardedValueGraph.Guarded (projectGraph initialGraph))
    (s : Saved R) (member : s ∈ arena)
    (responses : Fin count → Value R Empty)
    (responseTyped : ∀ i,
      ValueTyped xi emptyTy emptyContext (responses i) s.operation.responseType) :
    ∀ i trace last, Prefix graph (s.resume (responses i)) trace last →
      CompTyped xi emptyTy emptyContext last result ∧ CanProgress graph last :=
  run_all_saved_responses typed initialTyped (history.erase typed)
    (history.graphGuard guard) s member responses responseTyped

/-- Prefix is Prop, so its constructor-by-constructor history extension is
asserted as Nonempty; no elimination of a raw proof into history data. -/
theorem History.internal_prefix
    (history : History B initialGraph initialTypes initial R graph xi current arena)
    (steps : Prefix graph current trace last) :
    Nonempty (History B initialGraph initialTypes initial R graph xi last arena) := by
  revert history
  induction steps with
  | refl => intro history; exact ⟨history⟩
  | cons step _ ih => intro history; exact ih (.internal history step)

namespace Recovered
open YulangClosure.HandlerGraph.Extension.Demo
open YulangClosure.HandlerGraph.Combined.ConcreteSourceRun
open YulangClosure.HandlerGraph.Combined.RecursiveTrace

/-- The recovered recursive callback is allocated from its WHOLE source RHS,
then supplied to the old operation-73 continuation. -/
def firstAnswer :
    History (Fin 1) old oldTypes saved.suspended FirstRef recursiveGraph recursiveTypes
      ((saved.map Sum.inl).resume recursiveResponse) [saved.map Sum.inl] := by
  apply History.answer (History.allocation recursiveRhs captures (.publish saved .start)
    (fun _ => recursiveCallback_typed) captures_typed recursiveFresh_noCycle)
  · exact List.mem_cons.mpr (.inl rfl)
  · exact .matched (s := saved.map Sum.inl) operation rfl recursiveResponse
  · exact recursiveResponse_typed

/-- Reuse the established six-step RAW trace, publish operation 75, allocate
the second actual source family, and resume the older operation-73 entry.
Only the initial graph guard is later needed by the safety consumer. -/
theorem original_entry_reused_history :
    Nonempty (History (Fin 1) old oldTypes saved.suspended SecondRef
      RecursiveTrace.secondGraph RecursiveTrace.secondTypes
      (((saved.map Sum.inl).map Sum.inl).resume transportedResponse)
      RecursiveTrace.secondArena) := by
  obtain ⟨reached⟩ := firstAnswer.internal_prefix recursive_callback_reaches_own_request
  let published := History.publish recursiveSaved reached
  let allocated := History.allocation secondRhs secondCaptures published
    secondRhs_typed secondCaptures_typed secondFresh_noCycle
  refine ⟨History.answer allocated ?_ ?_ transportedResponse_typed⟩
  · exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl)))
  · exact .matched (s := (saved.map Sum.inl).map Sum.inl)
      operation rfl transportedResponse

/-- Parent application: the recovered interaction no longer supplies either
intermediate or final graph typing/guard as an external safety premise. -/
theorem reused_entry_every_prefix_safe
    (steps : Prefix RecursiveTrace.secondGraph
      (((saved.map Sum.inl).map Sum.inl).resume transportedResponse) trace last) :
    CompTyped RecursiveTrace.secondTypes emptyTy emptyContext last unitTy ∧
      CanProgress RecursiveTrace.secondGraph last ∧
      (∀ s, s ∈ RecursiveTrace.secondArena →
        SavedTyped RecursiveTrace.secondTypes s unitTy) := by
  obtain ⟨history⟩ := original_entry_reused_history
  exact history.prefix_safety old_typed saved_actual_request oldGraphGuard steps

theorem reused_entry_every_prefix_four
    (steps : Prefix RecursiveTrace.secondGraph
      (((saved.map Sum.inl).map Sum.inl).resume transportedResponse) trace last) :
    (∃ v, last = .ret v) ∨ (∃ op p k, last = .request op p k) ∨
      (∃ reason, last = .fail reason) ∨
      ∃ event next, Step RecursiveTrace.secondGraph last event next := by
  obtain ⟨history⟩ := original_entry_reused_history
  exact history.prefix_four old_typed saved_actual_request oldGraphGuard steps

end Recovered
end YulangClosure.HandlerGraph.Combined.SourceGenerated
