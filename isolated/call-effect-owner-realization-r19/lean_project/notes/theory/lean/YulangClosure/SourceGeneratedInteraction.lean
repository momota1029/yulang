import YulangClosure.HandlerGraphRecursiveTrace

/-! Finite source-generated interaction histories in the existing research
machine. Allocation is the actual sourceFresh/allocate construction, with
source RHS/capture typing and its local finite transparent-cycle criterion.
No final graph typing or guard is supplied by a history constructor.

This domain refines Extension.Run; it does not replace the broader Run or claim
that arbitrary typed immutable extensions are guarded. Full paper syntax and
native source-to-machine correspondence remain separate obligations. -/
namespace YulangClosure.HandlerGraph.SourceGenerated
open HigherOrder (Ty Context emptyContext OperationInstance)
open YulangClosure.HandlerGraph.Extension
open YulangClosure.HandlerGraph.Recursive
open YulangClosure.HandlerGraph.Combined

/-- Arbitrary finite histories; reference sorts need not be finite. Only each
new recursive family is finite, and n may be zero. Publication and answers use
the existing raw rules, including full operation-instance equality. -/
inductive History (B : Type) (initialGraph : Graph B) (initialTypes : B → Ty)
    (initial : Comp B Empty) :
    (R : Type) → Graph R → (R → Ty) → Comp R Empty → List (Saved R) → Prop where
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
      CapturesTyped xi env capture →
      FreshNoCycle (sourceFresh capture rhs) →
      History B initialGraph initialTypes initial
        (Sum R (Fin n)) (allocate graph (sourceFresh capture rhs)) (joinTy xi nu)
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
    {current : Comp R Empty} {arena : List (Saved R)} {result : Ty}

/-- Erasure preserves the exact graph, current term and entire arena. Its
extension typing premise is proved from source typing, not assumed. -/
theorem erase_and_graph
    (initialGraphTyped : WellTyped initialGraph initialTypes)
    (history : History B initialGraph initialTypes initial R graph xi current arena) :
    Run B initialGraph initialTypes initial R graph xi current arena ∧ WellTyped graph xi := by
  induction history with
  | start => exact ⟨.start, initialGraphTyped⟩
  | internal prior step ih => exact ⟨.internal ih.1 step, ih.2⟩
  | publish saved prior ih => exact ⟨.publish saved ih.1, ih.2⟩
  | allocation rhs capture prior hrhs hcapture hcycle ih =>
      exact ⟨run_source_extension ih.1 ih.2 rhs hrhs capture hcapture,
        sourceExtension_typed ih.2 rhs hrhs capture hcapture⟩
  | answer prior member matched typed ih =>
      exact ⟨.answer ih.1 member matched typed, ih.2⟩

theorem erase
    (initialGraphTyped : WellTyped initialGraph initialTypes)
    (history : History B initialGraph initialTypes initial R graph xi current arena) :
    Run B initialGraph initialTypes initial R graph xi current arena :=
  (erase_and_graph initialGraphTyped history).1

/-- Prop-valued histories eliminate only into Prop. Each witness is nevertheless
the actual constructive allocationGuard, never a caller-supplied final guard.
The initial graph is the sole global guard premise. -/
theorem guarded
    (initialGuard : GuardedValueGraph.Guarded (projectGraph initialGraph))
    (history : History B initialGraph initialTypes initial R graph xi current arena) :
    Nonempty (GuardedValueGraph.Guarded (projectGraph graph)) := by
  induction history with
  | start => exact ⟨initialGuard⟩
  | internal prior step ih => exact ih
  | publish saved prior ih => exact ih
  | allocation rhs capture prior hrhs hcapture hcycle ih =>
      obtain ⟨guard⟩ := ih
      exact ⟨sourceExtension_guarded guard rhs capture hcycle⟩
  | answer prior member matched typed ih => exact ih

/-- Apply exact erasure to the original interaction invariant: every stored
record is covered, including older entries after any number of allocations. -/
theorem invariant
    (initialGraphTyped : WellTyped initialGraph initialTypes)
    (initialTyped : CompTyped initialTypes emptyTy emptyContext initial result)
    (history : History B initialGraph initialTypes initial R graph xi current arena) :
    WellTyped graph xi ∧ CompTyped xi emptyTy emptyContext current result ∧
      ∀ saved, saved ∈ arena → SavedTyped xi saved result :=
  run_invariant initialGraphTyped initialTyped (erase initialGraphTyped history)

/-- Every finite internal prefix after every finite source history is safe,
with a guard derived from the initial graph and local source allocation checks. -/
theorem prefix_safety
    (initialGraphTyped : WellTyped initialGraph initialTypes)
    (initialTyped : CompTyped initialTypes emptyTy emptyContext initial result)
    (initialGuard : GuardedValueGraph.Guarded (projectGraph initialGraph))
    (history : History B initialGraph initialTypes initial R graph xi current arena)
    (steps : Prefix graph current trace last) :
    CompTyped xi emptyTy emptyContext last result ∧ CanProgress graph last ∧
      (∀ saved, saved ∈ arena → SavedTyped xi saved result) := by
  obtain ⟨guard⟩ := guarded initialGuard history
  exact run_prefix_safety initialGraphTyped initialTyped
    (erase initialGraphTyped history) guard steps

theorem prefix_four
    (initialGraphTyped : WellTyped initialGraph initialTypes)
    (initialTyped : CompTyped initialTypes emptyTy emptyContext initial result)
    (initialGuard : GuardedValueGraph.Guarded (projectGraph initialGraph))
    (history : History B initialGraph initialTypes initial R graph xi current arena)
    (steps : Prefix graph current trace last) :
    (∃ v, last = .ret v) ∨ (∃ op p k, last = .request op p k) ∨
      (∃ reason, last = .fail reason) ∨ ∃ event next, Step graph last event next := by
  obtain ⟨guard⟩ := guarded initialGuard history
  exact run_prefix_four initialGraphTyped initialTyped
    (erase initialGraphTyped history) guard steps

/-- Actual raw prefixes can be appended without any new typing assumptions. -/
theorem internal_prefix
    (history : History B initialGraph initialTypes initial R graph xi current arena)
    (steps : Prefix graph current trace last) :
    History B initialGraph initialTypes initial R graph xi last arena := by
  revert history
  induction steps with
  | refl => intro history; exact history
  | cons step _ ih => intro history; exact ih (.internal history step)

/-- Both answers are sequentially legal and independently typed. The first
answer leaves the exact arena available for the second. -/
theorem answer_twice
    (history : History B initialGraph initialTypes initial R graph xi current arena)
    (saved : Saved R) (member : saved ∈ arena) (one two : Value R Empty)
    (hOne : ValueTyped xi emptyTy emptyContext one saved.operation.responseType)
    (hTwo : ValueTyped xi emptyTy emptyContext two saved.operation.responseType) :
    History B initialGraph initialTypes initial R graph xi (saved.resume one) arena ∧
    History B initialGraph initialTypes initial R graph xi (saved.resume two) arena := by
  have first := History.answer history member (.matched saved.operation rfl one) hOne
  exact ⟨first, .answer first member (.matched saved.operation rfl two) hTwo⟩

/-- Uniform over every saved member and every independently chosen finite
response family (including zero); responses may use the current fresh nodes. -/
theorem all_saved_responses
    (initialGraphTyped : WellTyped initialGraph initialTypes)
    (initialTyped : CompTyped initialTypes emptyTy emptyContext initial result)
    (initialGuard : GuardedValueGraph.Guarded (projectGraph initialGraph))
    (history : History B initialGraph initialTypes initial R graph xi current arena)
    (saved : Saved R) (member : saved ∈ arena)
    (responses : Fin count → Value R Empty)
    (typed : ∀ i, ValueTyped xi emptyTy emptyContext (responses i) saved.operation.responseType) :
    ∀ i trace last, Prefix graph (saved.resume (responses i)) trace last →
      CompTyped xi emptyTy emptyContext last result ∧ CanProgress graph last := by
  obtain ⟨guard⟩ := guarded initialGuard history
  exact run_all_saved_responses initialGraphTyped initialTyped
    (erase initialGraphTyped history) guard saved member responses typed

/-- Saved provenance is inherited without supplying origin/saved typing. The
chain is the existing immutable embedding chain, retaining exact code/payload. -/
theorem saved_origin_typed
    (initialGraphTyped : WellTyped initialGraph initialTypes)
    (initialTyped : CompTyped initialTypes emptyTy emptyContext initial result)
    (history : History B initialGraph initialTypes initial R graph xi current arena)
    (saved : Saved R) (member : saved ∈ arena) :
    ∃ (V : Type) (originGraph : Graph V) (originTypes : V → Ty)
      (origin : Saved V) (originArena : List (Saved V)),
      Run B initialGraph initialTypes initial V originGraph originTypes
        origin.suspended (origin :: originArena) ∧
      SavedTyped originTypes origin result ∧
      ∃ chain : Chain V originGraph originTypes R graph xi,
        saved = origin.map chain.embedding.refs :=
  run_saved_origin_typed initialGraphTyped initialTyped
    (erase initialGraphTyped history) saved member

namespace RecoveredTrace
open YulangClosure.HandlerGraph.Extension.Demo
open YulangClosure.HandlerGraph.Combined.ConcreteSourceRun
open YulangClosure.HandlerGraph.Combined.RecursiveTrace

/-- Reconstruct the recovered self-recursive trace inside the new domain. Its
actual source RHS, capture typing and local cycle check supply the allocation. -/
theorem first_answer :
    History (Fin 1) old oldTypes saved.suspended
      FirstRef recursiveGraph recursiveTypes
      ((saved.map Sum.inl).resume recursiveResponse) [saved.map Sum.inl] := by
  apply History.answer
  · exact History.allocation recursiveRhs captures (.publish saved .start)
      (fun _ => recursiveCallback_typed) captures_typed recursiveFresh_noCycle
  · exact List.mem_cons.mpr (.inl rfl)
  · exact .matched (s := saved.map Sum.inl) operation rfl recursiveResponse
  · exact recursiveResponse_typed

theorem later_publication :
    History (Fin 1) old oldTypes saved.suspended
      FirstRef recursiveGraph recursiveTypes recursiveSaved.suspended
      [recursiveSaved, saved.map Sum.inl] :=
  .publish recursiveSaved (internal_prefix first_answer recursive_callback_reaches_own_request)

theorem second_allocation :
    History (Fin 1) old oldTypes saved.suspended
      SecondRef secondGraph RecursiveTrace.secondTypes
      ((recursiveSaved.map Sum.inl).suspended) RecursiveTrace.secondArena := by
  exact History.allocation secondRhs secondCaptures later_publication
    secondRhs_typed secondCaptures_typed secondFresh_noCycle

/-- The reused operation-73 record is the second arena member; neither the
operation-75 record nor its own-reference payload is discarded. -/
theorem old_entry_reused :
    History (Fin 1) old oldTypes saved.suspended
      SecondRef secondGraph RecursiveTrace.secondTypes
      (((saved.map Sum.inl).map Sum.inl).resume transportedResponse) RecursiveTrace.secondArena := by
  apply History.answer second_allocation
  · exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl)))
  · exact .matched (s := (saved.map Sum.inl).map Sum.inl)
      operation rfl transportedResponse
  · exact transportedResponse_typed

/-- The generic theorem now supplies all-prefix safety for the recovered
interaction using only the INITIAL graph guard, not secondGraph_guard. -/
theorem every_prefix_safe
    (steps : Prefix secondGraph
      (((saved.map Sum.inl).map Sum.inl).resume transportedResponse) trace last) :
    CompTyped RecursiveTrace.secondTypes emptyTy emptyContext last unitTy ∧
      CanProgress secondGraph last ∧
      (∀ s, s ∈ RecursiveTrace.secondArena → SavedTyped RecursiveTrace.secondTypes s unitTy) :=
  prefix_safety old_typed saved_actual_request oldGraphGuard old_entry_reused steps

theorem every_prefix_four
    (steps : Prefix secondGraph
      (((saved.map Sum.inl).map Sum.inl).resume transportedResponse) trace last) :
    (∃ v, last = .ret v) ∨ (∃ op p k, last = .request op p k) ∨
      (∃ reason, last = .fail reason) ∨ ∃ event next, Step secondGraph last event next :=
  prefix_four old_typed saved_actual_request oldGraphGuard old_entry_reused steps

/-- The existing six-step trace after reuse is a further source history. Its
endpoint equation and binder closure are proved in the pinned trace dependency. -/
theorem repeated_request_history :
    History (Fin 1) old oldTypes saved.suspended
      SecondRef secondGraph RecursiveTrace.secondTypes
      ((recursiveSaved.map Sum.inl).suspended) RecursiveTrace.secondArena :=
  internal_prefix old_entry_reused reused_entry_reaches_own_request

end RecoveredTrace
end YulangClosure.HandlerGraph.SourceGenerated
