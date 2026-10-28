import YulangClosure.PaperHeapObservation
import YulangClosure.PaperExtendedExecution

/-!
R62: couple an explicit allocated heap to finite operand observation and the
existing connected Force/Delay transition. State has no heap; observation is
not asserted to be an executor step. All contexts, body, stack and final type
are shared literally. Guardedness, source realization and progress remain open.
-/
namespace YulangClosure.PaperTypes.PaperHeapExecution

open FreshHeap PaperCoreControl

/-- The actual Force/Delay reduction, lifted through the unchanged let stack. -/
theorem force_delay_erased_step (d : DeclarationTable) (binder : TermName)
    (body : Computation) (stack : List Computation) :
    PaperExtendedExecution.ComputationStep d binder
      (erase ⟨.force (.delay body), stack⟩) (erase ⟨body, stack⟩) := by
  apply PaperExtendedExecution.plug_step
  exact .existing (.existing (.existing
    (PaperTupleSplitExecution.old_context_step (.principal rfl))))

/-- A supplied successful connected transition is used by R61 preservation.
The heap is an explicit coupling parameter, never a field of the executor. -/
theorem observed_force_control {d g e heap source body stack result binder}
    (hd : PaperTemplateExecution.BodiesTyped d)
    (hh : HeapPayloadTyped d g e heap)
    (ht : StateTyped d g e ⟨.force source, stack⟩ result)
    (path : PaperHeapObservation.ObservationTrace heap source (.delay body))
    (hs : PaperExtendedExecution.controlStep d binder
      ⟨.force (.delay body), stack⟩ = some ⟨body, stack⟩) :
    StateTyped d g e ⟨.force (.delay body), stack⟩ result ∧
    StateTyped d g e ⟨body, stack⟩ result ∧
    PaperComputationTyped d g e (erase ⟨body, stack⟩) result ∧
    PaperExtendedExecution.ControlStepEvidence d binder
      ⟨.force (.delay body), stack⟩ ⟨body, stack⟩ ∧
    PaperExtendedExecution.ComputationStep d binder
      (erase ⟨.force (.delay body), stack⟩) (erase ⟨body, stack⟩) := by
  obtain ⟨a, hc, hf⟩ := ht
  have observed := PaperHeapObservation.force_observation_preservation hh hc path
  have middle : StateTyped d g e ⟨.force (.delay body), stack⟩ result :=
    ⟨a, observed.1, hf⟩
  have last := PaperExtendedExecution.preservation hd middle hs
  exact ⟨middle, last, erase_typed last,
    PaperExtendedExecution.controlStep_evidence hs,
    force_delay_erased_step d binder body stack⟩

/-- R29 allocation, R59 finite observation and R61 successful control compose
on the same exact heap/graph/state witnesses. No allocated heap is existential. -/
theorem allocated_force_control
    {d old gamma target rho b heap source body stack result binder}
    (unique : (ids b).Nodup)
    (freshGraph : ∀ r, r ∈ ids b → r ∉ old.map Prod.fst)
    (freshHeap : ∀ r, r ∈ ids b → r ∉ heap.map Prod.fst)
    (hr : TermSubstitutionTyped d old gamma target rho)
    (hb : BlockTyped d old gamma b)
    (hh : HeapPayloadTyped d old target heap)
    (hd : PaperTemplateExecution.BodiesTyped d)
    (ht : StateTyped d (formals b ++ old) target ⟨.force source, stack⟩ result)
    (path : PaperHeapObservation.ObservationTrace
      (allocate b rho heap) source (.delay body)) :
    GraphLookupPreserved old (formals b ++ old) ∧
    HeapPayloadTyped d (formals b ++ old) target (allocate b rho heap) ∧
    PaperExtendedExecution.controlStep d binder
      ⟨.force (.delay body), stack⟩ = some ⟨body, stack⟩ ∧
    StateTyped d (formals b ++ old) target ⟨.force (.delay body), stack⟩ result ∧
    StateTyped d (formals b ++ old) target ⟨body, stack⟩ result ∧
    PaperComputationTyped d (formals b ++ old) target (erase ⟨body, stack⟩) result ∧
    PaperExtendedExecution.ControlStepEvidence d binder
      ⟨.force (.delay body), stack⟩ ⟨body, stack⟩ ∧
    PaperExtendedExecution.ComputationStep d binder
      (erase ⟨.force (.delay body), stack⟩) (erase ⟨body, stack⟩) := by
  obtain ⟨hg, _, _, _, _, _, _, hp⟩ :=
    finite_allocation unique freshGraph freshHeap hr hb hh
  have hs := PaperExtendedExecution.controlStep_force_delay d binder body stack
  exact ⟨hg, hp, hs, observed_force_control hd hp ht path hs⟩

end YulangClosure.PaperTypes.PaperHeapExecution
