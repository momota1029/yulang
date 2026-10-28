import YulangClosure.PaperFreshHeapAllocation
import YulangClosure.PaperTypeBetaExecution

/-! R59: finite graph reads and type beta at the root or a type-application
function position. No constructor interiors, guard, termination, full heap
judgment, source realization or whole-language preservation are asserted. -/
namespace YulangClosure.PaperTypes.PaperHeapObservation

open FreshHeap

/-- These are exactly the represented outer observation operations. -/
inductive ObservationStep (heap : Heap) : Value → Value → Prop where
  | graphRead {identity payload} : lookupHeap heap identity = some payload →
      ObservationStep heap (.graphReference identity) payload
  | typeBeta {source target} : PaperTypeBetaExecution.typeBetaValue source = some target →
      ObservationStep heap source target
  | typeApplication {source target argument} : ObservationStep heap source target →
      ObservationStep heap (.typeApplication source argument) (.typeApplication target argument)

/-- An actual finite trace, including the zero-step trace. -/
inductive ObservationTrace (heap : Heap) : Value → Value → Prop where
  | refl (value) : ObservationTrace heap value value
  | cons {source middle target} : ObservationStep heap source middle →
      ObservationTrace heap middle target → ObservationTrace heap source target

private theorem lookupHeap_member {heap : Heap} {identity payload}
    (h : lookupHeap heap identity = some payload) : (identity, payload) ∈ heap := by
  induction heap with
  | nil => cases h
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    by_cases he : key = identity
    · subst key
      have hv : value = payload := Option.some.inj (by simpa [lookupHeap] using h)
      subst payload
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih (by simpa [lookupHeap, he] using h))

/-- The successful graph lookup fixes the payload type even with shadowed IDs. -/
theorem heapLookup_payloadTyped {d g e heap identity payload a}
    (hh : HeapPayloadTyped d g e heap)
    (hg : lookupGraphEnvironment g identity = some a)
    (hl : lookupHeap heap identity = some payload) :
    PaperValueTyped d g e payload a := by
  obtain ⟨b, hb, hv⟩ := hh identity payload (lookupHeap_member hl)
  have he : b = a := Option.some.inj (hb.symm.trans hg)
  exact he ▸ hv

theorem observationStep_preservation {d g e heap source target a}
    (hh : HeapPayloadTyped d g e heap)
    (hs : ObservationStep heap source target)
    (hv : PaperValueTyped d g e source a) : PaperValueTyped d g e target a := by
  induction hs generalizing a with
  | graphRead hl =>
    cases hv with
    | graphReference hg => exact heapLookup_payloadTyped hh hg hl
  | typeBeta hb => exact PaperTypeBetaExecution.typeBetaValue_preservation hv hb
  | typeApplication hs ih =>
    cases hv with
    | typeApplication hf => exact .typeApplication (ih hf)

theorem observationTrace_preservation {d g e heap source target a}
    (hh : HeapPayloadTyped d g e heap)
    (hs : ObservationTrace heap source target)
    (hv : PaperValueTyped d g e source a) : PaperValueTyped d g e target a := by
  induction hs with
  | refl => exact hv
  | cons first rest ih => exact ih (observationStep_preservation hh first hv)

/-- Operand observation and Force/Delay remain distinct transitions. -/
theorem force_observation_preservation {d g e heap source body a}
    (hh : HeapPayloadTyped d g e heap)
    (hc : PaperComputationTyped d g e (.force source) a)
    (hs : ObservationTrace heap source (.delay body)) :
    PaperComputationTyped d g e (.force (.delay body)) a ∧
    PaperCoreStep.step (.force (.delay body)) = some body ∧
    PaperComputationTyped d g e body a := by
  cases hc with
  | force hv =>
    have middle := PaperComputationTyped.force (observationTrace_preservation hh hs hv)
    exact ⟨middle, rfl, PaperCoreStep.preservation middle rfl⟩

/-- Consume R29 on its same allocated heap and extended graph, without a new witness. -/
theorem allocated_force_observation {d old gamma target rho b heap source body a}
    (unique : (ids b).Nodup)
    (freshGraph : ∀ r, r ∈ ids b → r ∉ old.map Prod.fst)
    (freshHeap : ∀ r, r ∈ ids b → r ∉ heap.map Prod.fst)
    (hr : TermSubstitutionTyped d old gamma target rho)
    (hb : BlockTyped d old gamma b)
    (hh : HeapPayloadTyped d old target heap)
    (hc : PaperComputationTyped d (formals b ++ old) target (.force source) a)
    (hs : ObservationTrace (allocate b rho heap) source (.delay body)) :
    GraphLookupPreserved old (formals b ++ old) ∧
    HeapPayloadTyped d (formals b ++ old) target (allocate b rho heap) ∧
    PaperComputationTyped d (formals b ++ old) target (.force (.delay body)) a ∧
    PaperCoreStep.step (.force (.delay body)) = some body ∧
    PaperComputationTyped d (formals b ++ old) target body a := by
  obtain ⟨hg, _, _, _, _, _, _, hp⟩ :=
    finite_allocation unique freshGraph freshHeap hr hb hh
  exact ⟨hg, hp, force_observation_preservation hp hc hs⟩

/-- Payload typing admits a literal observation self-loop, so it is no guard. -/
theorem selfAlias_observation_loop (d : DeclarationTable) (e : TypeEnvironment)
    (identity : Nat) (a : Ty) :
    HeapPayloadTyped d [(identity, a)] e [(identity, .graphReference identity)] ∧
    PaperValueTyped d [(identity, a)] e (.graphReference identity) a ∧
    ObservationStep [(identity, .graphReference identity)]
      (.graphReference identity) (.graphReference identity) ∧
    ObservationTrace [(identity, .graphReference identity)]
      (.graphReference identity) (.graphReference identity) := by
  have hp := self_alias_payload d e identity a
  have step : ObservationStep [(identity, .graphReference identity)]
      (.graphReference identity) (.graphReference identity) := .graphRead hp.2
  exact ⟨hp.1, .graphReference (by simp [lookupGraphEnvironment]), step,
    .cons step (.refl _)⟩

/-- A later duplicate graph declaration cannot change the first successful type. -/
theorem duplicate_graph_firstMatch :
    lookupGraphEnvironment [(7, .base .int), (7, .base .bool)] 7 = some (.base .int) ∧
    lookupGraphEnvironment [(7, .base .int), (7, .base .bool)] 7 ≠ some (.base .bool) := by
  simp [lookupGraphEnvironment]

/-- A colliding front node determines the graph read; the suffix cannot be selected. -/
theorem heap_collision_firstMatch :
    lookupHeap [(7, .graphReference 8), (7, .graphReference 9)] 7 = some (.graphReference 8) ∧
    lookupHeap [(7, .graphReference 8), (7, .graphReference 9)] 7 ≠ some (.graphReference 9) := by
  simp [lookupHeap]

/-- Two successful first-match lookups at one identity cannot disagree on its type. -/
theorem mismatched_graph_type_excluded {g identity a b}
    (ha : lookupGraphEnvironment g identity = some a)
    (hb : lookupGraphEnvironment g identity = some b) : a = b :=
  Option.some.inj (ha.symm.trans hb)

/-- Graph references are not type-beta redexes, even when used as functions. -/
theorem nonRedex_typeBeta_excluded (identity : Nat) (argument : Ty) :
    PaperTypeBetaExecution.typeBetaValue (.graphReference identity) = none ∧
    PaperTypeBetaExecution.typeBetaValue (.typeApplication (.graphReference identity) argument) = none := by
  exact ⟨rfl, rfl⟩

end YulangClosure.PaperTypes.PaperHeapObservation
