import Yulang.GeneralDeclarativeExactSupport337

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeExactNested337
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeEndpointRecord336 (Read)
open GeneralDeclarativeEndpointProgram336 (ready from_supported list_sound template)
open GeneralDeclarativeEndpointOverlay336 (Entry receipts footprintKeep span_order spans)
open GeneralDeclarativeEndpointBatch336 (prepare)
open GeneralDeclarativeEndpointSupport336 (Certified)
open GeneralDeclarativeEndpointConserve336 (names)
open GeneralDeclarativeExactOverlay337 (ModelsExact approved)
open GeneralDeclarativeExactSupport337 (rows endpointRows authorize model_exact receipts_same nested_read)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralDeclarativeRecordSpine330 (Terminal)
open GeneralDeclarativeOrderedRecord326 (order)
open CommonRoleCanonicalRows (normalize)
open GeneralNominalCommonBridge (Assignment)

/-- Materialize certified endpoint rows for a second real program,
keeping every byte of the older assignment on the exact old receipt
footprint. Both read lists remain true in one common model. -/
theorem extend {s : State} {p : Supported s done}
    (r : Read (authorize p old) arg (shape.map Prod.fst) ls us first last le ue)
    (computed : ready arg shape tail ls us first last le ue = some jobs)
    (m : Assignment) (oldFit : ModelsExact s old m) (keep : List Nat) :
    ∃ n,
      ModelsExact (prepare (appendFacts s (rows old)) (footprintKeep (names old ++ keep) jobs) jobs.length)
        (old ++ receipts (appendFacts s (rows old)) (footprintKeep (names old ++ keep) jobs) jobs) n ∧
      ∀ x ∈ stateNames (appendFacts s (rows old)) ++ footprintKeep (names old ++ keep) jobs, n x = m x := by
  have current := (model_exact s old m).mpr oldFit
  obtain ⟨n,newFit,kept⟩ := approved r computed m current.1 (names old ++ keep)
  have oldNames : ∀ x ∈ names old, n x = m x := by
    intro x used
    exact kept x (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_left _ used)))
  have oldReads := (receipts_same oldNames).mpr oldFit.2
  exact ⟨n,⟨newFit.1,fun e part => (List.mem_append.mp part).elim (oldReads e) (newFit.2 e)⟩,kept⟩

/-- Once the nested projected value's literal endpoint rows have been
certified, run the same real ordered record compiler again. The new
binder names are precisely the variables of the nested pattern; old
and new receipts hold together, without actual center RHS syntax. -/
theorem compile_nested {s : State} {p : Supported s done}
    (listed : e ∈ old) (backed : Certified p e) (bounded : Bounds s e.2)
    (left : (⟨e.2.lower,withTail ls le⟩ : Equation) ∈ endpointRows e)
    (right : (⟨e.2.upper,withTail us ue⟩ : Equation) ∈ endpointRows e)
    (leftEnd : Terminal le) (rightEnd : Terminal ue)
    (different : (shape.map Prod.fst).Nodup)
    (lowOrder : order (normalize ls) (shape.map Prod.fst) = some first)
    (highOrder : order (normalize us) (shape.map Prod.fst) = some last)
    (m : Assignment) (oldFit : ModelsExact s old m) (keep : List Nat) (tail : Nat) :
    ∃ jobs n,
      ready e.2 shape tail ls us first last le ue = some jobs ∧
      (spans (appendFacts s (rows old)) (footprintKeep (names old ++ keep) jobs) jobs).map Prod.fst
        = (template shape tail).variables ∧
      ModelsExact (prepare (appendFacts s (rows old)) (footprintKeep (names old ++ keep) jobs) jobs.length)
        (old ++ receipts (appendFacts s (rows old)) (footprintKeep (names old ++ keep) jobs) jobs) n ∧
      ∀ x ∈ names old, n x = m x := by
  have read := nested_read listed backed bounded left right leftEnd rightEnd different lowOrder highOrder
  obtain ⟨jobs,computed⟩ := from_supported read tail
  obtain ⟨n,fit,kept⟩ := extend read computed m oldFit keep
  refine ⟨jobs,n,computed,?_,fit,?_⟩
  · rw [span_order]; exact (list_sound read computed).1
  · intro x member
    exact kept x (List.mem_append_right _ (List.mem_append_right _
      (List.mem_append_left _ member)))

end Yulang.GeneralDeclarativeExactNested337
