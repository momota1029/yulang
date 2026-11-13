import Yulang.GeneralDictionaryProvenanceScalarBranch

/-! Arbitrarily many scalar point arguments. Slots may repeat; no capture or
interval generality is claimed. This derives branch checks from syntax. -/
namespace Yulang.GeneralDictionaryMultiScalarInspection
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query Bounds)
variable {state : GeneralNominalState.State}

def points (entries : List (Fin state.base.slots × Inference.Base)) : List (Bounds state) :=
  entries.map (fun entry => (entry.1,entry.1))
def queries (entries : List (Fin state.base.slots × Inference.Base)) : List Query :=
  entries.map (fun entry => .scalar entry.2)
def scalarReport (entries : List (Fin state.base.slots × Inference.Base)) : Report state :=
  { inspected := points entries, checked := points entries }
def Observed (state : GeneralNominalState.State)
    (entries : List (Fin state.base.slots × Inference.Base)) : Prop :=
  ∀ entry ∈ entries, state.nominals entry.1 = none ∧ state.view.heads entry.1 = .scalar entry.2

theorem inspect_exact (state : GeneralNominalState.State)
    (entries : List (Fin state.base.slots × Inference.Base)) (observed : Observed state entries)
    (index : Nat) :
    inspectMany state (queries entries) (points entries) (fun _ => none) index = scalarReport entries := by
  induction entries generalizing index with
  | nil => simp [queries,points,inspectMany,scalarReport]
  | cons entry rest ih =>
    obtain ⟨noNominal,head⟩ := observed entry List.mem_cons_self
    have tail : Observed state rest := fun other member => observed other (List.mem_cons_of_mem _ member)
    simp only [queries,points,List.map_cons,inspectMany]
    change (inspect state (.scalar entry.2) (entry.1,entry.1) none).append
      (inspectMany state (queries rest) (points rest) (fun _ => none) (index+1)) = _
    rw [ih tail (index+1)]
    simp [inspect,noNominal,head,Report.visit,scalarReport,points,Report.append]

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalRecursiveCandidates

structure Shape (context : Context) (root : Occurrence roles) (declaration : Declaration) where
  role : declaration.role = root.demand.role
  entries : List (Fin context.state.base.slots × Inference.Base)
  observed : Observed context.state entries
  inputs : declaration.inputNames = []
  query : GeneralNominalInspection.queries context.state context.interpretation declaration = queries entries
  located : arguments context root = some (points entries)
  defined : GeneralNominalMaterialization.RootDefined declaration root

theorem report_exact (context : Context) (root : Occurrence roles) (declaration : Declaration)
    (shape : Shape context root declaration) :
    report context declaration (points shape.entries) =
      { inspected := points shape.entries, checked := points shape.entries ++ points shape.entries } := by
  unfold report
  rw [shape.query,inspect_exact context.state shape.entries shape.observed]
  rfl

theorem point_checks (state : GeneralNominalState.State)
    (entries : List (Fin state.base.slots × Inference.Base))
    (model : GeneralNominalCommonBridge.Assignment) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (selfChecks state { checked := points entries ++ points entries }) := by
  intro atom member
  simp only [selfChecks,List.mem_map] at member
  obtain ⟨bounds,present,rfl⟩ := member
  have present : bounds ∈ points entries := by simpa only [List.mem_append,or_self] using present
  obtain ⟨entry,_,rfl⟩ := List.mem_map.mp present
  exact CommonNominalFullCarrier.subtype_refl _

theorem private_models (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (shape : Shape context root declaration)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models context.state model) :
    GeneralNominalState.Models (privateState registry context root declaration (points shape.entries)) model ∧
    ProjectionModels context.state (report context declaration (points shape.entries)) model := by
  constructor
  · unfold privateState
    rw [report_exact context root declaration shape]
    apply (GeneralNominalState.extend_models ..).mpr
    refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨valid,?_,?_⟩,?_⟩
    · simp [bindings,GeneralNominalAllocation.Compatible]
    · simp [bindings,GeneralNominalAllocation.merges,shape.inputs]
    · exact point_checks context.state shape.entries model
  · rw [report_exact context root declaration shape]
    simp [ProjectionModels]

end Yulang.GeneralDictionaryMultiScalarInspection
