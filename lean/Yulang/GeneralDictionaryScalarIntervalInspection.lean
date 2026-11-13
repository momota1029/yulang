import Yulang.GeneralDictionaryReachableRootIntervals
import Yulang.GeneralDictionaryProvenanceScalarBranch

/-! Scalar inspection at arbitrary lower/upper pairs, without captures. The
private-state check exposes only the original endpoint inequalities. The next
module derives these inequalities from initial root formation and actual traces. -/
namespace Yulang.GeneralDictionaryScalarIntervalInspection
open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query Bounds)
variable {state : GeneralNominalState.State}

def intervals (entries : List (Bounds state × Inference.Base)) : List (Bounds state) :=
  entries.map (fun entry => entry.1)
def queries (entries : List (Bounds state × Inference.Base)) : List Query :=
  entries.map (fun entry => .scalar entry.2)
def scalarReport (entries : List (Bounds state × Inference.Base)) : Report state :=
  { inspected := intervals entries, checked := intervals entries }
def Observed (state : GeneralNominalState.State)
    (entries : List (Bounds state × Inference.Base)) : Prop :=
  ∀ entry ∈ entries, state.nominals entry.1.1 = none ∧ state.view.heads entry.1.1 = .scalar entry.2

theorem inspect_exact (state : GeneralNominalState.State)
    (entries : List (Bounds state × Inference.Base)) (observed : Observed state entries)
    (index : Nat) :
    inspectMany state (queries entries) (intervals entries) (fun _ => none) index = scalarReport entries := by
  induction entries generalizing index with
  | nil => simp [queries,intervals,inspectMany,scalarReport]
  | cons entry rest ih =>
    obtain ⟨noNominal,head⟩ := observed entry List.mem_cons_self
    have tail : Observed state rest := fun other member => observed other (List.mem_cons_of_mem _ member)
    simp only [queries,intervals,List.map_cons,inspectMany]
    change (inspect state (.scalar entry.2) entry.1 none).append
      (inspectMany state (queries rest) (intervals rest) (fun _ => none) (index+1)) = _
    rw [ih tail (index+1)]
    simp [inspect,noNominal,head,Report.visit,scalarReport,intervals,Report.append]

open GeneralDeclarations GeneralSourceDictionaries GeneralNominalRecursiveCandidates

structure Shape (context : Context) (root : Occurrence roles) (declaration : Declaration) where
  role : declaration.role = root.demand.role
  entries : List (Bounds context.state × Inference.Base)
  observed : Observed context.state entries
  inputs : declaration.inputNames = []
  query : GeneralNominalInspection.queries context.state context.interpretation declaration = queries entries
  located : arguments context root = some (intervals entries)
  defined : GeneralNominalMaterialization.RootDefined declaration root

theorem report_exact (context : Context) (root : Occurrence roles) (declaration : Declaration)
    (shape : Shape context root declaration) :
    report context declaration (intervals shape.entries) =
      { inspected := intervals shape.entries, checked := intervals shape.entries ++ intervals shape.entries } := by
  unfold report
  rw [shape.query,inspect_exact context.state shape.entries shape.observed]
  rfl

theorem interval_checks (state : GeneralNominalState.State)
    (entries : List (Bounds state × Inference.Base))
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : ∀ pair ∈ intervals entries, CommonNominalFullCarrier.Subtype
      (model (state.base.source pair.1)).1 (model (state.base.source pair.2)).1) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (selfChecks state { checked := intervals entries ++ intervals entries }) := by
  intro atom member
  simp only [selfChecks,List.mem_map] at member
  obtain ⟨bounds,present,rfl⟩ := member
  have present : bounds ∈ intervals entries := by simpa only [List.mem_append,or_self] using present
  exact valid bounds present

theorem private_models (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (shape : Shape context root declaration)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models context.state model)
    (ordered : ∀ pair ∈ intervals shape.entries, CommonNominalFullCarrier.Subtype
      (model (context.state.base.source pair.1)).1 (model (context.state.base.source pair.2)).1) :
    GeneralNominalState.Models (privateState registry context root declaration (intervals shape.entries)) model ∧
    ProjectionModels context.state (report context declaration (intervals shape.entries)) model := by
  constructor
  · unfold privateState
    rw [report_exact context root declaration shape]
    apply (GeneralNominalState.extend_models ..).mpr
    refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨valid,?_,?_⟩,?_⟩
    · simp [bindings,GeneralNominalAllocation.Compatible]
    · simp [bindings,GeneralNominalAllocation.merges,shape.inputs]
    · exact interval_checks context.state shape.entries model ordered
  · rw [report_exact context root declaration shape]
    simp [ProjectionModels]

end Yulang.GeneralDictionaryScalarIntervalInspection
