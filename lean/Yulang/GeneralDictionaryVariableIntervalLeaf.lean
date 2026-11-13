import Yulang.GeneralDictionaryLinearLeaf

/-! A bare-variable terminal declaration accepts a located nonpoint interval
when its endpoints are ordered in the specified source model. No selection or
execution assumption is used. -/
namespace Yulang.GeneralDictionaryVariableIntervalLeaf
open GeneralDeclarations GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionaryRecursiveEvidence CommonNominalFullCarrier

def variableReport (context : Context) (name : Nat)
    (pair : GeneralNominalInspection.Bounds context.state) : Report context.state :=
  { captures := [⟨name,pair,none⟩], checked := [pair,pair] }

theorem report_exact (context : Context) (declaration : Declaration) (name : Nat)
    (pair : GeneralNominalInspection.Bounds context.state)
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration = [.variables [name]]) :
    report context declaration [pair] = variableReport context name pair := by
  unfold report
  rw [query]
  simp [inspectMany,inspect,Report.append,variableReport]

theorem branch_models (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration) (name : Nat)
    (pair : GeneralNominalInspection.Bounds context.state)
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration = [.variables [name]])
    (inputs : declaration.inputNames = [name]) (terminal : declaration.requirements = [])
    (outputs : root.demand.outputs = []) (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models context.state model)
    (ordered : Subtype (model (context.state.base.source pair.1)).1 (model (context.state.base.source pair.2)).1) :
    BranchModels registry context root declaration checked [pair] model := by
  refine ⟨?_,?_,?_⟩
  · unfold privateState
    rw [report_exact context declaration name pair query]
    apply (GeneralNominalState.extend_models ..).mpr
    constructor
    · have propagated := GeneralNominalLinearCaptureFacts.propagated_models context.state registry root.identity declaration
        (fun _ : Fin 1 => name) (by intro a b _; exact Subsingleton.elim a b)
        (by simpa only [List.ofFn_succ,List.ofFn_zero] using inputs)
        (fun _ => pair) model valid (fun _ => ordered)
      simpa only [variableReport,bindings,List.map_cons,List.map_nil,List.ofFn_succ,List.ofFn_zero] using propagated
    · intro atom member
      simp only [variableReport,selfChecks,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl <;> exact ordered
  · rw [report_exact context declaration name pair query]
    simp [ProjectionModels,variableReport]
  · rw [GeneralDictionaryLinearLeaf.generated_empty context registry root declaration checked terminal outputs]
    exact GeneralNominalMaterialization.empty_models ..

theorem instance_of_interval (context : Context) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration) (name : Nat)
    (pair : GeneralNominalInspection.Bounds context.state)
    (query : GeneralNominalInspection.queries context.state context.interpretation declaration = [.variables [name]])
    (inputs : declaration.inputNames = [name]) (terminal : declaration.requirements = [])
    (outputs : root.demand.outputs = []) (role : declaration.role = root.demand.role)
    (located : arguments context root = some [pair]) (metadata : Metadata registry context)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models context.state model)
    (ordered : Subtype (model (context.state.base.source pair.1)).1 (model (context.state.base.source pair.2)).1) :
    Instance registry context model root declaration.id [] := by
  refine ⟨declaration,visible,checked,rfl,role,[pair],located,?_,?_,?_,metadata,?_⟩
  · rw [report_exact context declaration name pair query]
    exact ⟨rfl,rfl,rfl⟩
  · constructor
    · intro output member; rw [outputs] at member; cases member
    · rw [GeneralDictionaryLinearLeaf.generated_empty context registry root declaration checked terminal outputs]
  · exact (GeneralDictionaryLinearLeaf.children_empty context registry root declaration checked terminal _).symm
  · exact branch_models context registry root declaration checked name pair query inputs terminal outputs model valid ordered
end Yulang.GeneralDictionaryVariableIntervalLeaf
