import Yulang.GeneralDictionary171AssemblyPersistence
import Yulang.GeneralDictionarySelectedInstanceCoherence

/-! Actual current selection makes bounded assembly independent of the chosen
local structural certificates. A real current model is explicit; general
coverage discovery and global selectedness are not inferred. -/
namespace Yulang.GeneralDictionary171SelectedAssembly
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionary171SpineCoverage
open GeneralDictionaryRecursiveEvidence GeneralDictionary171BoundedAssembly
variable {roles : Roles.RoleDecls}

/-- Local structure supplies the current instance without asking for child
Evidence. All alternatives use one and the same current model. -/
theorem node_instance {registry : Registry} {state : Tracked roles}
    {root occurrence : Occurrence roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (node : Node registry state occurrence) :
    Instance registry state.current.context model occurrence node.key node.children := by
  have metadata := GeneralDictionarySharedMetadata.formed_metadata formed
  cases node with
  | old previous =>
    cases previous with
    | recorded packet member relocation =>
      exact GeneralDictionaryRecorded168Relocation.current_instance formed packet member relocation model valid
    | scalar occurrence declaration visible checked shape =>
      exact GeneralDictionaryScalarLeaf.instance_of_shape _ _ _ _ visible checked shape metadata model valid.1
    | spine occurrence declaration visible checked shape =>
      exact GeneralDictionarySpineLeaf.instance_of_shape _ _ _ _ visible checked shape metadata model valid.1
    | named occurrence declaration visible checked shape =>
      exact GeneralDictionary169NamedLeaf.instance_of_shape _ _ _ _ visible checked shape metadata model valid.1
  | namedSpine declaration visible checked shape =>
    exact GeneralDictionary170NamedSpine.instance_of_shape _ _ _ _ visible checked shape metadata model valid.1

/-- Exact selected child order, not just key agreement, is recovered. -/
theorem node_selected {registry : Registry} {state : Tracked roles}
    {root occurrence : Occurrence roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (node : Node registry state occurrence)
    (selected : GeneralNominalFeedbackK2.Local registry state.current occurrence (.selected key children)) :
    node.key = key ∧ node.children = children :=
  GeneralDictionarySelectedInstanceCoherence.instance_selected _ _ _ model _ _ _ _
    (node_instance formed model valid node) selected

/-- Supplied local coverages of one selected domain give the identical runtime
Option result at every common fuel, even if their structural certificates differ. -/
theorem assemble_independent {registry : Registry} {state : Tracked roles}
    {root : Occurrence roles} {domain : Occurrence roles → Prop}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (selected : ∀ occurrence, domain occurrence → ∃ key children,
      GeneralNominalFeedbackK2.Local registry state.current occurrence (.selected key children))
    (first second : Coverage registry state domain) (fuel : Nat) (focus : Subtype domain) :
    assemble first fuel focus = assemble second fuel focus := by
  apply GeneralDictionary171AssemblyPersistence.assemble_congr
  · intro occurrence member
    obtain ⟨key,children,choice⟩ := selected occurrence member
    exact (node_selected formed model valid (first.node occurrence member) choice).2.trans
      (node_selected formed model valid (second.node occurrence member) choice).2.symm
  · intro occurrence member
    obtain ⟨key,children,choice⟩ := selected occurrence member
    exact (node_selected formed model valid (first.node occurrence member) choice).1.trans
      (node_selected formed model valid (second.node occurrence member) choice).1.symm

/-- The same result holds for the derived rank budget used by build. -/
theorem build_independent {registry : Registry} {state : Tracked roles}
    {root : Occurrence roles} {domain : Occurrence roles → Prop}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (selected : ∀ occurrence, domain occurrence → ∃ key children,
      GeneralNominalFeedbackK2.Local registry state.current occurrence (.selected key children))
    (first second : Coverage registry state domain) (focus : Subtype domain) :
    build first focus = build second focus :=
  assemble_independent formed model valid selected first second _ focus
end Yulang.GeneralDictionary171SelectedAssembly
