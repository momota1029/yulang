import Yulang.GeneralDictionaryCenteredScalar177
import Yulang.GeneralDictionaryClosedTreeBranch

/-! Current closed-tree source certificates at centered selection. Unlike the
terminal scalar fragment, this consumer permits emitted children and named
outputs when their finite source trees are structurally observed. -/
namespace Yulang.GeneralDictionaryCenteredClosed177
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralDictionaryRecursiveEvidence (Instance Evidence)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
open GeneralNominalCenteredBoundary (Local)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}
  {focus : Occurrence roles} {key : Nat} {children : List (Occurrence roles)}

theorem selected_instance (declaration : Declaration)
    (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : GeneralDictionaryClosedTreeBranch.Shape state.erased.current.context registry focus declaration checked)
    (selected : Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    declaration.id = key ∧ Instance registry state.erased.current.context model focus key children := by
  have old : GeneralNominalFeedbackK2.Local registry state.erased.current focus (.selected key children) := by
    cases selected with
    | selected safe unique =>
      exact .selected ⟨safe.1,fun h => safe.2.1 (Or.inl h),
        fun h => safe.2.2.1 (Or.inl h),fun h => safe.2.2.2 (Or.inl h)⟩ unique
  exact GeneralDictionaryClosedTreeBranch.selected_instance registry state.erased.current focus
    declaration visible checked shape key children old model valid.1.1

theorem selected_evidence (declaration : Declaration)
    (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : GeneralDictionaryClosedTreeBranch.Shape state.erased.current.context registry focus declaration checked)
    (selected : Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (dictionaries : List Payload)
    (given : All₂ (Evidence registry state.erased.current.context model) children dictionaries) :
    Evidence registry state.erased.current.context model focus (.node key dictionaries) :=
  GeneralDictionaryRecursiveEvidence.evidence_node registry state.erased.current.context model focus
    key children dictionaries (selected_instance declaration visible checked shape selected model valid).2 given

end Yulang.GeneralDictionaryCenteredClosed177
