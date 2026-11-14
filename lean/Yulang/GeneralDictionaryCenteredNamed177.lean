import Yulang.GeneralDictionaryCenteredScalar177
import Yulang.GeneralDictionary172CheckedSpineExact

/-! Centered selected terminal nominal spines with named outputs. A finite
inspection checker supplies the output certificate; neither journal membership
nor a supplied semantic Instance is used. Coverage is only this syntax fragment. -/
namespace Yulang.GeneralDictionaryCenteredNamed177
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredSteps GeneralNominalRecursiveCandidates
open GeneralNominalCenteredBoundary (Local)
open GeneralDictionaryRecursiveEvidence (Instance Evidence)
open GeneralDictionaryReadback (Payload)
open GeneralDictionary171SpineDiscovery (Input RequestsFinished)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}
  {focus : Occurrence roles} {key : Nat} {children : List (Occurrence roles)}

theorem selected_named (declaration : Declaration)
    (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (input : Input state.erased.current.context focus declaration)
    (tested : RequestsFinished registry state.erased.current.context focus declaration checked input)
    (selected : Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    declaration.id = key ∧ children = [] ∧
    Instance registry state.erased.current.context model focus key [] ∧
    Evidence registry state.erased.current.context model focus (.node key []) := by
  have old : GeneralNominalFeedbackK2.Local registry state.erased.current focus (.selected key children) := by
    cases selected with
    | selected safe unique =>
      exact .selected ⟨safe.1,fun h => safe.2.1 (Or.inl h),
        fun h => safe.2.2.1 (Or.inl h),fun h => safe.2.2.2 (Or.inl h)⟩ unique
  have metadata : Metadata registry state.erased.current.context := by
    cases old with
    | selected _ unique =>
      obtain ⟨_,_,_,_,_,_,_,_,prepared,_⟩ := unique.1
      exact prepared.1
  have instanceRule := GeneralDictionary170NamedSpine.instance_of_shape _ registry focus declaration
    visible checked (GeneralDictionary171SpineDiscovery.shape _ _ _ _ _ input tested)
    metadata model valid.1.1
  have same := GeneralDictionarySelectedInstanceCoherence.instance_selected registry state.erased.current
    focus model declaration.id key [] children instanceRule old
  refine ⟨same.1,same.2.symm,?_,?_⟩
  · simpa only [same.1] using instanceRule
  · apply (GeneralDictionaryRecursiveEvidence.evidence_leaf_iff _ _ _ _ _).mpr
    simpa only [same.1] using instanceRule

/-- The model is quantified after the Boolean certificate: one successful
finite inspection certifies the node in every current centered model. -/
theorem checked_named (declaration : Declaration)
    (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (input : Input state.erased.current.context focus declaration)
    (accepted : GeneralDictionary171CheckedSpine.check registry state.erased.current.context focus declaration checked input = true)
    (selected : Local registry state focus (.selected key children)) :
    ∀ model, Models state model →
      declaration.id = key ∧ children = [] ∧
      Instance registry state.erased.current.context model focus key [] ∧
      Evidence registry state.erased.current.context model focus (.node key []) :=
  selected_named declaration visible checked input
    ((GeneralDictionary172CheckedSpineExact.check_iff ..).mp accepted) selected

/-- Syntactic/inspection coverage, not an assumption of Evidence or completion. -/
def Covered (registry : Registry) (state : State roles) (focus : Occurrence roles) : Prop :=
  ∃ declaration, ∃ _visible : declaration ∈ registry.declarations,
    ∃ checked : DeclarationChecked registry.constructors roles declaration,
    ∃ input : Input state.erased.current.context focus declaration,
      GeneralDictionary171CheckedSpine.check registry state.erased.current.context focus declaration checked input = true

theorem covered_evidence (coverage : Covered registry state focus)
    (selected : Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (dictionaries : List Payload)
    (given : All₂ (Evidence registry state.erased.current.context model) children dictionaries) :
    Evidence registry state.erased.current.context model focus (.node key dictionaries) := by
  obtain ⟨declaration,visible,checked,input,accepted⟩ := coverage
  obtain ⟨_,empty,_,leaf⟩ := checked_named declaration visible checked input accepted selected model valid
  rw [empty] at given
  cases given
  exact leaf
end Yulang.GeneralDictionaryCenteredNamed177
