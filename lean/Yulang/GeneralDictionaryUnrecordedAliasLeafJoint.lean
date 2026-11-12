import Yulang.GeneralDictionaryAliasTreeLocality

/-! Independent same-model Joint for a structurally covered alias class.
No packet at the focus, Coherent, Scheduled, Joint or BranchModels is assumed.
All sites use the actual chosen declaration's terminal/no-output syntax. -/
namespace Yulang.GeneralDictionaryUnrecordedAliasLeafJoint
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps GeneralNominalJointCandidates
variable {roles : Roles.RoleDecls}

/-- Every alias site has structural syntax for one declaration and an actual
current selection. Their selected keys are deliberately not identified here. -/
def Covered (registry : Registry) (state : Tracked roles) (focus : Occurrence roles)
    (chosen : Declaration) : Prop :=
  ∀ site, Related state.current focus site →
    GeneralDictionaryAliasTreeLocality.Leaf state.current.context site.occurrence chosen ∧
    ∃ key children, GeneralNominalSupportBoundary.Local registry state site.occurrence (.selected key children)

/-- Structural syntax builds the instance before using current uniqueness. -/
theorem leaf_instance (registry : Registry) (state : Tracked roles) (focus : Occurrence roles)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (leaf : GeneralDictionaryAliasTreeLocality.Leaf state.current.context focus chosen)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    GeneralDictionaryRecursiveEvidence.Instance registry state.current.context model focus chosen.id [] := by
  have metadata : GeneralNominalRecursiveCandidates.Metadata registry state.current.context := by
    cases selected with
    | selected _ unique =>
      obtain ⟨_,_,_,_,_,_,_,_,prepared,_⟩ := unique.1
      exact prepared.1
  rcases leaf with tree | scalar
  · obtain ⟨tree⟩ := tree
    exact GeneralDictionaryTreeLeaf.instance_of_shape _ _ _ _ visible checked tree metadata model valid.1
  · obtain ⟨scalar⟩ := scalar
    exact GeneralDictionaryScalarLeaf.instance_of_shape _ _ _ _ visible checked scalar metadata model valid.1

/-- Actual uniqueness, not an assumed key equality, identifies every alias's
selected key with the syntactically covered declaration. -/
theorem leaf_selected (registry : Registry) (state : Tracked roles) (focus : Occurrence roles)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (leaf : GeneralDictionaryAliasTreeLocality.Leaf state.current.context focus chosen)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    chosen.id = key ∧ [] = children := by
  have rule := leaf_instance registry state focus chosen visible checked leaf key children selected model valid
  cases selected with
  | selected safe unique =>
    exact unique.2 _ _ (GeneralDictionaryOrdinarySelectedReplay.survivor_of_instance
      registry state.current.context focus key children unique.1 model chosen.id [] rule)

/-- Journal key coherence is derived by replay and uniqueness; no focus packet
or independently supplied Coherent premise is needed. -/
theorem covered_joint (registry : Registry) (root focus : Occurrence roles) (state : Tracked roles)
    (formed : SourceFormed registry root state)
    (growth : ∀ packet ∈ state.current.packets,
      GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (leaf : GeneralDictionaryAliasTreeLocality.Leaf state.current.context focus chosen)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (covered : Covered registry state focus chosen)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Joint registry state.current focus key := by
  have identity := (leaf_selected registry state focus chosen visible checked leaf key children selected model valid).1
  refine ⟨?_,model,valid,?_,?_⟩
  · intro packet member alias
    have related : Related state.current focus packet.site :=
      ⟨GeneralDictionaryFiniteJournalJoint.packet_site registry root state formed packet member,alias⟩
    obtain ⟨localLeaf,localKey,localChildren,localSelected⟩ := covered packet.site related
    have replay := GeneralDictionaryOrdinarySelectedReplay.selected_replay registry root packet.site.occurrence state
      formed packet member (growth packet member) rfl localKey localChildren localSelected model valid
    have localIdentity := (leaf_selected registry state packet.site.occurrence chosen visible checked
      localLeaf localKey localChildren localSelected model valid).1
    exact replay.1.trans (localIdentity.symm.trans identity)
  · rw [← identity]
    exact GeneralDictionaryAliasTreeLocality.leaf_branch registry state focus chosen visible checked
      leaf key children selected model valid
  · intro site related
    obtain ⟨localLeaf,localKey,localChildren,localSelected⟩ := covered site related
    rw [← identity]
    exact GeneralDictionaryAliasTreeLocality.leaf_branch registry state site.occurrence chosen visible checked
      localLeaf localKey localChildren localSelected model valid

/-- A finite actual ordinary trace supplies formation and packet growth. There
is no scheduling premise and no requirement that the focus has been recorded. -/
theorem initial_trace_joint (registry : Registry) (root focus : Occurrence roles)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (state : Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (leaf : GeneralDictionaryAliasTreeLocality.Leaf state.current.context focus chosen)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (covered : Covered registry state focus chosen)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Joint registry state.current focus key :=
  covered_joint registry root focus state
    (GeneralDictionarySupportOrdinaryExecution.steps_formed (.initial context source) path)
    (GeneralDictionarySupportOrdinaryExecution.initial_packets_extension registry root context state path)
    chosen visible checked leaf key children selected covered model valid
end Yulang.GeneralDictionaryUnrecordedAliasLeafJoint
