import Yulang.GeneralDictionaryFiniteTreeBranch
import Yulang.GeneralDictionaryObservedAliasJoint
import Yulang.GeneralDictionaryClosedAliasJoint

/-! Arbitrary finite-arity closed nominal-output-aware structural alias Joint. Recorded descriptor trees,
not desired branch validity, justify compound outputs in one unchanged model. -/
namespace Yulang.GeneralDictionaryFiniteAliasJoint
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps GeneralNominalJointCandidates
variable {roles : Roles.RoleDecls}

def Shape (context : GeneralNominalCandidates.Context) (registry : Registry)
    (focus : Occurrence roles) (chosen : Declaration)
    (checked : DeclarationChecked registry.constructors roles chosen) : Prop :=
  Nonempty (GeneralDictionaryFiniteTreeBranch.Shape context registry focus chosen checked) ∨
    GeneralDictionaryObservedAliasJoint.Shape context registry focus chosen checked

def Covered (registry : Registry) (state : Tracked roles) (focus : Occurrence roles)
    (chosen : Declaration) (checked : DeclarationChecked registry.constructors roles chosen) : Prop :=
  ∀ site, Related state.current focus site →
    Shape state.current.context registry site.occurrence chosen checked ∧
    ∃ key children, GeneralNominalSupportBoundary.Local registry state site.occurrence (.selected key children)

theorem shape_of_closed (context : GeneralNominalCandidates.Context) (registry : Registry)
    (focus : Occurrence roles) (chosen : Declaration)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (shape : GeneralDictionaryClosedAliasJoint.Shape context registry focus chosen checked) :
    Shape context registry focus chosen checked := by
  rcases shape with observed | previous
  · obtain ⟨witness⟩ := observed
    exact Or.inl ⟨GeneralDictionaryFiniteTreeBranch.of_closed context registry focus chosen checked witness⟩
  · exact Or.inr previous

theorem covered_of_closed (registry : Registry) (state : Tracked roles) (focus : Occurrence roles)
    (chosen : Declaration) (checked : DeclarationChecked registry.constructors roles chosen)
    (covered : GeneralDictionaryClosedAliasJoint.Covered registry state focus chosen checked) :
    Covered registry state focus chosen checked := by
  intro site related
  obtain ⟨shape,selected⟩ := covered site related
  exact ⟨shape_of_closed _ _ _ _ _ shape,selected⟩

theorem selected_branch (registry : Registry) (state : Tracked roles) (focus : Occurrence roles)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (shape : Shape state.current.context registry focus chosen checked)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    chosen.id = key ∧ BranchAt registry state.current focus chosen.id model := by
  rcases shape with observed | previous
  · obtain ⟨observed⟩ := observed
    have result := GeneralDictionaryFiniteTreeBranch.selected_instance registry state.current focus chosen
      visible checked observed key children (GeneralNominalSupportBoundary.selected_old selected) model valid.1
    have survivor : GeneralNominalRecursiveCandidates.Survivor registry state.current.context focus key children := by
      cases selected with | selected _ unique => exact unique.1
    have branch := GeneralNominalStructuralSelectedGraph.branchAt_of_instance registry state.current focus key children
      survivor model result.2
    exact ⟨result.1,result.1.symm ▸ branch⟩
  · exact GeneralDictionaryObservedAliasJoint.selected_branch registry state focus chosen visible checked
      previous key children selected model valid

theorem covered_joint (registry : Registry) (root focus : Occurrence roles) (state : Tracked roles)
    (formed : SourceFormed registry root state)
    (growth : ∀ packet ∈ state.current.packets,
      GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (shape : Shape state.current.context registry focus chosen checked)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (covered : Covered registry state focus chosen checked)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Joint registry state.current focus key := by
  have branch := selected_branch registry state focus chosen visible checked shape key children selected model valid
  refine ⟨?_,model,valid,branch.1 ▸ branch.2,?_⟩
  · intro packet member alias
    have related : Related state.current focus packet.site :=
      ⟨GeneralDictionaryFiniteJournalJoint.packet_site registry root state formed packet member,alias⟩
    obtain ⟨localShape,localKey,localChildren,localSelected⟩ := covered packet.site related
    have replay := GeneralDictionaryOrdinarySelectedReplay.selected_replay registry root packet.site.occurrence state
      formed packet member (growth packet member) rfl localKey localChildren localSelected model valid
    have localBranch := selected_branch registry state packet.site.occurrence chosen visible checked
      localShape localKey localChildren localSelected model valid
    exact replay.1.trans (localBranch.1.symm.trans branch.1)
  · intro site related
    obtain ⟨localShape,localKey,localChildren,localSelected⟩ := covered site related
    exact branch.1 ▸ (selected_branch registry state site.occurrence chosen visible checked localShape
      localKey localChildren localSelected model valid).2

/-- A conditional support node theorem permitting closed nominal outputs. Joint
is a derived result, and child dictionaries remain explicit real obligations. -/
theorem ordinary_stable_evidence (registry : Registry) (root focus : Occurrence roles)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (state : Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (stable : Stable registry state focus)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (shape : Shape state.current.context registry focus chosen checked)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (covered : Covered registry state focus chosen checked)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model) children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model focus (.node key dictionaries) := by
  have reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state :=
    ⟨GeneralNominalSupport.initial context root,⟨context,source,rfl⟩,
      GeneralDictionarySupportOrdinaryExecution.steps_actual path⟩
  have joint := covered_joint registry root focus state
    (GeneralDictionarySupportOrdinaryExecution.steps_formed (.initial context source) path)
    (GeneralDictionarySupportOrdinaryExecution.initial_packets_extension registry root context state path)
    chosen visible checked shape key children selected covered model valid
  exact GeneralDictionarySupportEvidence.reachable_joint_evidence registry state root focus reachable key children
    stable selected joint model valid dictionaries given
end Yulang.GeneralDictionaryFiniteAliasJoint
