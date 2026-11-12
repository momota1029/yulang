import Yulang.GeneralDictionaryUnrecordedAliasLeafJoint
import Yulang.GeneralDictionaryVariableTree
import Yulang.GeneralDictionaryEdgeOrigin

/-! Independent Joint for first-time variable-requirement branches. Nonempty
children are retained. Stability is used only AFTER Joint has been constructed. -/
namespace Yulang.GeneralDictionaryUnrecordedVariableJoint
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps GeneralNominalJointCandidates
variable {roles : Roles.RoleDecls}

def Shape (context : GeneralNominalCandidates.Context) (focus : Occurrence roles)
    (chosen : Declaration) : Prop :=
  Nonempty (GeneralDictionaryVariableTree.TreeBranchShape context focus chosen) ∨
    GeneralDictionaryAliasTreeLocality.Leaf context focus chosen

def Covered (registry : Registry) (state : Tracked roles) (focus : Occurrence roles)
    (chosen : Declaration) : Prop :=
  ∀ site, Related state.current focus site → Shape state.current.context site.occurrence chosen ∧
    ∃ key children, GeneralNominalSupportBoundary.Local registry state site.occurrence (.selected key children)

/-- Same current assignment; no conclusion-shaped branch assumption. Selection
identifies the syntactically constructed key, while preserving actual children. -/
theorem selected_branch (registry : Registry) (state : Tracked roles) (focus : Occurrence roles)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (shape : Shape state.current.context focus chosen)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    chosen.id = key ∧ BranchAt registry state.current focus chosen.id model := by
  rcases shape with variableShape | leaf
  · obtain ⟨tree⟩ := variableShape
    have result := GeneralDictionaryVariableTree.selected_instance registry state.current focus chosen visible
      checked tree key children (GeneralNominalSupportBoundary.selected_old selected) model valid.1
    have survivor : GeneralNominalRecursiveCandidates.Survivor registry state.current.context focus key children := by
      cases selected with | selected _ unique => exact unique.1
    refine ⟨result.1,?_⟩
    rw [result.1]
    exact GeneralNominalStructuralSelectedGraph.branchAt_of_instance registry state.current focus key children
      survivor model result.2
  · exact ⟨(GeneralDictionaryUnrecordedAliasLeafJoint.leaf_selected registry state focus chosen visible checked
      leaf key children selected model valid).1,
      GeneralDictionaryAliasTreeLocality.leaf_branch registry state focus chosen visible checked
        leaf key children selected model valid⟩

/-- Arbitrarily many related sites share one model. Key consistency with all
old packets is proved, not assumed. The focus need not have an old packet. -/
theorem covered_joint (registry : Registry) (root focus : Occurrence roles) (state : Tracked roles)
    (formed : SourceFormed registry root state)
    (growth : ∀ packet ∈ state.current.packets,
      GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (shape : Shape state.current.context focus chosen)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (covered : Covered registry state focus chosen)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Joint registry state.current focus key := by
  have branch := selected_branch registry state focus chosen visible checked shape key children selected model valid
  refine ⟨?_,model,valid,?_,?_⟩
  · intro packet member alias
    have related : Related state.current focus packet.site :=
      ⟨GeneralDictionaryFiniteJournalJoint.packet_site registry root state formed packet member,alias⟩
    obtain ⟨localShape,localKey,localChildren,localSelected⟩ := covered packet.site related
    have replay := GeneralDictionaryOrdinarySelectedReplay.selected_replay registry root packet.site.occurrence state
      formed packet member (growth packet member) rfl localKey localChildren localSelected model valid
    have localBranch := selected_branch registry state packet.site.occurrence chosen visible checked
      localShape localKey localChildren localSelected model valid
    exact replay.1.trans (localBranch.1.symm.trans branch.1)
  · exact branch.1 ▸ branch.2
  · intro site related
    obtain ⟨localShape,localKey,localChildren,localSelected⟩ := covered site related
    exact branch.1 ▸ (selected_branch registry state site.occurrence chosen visible checked localShape
      localKey localChildren localSelected model valid).2

theorem initial_trace_joint (registry : Registry) (root focus : Occurrence roles)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (state : Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (shape : Shape state.current.context focus chosen)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (covered : Covered registry state focus chosen)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Joint registry state.current focus key :=
  covered_joint registry root focus state
    (GeneralDictionarySupportOrdinaryExecution.steps_formed (.initial context source) path)
    (GeneralDictionarySupportOrdinaryExecution.initial_packets_extension registry root context state path)
    chosen visible checked shape key children selected covered model valid

/-- No circular packet coverage: Joint is constructed from syntax and the
ordinary trace first; stability then forces a packet for nonempty children. -/
theorem stable_nonterminal_packet (registry : Registry) (root focus : Occurrence roles)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (state : Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (shape : Shape state.current.context focus chosen)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (covered : Covered registry state focus chosen)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (stable : Stable registry state focus) (nonempty : children ≠ []) :
    ∃ packet ∈ state.current.packets, packet.site.occurrence = focus := by
  have reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state :=
    ⟨GeneralNominalSupport.initial context root,⟨context,source,rfl⟩,
      GeneralDictionarySupportOrdinaryExecution.steps_actual path⟩
  exact GeneralDictionaryEdgeOrigin.selected_nonterminal_packet registry root focus state reachable key children
    stable selected (initial_trace_joint registry root focus context source state path chosen visible checked
      shape key children selected covered model valid) nonempty

/-- Actual stability now supplies recorded support and all selected children.
A single inhabited current assignment establishes Joint independently; the
conclusion's Instance then holds for EVERY current journal model. -/
theorem stable_instances_generated (registry : Registry) (root focus : Occurrence roles)
    (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (state : Tracked roles)
    (path : B4Target.Steps (GeneralDictionarySupportOrdinaryExecution.Step registry root)
      (GeneralNominalSupport.initial context root) state)
    (chosen : Declaration) (visible : chosen ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles chosen)
    (shape : Shape state.current.context focus chosen)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (covered : Covered registry state focus chosen)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (stable : Stable registry state focus) :
    (∀ assignment, Models state.current assignment →
      GeneralDictionaryRecursiveEvidence.Instance registry state.current.context assignment focus key children) ∧
      ∀ child ∈ children, Generated state.current focus child := by
  have reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state :=
    ⟨GeneralNominalSupport.initial context root,⟨context,source,rfl⟩,
      GeneralDictionarySupportOrdinaryExecution.steps_actual path⟩
  exact GeneralDictionarySupportEvidence.reachable_joint_instance registry state root focus reachable key children
    stable selected (initial_trace_joint registry root focus context source state path chosen visible checked
      shape key children selected covered model valid)
end Yulang.GeneralDictionaryUnrecordedVariableJoint
