import Yulang.GeneralDictionaryCenteredCandidate176
import Yulang.GeneralDictionaryCenteredReady176
import Yulang.GeneralDictionaryScalarLeaf

/-! Packet-free scalar leaves for the exact centered boundary. These producers
use syntax and the current normalized scalar head, not journal membership.
The general EvidenceNode field still needs coverage of non-scalar selections. -/
namespace Yulang.GeneralDictionaryCenteredScalar177
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredSteps GeneralDictionaryCenteredCandidate176
open GeneralNominalCenteredBoundary (Local)
open GeneralDictionaryRecursiveEvidence (Instance Evidence)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}
  {focus : Occurrence roles} {key : Nat} {children : List (Occurrence roles)}

/-- A current candidate with a branch valid in the supplied model suffices.
Child-edge commitment is irrelevant to the local Instance judgment. -/
theorem candidate_instance_of_holds {plan : Plan roles}
    (candidate : Candidate registry state focus key children plan)
    (model : GeneralNominalCommonBridge.Assignment)
    (holds : plan.packet.Holds model) :
    Instance registry state.erased.current.context model focus key children := by
  obtain ⟨metadata,_,_,bounds,found,finished,ready,_⟩ := candidate.prepared
  have same := Option.some.inj (candidate.located.symm.trans found)
  subst bounds
  have source : Instance plan.packet.registry plan.packet.context model
      plan.packet.site.occurrence plan.packet.declaration.id plan.packet.children := by
    refine ⟨plan.packet.declaration,?_,plan.packet.checked,rfl,?_,plan.packet.bounds,
      candidate.located,finished,ready,rfl,metadata,holds⟩
    · simpa only [candidate.registry_eq] using candidate.visible
    · simpa only [candidate.occurrence_eq] using candidate.role
  simpa only [candidate.registry_eq,candidate.context_eq,candidate.occurrence_eq,
    candidate.key_eq,candidate.children_eq] using source

/-- A current candidate which is already committed need not be installed or
present in the journal in order to supply its source instance. -/
theorem committed_candidate_instance {plan : Plan roles}
    (candidate : Candidate registry state focus key children plan)
    (committed : GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    Instance registry state.erased.current.context model focus key children := by
  exact candidate_instance_of_holds candidate model (committed.1 model valid.1)

/-- The full commitment of a scalar candidate is automatic, including its
empty child-edge obligation. No packet insertion or historical membership. -/
theorem scalar_candidate_committed {plan : Plan roles}
    (candidate : Candidate registry state focus key children plan)
    (shape : GeneralDictionaryScalarLeaf.ScalarLeafShape plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration) :
    GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet := by
  constructor
  · intro model valid
    have same := Option.some.inj (candidate.located.symm.trans shape.located)
    change GeneralNominalRecursiveCandidates.BranchModels plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.checked plan.packet.bounds model
    rw [same]
    apply GeneralDictionaryScalarLeaf.branch_models _ _ _ _ _ shape model
    simpa only [candidate.context_eq] using valid.1
  · intro child member
    have empty : plan.packet.children = [] :=
      GeneralDictionaryLinearLeaf.children_empty plan.packet.context plan.packet.registry
        plan.packet.site.occurrence plan.packet.declaration plan.packet.checked shape.terminal _
    rw [empty] at member
    cases member

/-- Center-aware selection has the same survivor predicate as the raw feedback
selection. Only its safety checks are stronger. -/
theorem selected_scalar {declaration : Declaration}
    (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : GeneralDictionaryScalarLeaf.ScalarLeafShape state.erased.current.context focus declaration)
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
  exact GeneralDictionaryScalarLeaf.selected_leaf registry state.erased.current focus
    declaration visible checked shape key children old model valid.1.1

/-- Scalar coverage is syntactic; key and emitted children are derived from
current uniqueness. Neither reachability nor stability is required. -/
theorem scalar_coverage
    (coverage : GeneralDictionaryScalarLeaf.HasScalarLeaf registry state.erased.current.context focus)
    (selected : Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model) :
    children = [] ∧ Instance registry state.erased.current.context model focus key [] ∧
    Evidence registry state.erased.current.context model focus (.node key []) := by
  obtain ⟨declaration,visible,checked,⟨shape⟩⟩ := coverage
  exact (selected_scalar visible checked shape selected model valid).2

/-- Direct EvidenceNode-shaped consumer for scalar coverage. The supplied list
of child dictionaries is forced empty; no recorded-tree producer is needed. -/
theorem scalar_evidence
    (coverage : GeneralDictionaryScalarLeaf.HasScalarLeaf registry state.erased.current.context focus)
    (selected : Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state model)
    (dictionaries : List Payload)
    (given : All₂ (Evidence registry state.erased.current.context model) children dictionaries) :
    Evidence registry state.erased.current.context model focus (.node key dictionaries) := by
  obtain ⟨empty,_,leaf⟩ := scalar_coverage coverage selected model valid
  rw [empty] at given
  cases given
  exact leaf

/-- The existing selected-plan obligation can be weakened by a packet-free
scalar branch. This is an outstanding coverage property, not asserted here. -/
def ScalarOrInstallable (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (GeneralNominalCenteredGroundBoundary.groundBoundary roles).Checked registry →
    ∀ state root, B4TargetV5.Reachable (GeneralNominalCenteredGroundBoundary.groundBoundary roles) registry root state →
    (∃ model, Models state model) → ∀ focus key children,
    (focus = root ∨ (GeneralNominalCenteredGroundBoundary.groundBoundary roles).Generated registry state root focus) →
    Stable registry state focus → Local registry state focus (.selected key children) →
    GeneralDictionaryScalarLeaf.HasScalarLeaf registry state.erased.current.context focus ∨
    ∃ plan : Plan roles, plan.packet.site.occurrence = focus ∧
      GeneralNominalCenteredBoundary.Installable registry state plan

theorem evidenceNode_of_scalarOrInstallable (coverage : ScalarOrInstallable roles) :
    B4SkeletonV5.EvidenceNode (GeneralNominalCenteredGroundBoundary.groundBoundary roles) := by
  intro registry checked state root reachable model valid focus key children dictionaries
    reached stable _ safe unique given
  have selected : Local registry state focus (.selected key children) :=
    (GeneralNominalCenteredBoundary.local_correspondence registry state focus _).mp
      (B4TargetV3.Local.selected safe unique)
  rcases coverage registry checked state root reachable ⟨model,valid⟩ focus key children reached stable selected with scalar | ⟨plan,same,enabled⟩
  · exact scalar_evidence scalar selected model valid dictionaries given
  · exact GeneralDictionaryCenteredReady176.selected_evidence stable selected plan same enabled model valid dictionaries given
end Yulang.GeneralDictionaryCenteredScalar177
