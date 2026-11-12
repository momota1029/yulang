import Yulang.GeneralDictionaryUnrecordedVariableJoint

/-! Distinct current selections in one alias class preclude Joint even without
any recorded packet. These are implications, not a reachable counterexample. -/
namespace Yulang.GeneralDictionarySelectedAliasConflict
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalJointCandidates GeneralNominalRecursiveCandidates
variable {roles : Roles.RoleDecls}

/-- A current branch carries Prepared, so current uniqueness identifies its
key without using any historical packet or same-model amalgamation theorem. -/
theorem branch_selected_key (registry : Registry) (state : State roles)
    (focus : Occurrence roles) (key selectedKey : Nat)
    (model : GeneralNominalCommonBridge.Assignment)
    (branch : BranchAt registry state focus key model)
    (children : List (Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry state focus (.selected selectedKey children)) :
    key = selectedKey := by
  obtain ⟨declaration,visible,checked,identity,role,prepared,bounds,located,_⟩ := branch
  cases selected with
  | selected safe unique =>
    let emitted := GeneralNominalAllocation.children state.context.state registry focus declaration checked
      (GeneralNominalRecursiveInspection.bindings state.context.state (report state.context declaration bounds))
    have survivor : GeneralNominalRecursiveCandidates.Survivor registry state.context focus key emitted :=
      ⟨safe.1,declaration,visible,checked,identity,role,bounds,located,prepared,rfl⟩
    exact (unique.2 key emitted survivor).1

/-- Every selected related site must agree with a Joint key. This derives a
necessary coherence condition rather than assuming aliases have equal keys. -/
theorem joint_related_selected_key (registry : Registry) (state : State roles)
    (focus : Occurrence roles) (key selectedKey : Nat)
    (joint : Joint registry state focus key)
    (site : GeneralNominalDemandMerging.Site roles) (related : Related state focus site)
    (children : List (Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry state site.occurrence (.selected selectedKey children)) :
    key = selectedKey := by
  obtain ⟨model,_,_,branches⟩ := joint.2
  exact branch_selected_key registry state site.occurrence key selectedKey model
    (branches site related) children selected

/-- The obstruction concerns current selections, not previously recorded key
conflicts. No existence of such a reachable configuration is asserted. -/
theorem different_selected_no_joint (registry : Registry) (state : State roles)
    (focus : Occurrence roles) (firstKey lastKey : Nat)
    (firstChildren lastChildren : List (Occurrence roles))
    (first : GeneralNominalFeedbackK2.Local registry state focus (.selected firstKey firstChildren))
    (site : GeneralNominalDemandMerging.Site roles) (related : Related state focus site)
    (last : GeneralNominalFeedbackK2.Local registry state site.occurrence (.selected lastKey lastChildren))
    (different : firstKey ≠ lastKey) : ∀ key, ¬ Joint registry state focus key := by
  intro key joint
  obtain ⟨model,_,branch,_⟩ := joint.2
  have one := branch_selected_key registry state focus key firstKey model branch firstChildren first
  have two := joint_related_selected_key registry state focus key lastKey joint site related lastChildren last
  exact different (one.symm.trans two)

/-- Same implication at the actual support boundary. Reachability, stability,
inhabitation and nonempty children would still have to be constructed separately. -/
theorem support_different_selected_no_joint (registry : Registry)
    (state : GeneralNominalSupport.Tracked roles) (focus : Occurrence roles)
    (firstKey lastKey : Nat) (firstChildren lastChildren : List (Occurrence roles))
    (first : GeneralNominalSupportBoundary.Local registry state focus (.selected firstKey firstChildren))
    (site : GeneralNominalDemandMerging.Site roles) (related : Related state.current focus site)
    (last : GeneralNominalSupportBoundary.Local registry state site.occurrence (.selected lastKey lastChildren))
    (different : firstKey ≠ lastKey) : ∀ key, ¬ Joint registry state.current focus key :=
  different_selected_no_joint registry state.current focus firstKey lastKey firstChildren lastChildren
    (GeneralNominalSupportBoundary.selected_old first) site related
    (GeneralNominalSupportBoundary.selected_old last) different
end Yulang.GeneralDictionarySelectedAliasConflict
