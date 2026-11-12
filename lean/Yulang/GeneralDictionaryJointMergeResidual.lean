import Yulang.GeneralDictionaryJointMerge

/-! Two independently inhabited Joint predicates discharge the journal-key
part, not the simultaneous-model part, of merge transport. This file gives
an exact criterion and does not claim a counterexample to enabled merging. -/
namespace Yulang.GeneralDictionaryJointMergeResidual
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalJointCandidates
open GeneralNominalDemandMerging (Site)
variable {roles : Roles.RoleDecls}

/-- The genuinely shared witness still needed after separate Joint proofs.
Every branch and every added associated equation uses this one assignment. -/
def Shared (registry : Registry) (state : State roles) (first last : Site roles)
    (key : Nat) : Prop :=
  ∃ model, Models state model ∧
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalDemandMerging.outputAtoms first last) ∧
    ∀ site ∈ state.sites,
      (Alias state first.occurrence.identity site.occurrence.identity ∨
       Alias state last.occurrence.identity site.occurrence.identity) →
      BranchAt registry state site.occurrence key model

/-- Once both old classes independently support the SAME key, and the first
representative is registered, Shared is exactly the remaining obligation.
No old witnesses are equated or chosen as the new witness. -/
theorem separate_joint_merge_iff (registry : Registry) (state : State roles)
    (first last : Site roles) (registered : first ∈ state.sites)
    (key : Nat) (left : Joint registry state first.occurrence key)
    (right : Joint registry state last.occurrence key) :
    Joint registry (merge state first last) first.occurrence key ↔
      Shared registry state first last key := by
  obtain ⟨leftModel,_,leftBranch,_⟩ := left.2
  obtain ⟨rightModel,_,rightBranch,_⟩ := right.2
  have leftTargets := GeneralDictionaryJointMerge.branch_output_targets registry state
    first.occurrence key leftModel leftBranch
  have rightTargets := GeneralDictionaryJointMerge.branch_output_targets registry state
    last.occurrence key rightModel rightBranch
  rw [GeneralDictionaryJointMerge.joint_merge_iff registry state first last leftTargets rightTargets key]
  constructor
  · rintro ⟨_,model,valid,outputs,_,branches⟩
    exact ⟨model,valid,outputs,branches⟩
  · rintro ⟨model,valid,outputs,branches⟩
    refine ⟨?_,model,valid,outputs,branches first registered (Or.inl (.refl _)),branches⟩
    intro packet member related
    rcases related with one | two
    · exact left.1 packet member one
    · exact right.1 packet member two

/-- Exact failure test after separate Joint witnesses: no simultaneous
assignment satisfies the union of branches and the new output equations. -/
theorem separate_joint_failure_iff (registry : Registry) (state : State roles)
    (first last : Site roles) (registered : first ∈ state.sites)
    (key : Nat) (left : Joint registry state first.occurrence key)
    (right : Joint registry state last.occurrence key) :
    ¬ Joint registry (merge state first last) first.occurrence key ↔
      ¬ Shared registry state first last key :=
  not_congr (separate_joint_merge_iff registry state first last registered key left right)

/-- A key conflict is a separate obstruction. It needs actual recorded
packets in the joined classes, not merely different unrecorded candidates. -/
theorem recorded_key_conflict (registry : Registry) (state : State roles)
    (first last : Site roles) (one two : Packet roles)
    (firstRecorded : one ∈ state.packets) (lastRecorded : two ∈ state.packets)
    (firstAlias : Alias state first.occurrence.identity one.site.occurrence.identity)
    (lastAlias : Alias state last.occurrence.identity two.site.occurrence.identity)
    (different : one.declaration.id ≠ two.declaration.id) :
    ∀ key, ¬ Joint registry (merge state first last) first.occurrence key := by
  intro key joint
  have a := joint.1 one firstRecorded
    ((GeneralDictionaryJointMerge.alias_merge_first_iff state first last _).mpr (Or.inl firstAlias))
  have b := joint.1 two lastRecorded
    ((GeneralDictionaryJointMerge.alias_merge_first_iff state first last _).mpr (Or.inr lastAlias))
  exact different (a.trans b.symm)
end Yulang.GeneralDictionaryJointMergeResidual
