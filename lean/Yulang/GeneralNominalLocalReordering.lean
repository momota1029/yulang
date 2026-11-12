import Yulang.GeneralNominalCandidateReordering
import Yulang.GeneralDictionaryReachableObligations

/-! Exact independent Local invariance at a shared state. Canonical emission
already makes child lists literally equal. The V5 bridge additionally compares
two returned states; a separate theorem exposes that remaining executor premise. -/
namespace Yulang.GeneralNominalLocalReordering

open GeneralDeclarations GeneralRegistryReordering GeneralSourceDictionaries
open GeneralNominalSaturationState CommonRoleOutermostResolver
open GeneralNominalCandidateReordering

variable {roles : Roles.RoleDecls} {first last : Registry}

private theorem safe (order : Reorders first last) (roleEq : first.roles = roles)
    (state : State roles) (root : Occurrence roles) :
    GeneralNominalLocalBoundary.SafeKnown (GeneralNominalFeedbackK2.fields roles) first state root ↔
      GeneralNominalLocalBoundary.SafeKnown (GeneralNominalFeedbackK2.fields roles) last state root := by
  change (¬ GeneralNominalState.RootPending state.context.state root.demand ∧
    ¬ GeneralNominalFeedbackK2.RootK2 state root ∧ ¬ GeneralNominalFeedbackK2.CandidateK2 first state root ∧
    ¬ GeneralNominalCycleK2.InspectionPending first state.context root) ↔ _
  rw [feedback_candidateK2 order state root,cycle_inspection_pending order roleEq state.context root]
  rfl

private theorem rejection (order : Reorders first last) (roleEq : first.roles = roles)
    (state : State roles) (root : Occurrence roles) :
    GeneralNominalLocalBoundary.RejectReason (GeneralNominalFeedbackK2.fields roles) first state root ↔
      GeneralNominalLocalBoundary.RejectReason (GeneralNominalFeedbackK2.fields roles) last state root := by
  change (¬ GeneralNominalState.RootPending state.context.state root.demand ∧
    (GeneralNominalFeedbackK2.RootK2 state root ∨ GeneralNominalFeedbackK2.CandidateK2 first state root ∨
      (¬ GeneralNominalCycleK2.InspectionPending first state.context root ∧
        ∀ key children, ¬ GeneralNominalRecursiveCandidates.Survivor first state.context root key children))) ↔ _
  simp only [feedback_candidateK2 order state root,cycle_inspection_pending order roleEq state.context root,
    survivor order roleEq state.context root]
  rfl

theorem local_forward (order : Reorders first last) (roleEq : first.roles = roles)
    (state : State roles) (root : Occurrence roles) (frontier : Frontier (Occurrence roles))
    (valid : GeneralNominalFeedbackK2.Local first state root frontier) :
    GeneralNominalFeedbackK2.Local last state root frontier := by
  refine GeneralNominalLocalBoundary.Local.rec
    (v := GeneralNominalCycleBoundary.vocabulary roles) (b := GeneralNominalFeedbackK2.fields roles)
    (r := first) (s := state)
    (motive := fun f _ => GeneralNominalFeedbackK2.Local last state root f) ?_ ?_ ?_ ?_ ?_ valid
  · intro pending
    exact .pending pending
  · intro ready pending rootClear candidateClear
    exact .inspectionPending ready ((cycle_inspection_pending order roleEq state.context root).mp pending)
      rootClear (fun bad => candidateClear ((feedback_candidateK2 order state root).mpr bad))
  · intro reason
    exact .rejected ((rejection order roleEq state root).mp reason)
  · intro keyOne childrenOne keyTwo childrenTwo ready one two different
    exact .ambiguous ((safe order roleEq state root).mp ready)
      ((survivor order roleEq state.context root _ _).mp one)
      ((survivor order roleEq state.context root _ _).mp two) different
  · intro key children ready unique
    exact .selected ((safe order roleEq state root).mp ready)
      ⟨(survivor order roleEq state.context root _ _).mp unique.1,
        fun key children found => unique.2 key children ((survivor order roleEq state.context root key children).mpr found)⟩

theorem local_iff (order : Reorders first last) (roleEq : first.roles = roles)
    (state : State roles) (root : Occurrence roles) (frontier : Frontier (Occurrence roles)) :
    GeneralNominalFeedbackK2.Local first state root frontier ↔
      GeneralNominalFeedbackK2.Local last state root frontier :=
  ⟨local_forward order roleEq state root frontier,
    local_forward (GeneralRegistryChildOrder.reorders_symm order) (order.2.1.symm.trans roleEq) state root frontier⟩

theorem boundary_local (order : Reorders first last) (roleEq : first.roles = roles)
    (state : State roles) (root : Occurrence roles) (frontier : Frontier (Occurrence roles)) :
    B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles) first state root frontier ↔
      B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles) last state root frontier :=
  (GeneralNominalFeedbackBoundary.local_correspondence roles (GeneralDictionaryFeedbackEvidence.evidence roles)
    first state root frontier).trans ((local_iff order roleEq state root frontier).trans
      (GeneralNominalFeedbackBoundary.local_correspondence roles (GeneralDictionaryFeedbackEvidence.evidence roles)
        last state root frontier).symm)

/-- The complete diagnostic tree is preserved, including unsuccessful children. -/
theorem resolves (order : Reorders first last) (roleEq : first.roles = roles)
    (state : State roles) (root : Occurrence roles) (tree : Tree) :
    Resolves (B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles) first state) root tree ↔
      Resolves (B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles) last state) root tree :=
  ⟨B4Skeleton.resolves_transport (fun d f => (boundary_local order roleEq state d f).mp),
    B4Skeleton.resolves_transport (fun d f => (boundary_local order roleEq state d f).mpr)⟩

theorem child (order : Reorders first last) (roleEq : first.roles = roles)
    (state : State roles) (descendant parent : Occurrence roles) :
    Child (B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles) first state) descendant parent ↔
      Child (B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles) last state) descendant parent := by
  constructor
  · rintro ⟨key, children, selected, member⟩
    exact ⟨key, children, (boundary_local order roleEq state parent _).mp selected, member⟩
  · rintro ⟨key, children, selected, member⟩
    exact ⟨key, children, (boundary_local order roleEq state parent _).mpr selected, member⟩

/-- Order transport does not construct the required accessibility witness. -/
theorem whereAccessible_iff (order : Reorders first last) (roleEq : first.roles = roles)
    (state : State roles) (root : Occurrence roles) :
    Acc (Child (B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles) first state)) root ↔
      Acc (Child (B4TargetV3.Local (GeneralDictionaryFeedbackEvidence.boundary roles) last state)) root := by
  have same := funext (fun d => funext (fun p => propext (child order roleEq state d p)))
  rw [same]

/-- This is the shared-snapshot order law, with precisely V5's input domain.
The stronger theorem above needs neither reachability nor a final-state driver. -/
theorem reachable_local_order (roles : Roles.RoleDecls) :
    ∀ first last, (GeneralDictionaryReachableBoundary.boundary roles).Checked first →
      (GeneralDictionaryReachableBoundary.boundary roles).Checked last →
      (GeneralDictionaryReachableBoundary.boundary roles).Reorders first last →
      ∀ state root, B4TargetV5.Reachable (GeneralDictionaryReachableBoundary.boundary roles) first root state →
      B4TargetV5.Reachable (GeneralDictionaryReachableBoundary.boundary roles) last root state → ∀ demand frontier,
      B4TargetV3.Local (GeneralDictionaryReachableBoundary.boundary roles).toSourceBoundary first state demand frontier ↔
        B4TargetV3.Local (GeneralDictionaryReachableBoundary.boundary roles).toSourceBoundary last state demand frontier := by
  intro first last checked _ order state _ _ _ demand frontier
  exact boundary_local order checked.1 state demand frontier

/-- Exact final-state field, conditional on equality of the returned states.
No claim that reordering the inputs proves this executor property is made. -/
theorem canonicalLocalOrder_of_returned_state_equality (roles : Roles.RoleDecls)
    (executor : B4TargetV3.Executor (GeneralNominalFeedbackBoundary.vocabulary roles))
    (same : ∀ first last, (GeneralDictionaryReachableBoundary.boundary roles).Checked first →
      (GeneralDictionaryReachableBoundary.boundary roles).Checked last →
      (GeneralDictionaryReachableBoundary.boundary roles).Reorders first last →
      ∀ state root, B4TargetV5.Reachable (GeneralDictionaryReachableBoundary.boundary roles) first root state →
      B4TargetV5.Reachable (GeneralDictionaryReachableBoundary.boundary roles) last root state →
      (executor.run first state root).1 = (executor.run last state root).1) :
    ∀ first last, (GeneralDictionaryReachableBoundary.boundary roles).Checked first →
      (GeneralDictionaryReachableBoundary.boundary roles).Checked last →
      (GeneralDictionaryReachableBoundary.boundary roles).Reorders first last →
      ∀ state root, B4TargetV5.Reachable (GeneralDictionaryReachableBoundary.boundary roles) first root state →
      B4TargetV5.Reachable (GeneralDictionaryReachableBoundary.boundary roles) last root state → ∀ demand frontier,
      B4TargetV3.Local (GeneralDictionaryReachableBoundary.boundary roles).toSourceBoundary
        first (executor.run first state root).1 demand frontier ↔
      B4TargetV3.Local (GeneralDictionaryReachableBoundary.boundary roles).toSourceBoundary
        last (executor.run last state root).1 demand frontier := by
  intro first last checked checkedLast order state root reached reachedLast demand frontier
  rw [same first last checked checkedLast order state root reached reachedLast]
  exact boundary_local order checked.1 _ demand frontier

/-- Reachability supplies source formation but has not supplied Readback.
The premise here is the existing general cycle readback, not a replacement. -/
theorem whereAccessible_of_readback (roles : Roles.RoleDecls)
    (registry : Registry) (checked : (GeneralDictionaryReachableBoundary.boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (_reachable : B4TargetV5.Reachable (GeneralDictionaryReachableBoundary.boundary roles) registry root state)
    (readback : GeneralNominalCycleReadback.Readback roles registry state.context) :
    Acc (Child (B4TargetV3.Local (GeneralDictionaryReachableBoundary.boundary roles).toSourceBoundary registry state)) root :=
  GeneralNominalFeedbackBoundary.whereAccessible_of_readback roles (GeneralDictionaryFeedbackEvidence.evidence roles)
    registry checked state readback root

end Yulang.GeneralNominalLocalReordering
