import Yulang.GeneralNominalSupportBoundary
import Yulang.GeneralNominalLocalReordering

/-! Permitted registry order changes preserve support readiness and the entire
independent local diagnostic at one fixed tracked snapshot. No agreement of
executor-returned states is asserted. -/
namespace Yulang.GeneralDictionarySupportLocalOrder
open GeneralDeclarations GeneralRegistryReordering GeneralSourceDictionaries
open CommonRoleOutermostResolver GeneralNominalCandidateReordering
variable {roles : Roles.RoleDecls} {first last : Registry}

theorem inspection (pair : DeclarationReorders a b) (state : GeneralNominalSupport.Tracked roles)
    (support : List (Occurrence roles))
    (bounds : List (GeneralNominalInspection.Bounds state.current.context.state)) :
    GeneralNominalSupport.Inspection state support a bounds ↔
      GeneralNominalSupport.Inspection state support b bounds := by
  simp only [GeneralNominalSupport.Inspection, GeneralNominalInspection.queries,
    Declaration.normalHead, pair.head]

theorem decision_guard_forward (order : Reorders first last)
    (state : GeneralNominalSupport.Tracked roles) (root : Occurrence roles) (support : List (Occurrence roles))
    (guard : GeneralNominalSupport.DecisionGuard state first root support) :
    GeneralNominalSupport.DecisionGuard state last root support := by
  refine ⟨guard.1,guard.2.1,?_⟩
  intro b visible role bounds located
  obtain ⟨a,present,pair⟩ := reorders_visible_back order b visible
  exact (inspection pair state support bounds).mp
    (guard.2.2 a present (pair.role.trans role) bounds located)

theorem decision_guard (order : Reorders first last)
    (state : GeneralNominalSupport.Tracked roles) (root : Occurrence roles) (support : List (Occurrence roles)) :
    GeneralNominalSupport.DecisionGuard state first root support ↔
      GeneralNominalSupport.DecisionGuard state last root support :=
  ⟨decision_guard_forward order state root support,
    decision_guard_forward (GeneralRegistryChildOrder.reorders_symm order) state root support⟩

theorem support_pending (order : Reorders first last)
    (state : GeneralNominalSupport.Tracked roles) (root : Occurrence roles) :
    GeneralNominalSupportBoundary.SupportPending first state root ↔
      GeneralNominalSupportBoundary.SupportPending last state root := by
  simp only [GeneralNominalSupportBoundary.SupportPending,decision_guard order state root]

private theorem safe (order : Reorders first last) (roleEq : first.roles = roles)
    (state : GeneralNominalSupport.Tracked roles) (root : Occurrence roles) :
    GeneralNominalLocalBoundary.SafeKnown (GeneralNominalSupportBoundary.fields roles) first state root ↔
      GeneralNominalLocalBoundary.SafeKnown (GeneralNominalSupportBoundary.fields roles) last state root := by
  change (¬ GeneralNominalState.RootPending state.current.context.state root.demand ∧
    ¬ GeneralNominalFeedbackK2.RootK2 state.current root ∧ ¬ GeneralNominalFeedbackK2.CandidateK2 first state.current root ∧
    ¬ (GeneralNominalCycleK2.InspectionPending first state.current.context root ∨ GeneralNominalSupportBoundary.SupportPending first state root)) ↔ _
  rw [feedback_candidateK2 order state.current root,cycle_inspection_pending order roleEq state.current.context root, support_pending order state root]
  rfl

private theorem rejection (order : Reorders first last) (roleEq : first.roles = roles)
    (state : GeneralNominalSupport.Tracked roles) (root : Occurrence roles) :
    GeneralNominalLocalBoundary.RejectReason (GeneralNominalSupportBoundary.fields roles) first state root ↔
      GeneralNominalLocalBoundary.RejectReason (GeneralNominalSupportBoundary.fields roles) last state root := by
  change (¬ GeneralNominalState.RootPending state.current.context.state root.demand ∧
    (GeneralNominalFeedbackK2.RootK2 state.current root ∨ GeneralNominalFeedbackK2.CandidateK2 first state.current root ∨
      (¬ (GeneralNominalCycleK2.InspectionPending first state.current.context root ∨ GeneralNominalSupportBoundary.SupportPending first state root) ∧
        ∀ key children, ¬ GeneralNominalRecursiveCandidates.Survivor first state.current.context root key children))) ↔ _
  simp only [feedback_candidateK2 order state.current root,cycle_inspection_pending order roleEq state.current.context root, support_pending order state root,
    survivor order roleEq state.current.context root]
  rfl

theorem local_forward (order : Reorders first last) (roleEq : first.roles = roles)
    (state : GeneralNominalSupport.Tracked roles) (root : Occurrence roles) (frontier : Frontier (Occurrence roles))
    (valid : GeneralNominalSupportBoundary.Local first state root frontier) :
    GeneralNominalSupportBoundary.Local last state root frontier := by
  refine GeneralNominalLocalBoundary.Local.rec
    (v := GeneralNominalSupportBoundary.vocabulary roles) (b := GeneralNominalSupportBoundary.fields roles)
    (r := first) (s := state)
    (motive := fun f _ => GeneralNominalSupportBoundary.Local last state root f) ?_ ?_ ?_ ?_ ?_ valid
  · intro pending
    exact .pending pending
  · intro ready pending rootClear candidateClear
    exact .inspectionPending ready ((or_congr (cycle_inspection_pending order roleEq state.current.context root) (support_pending order state root)).mp pending)
      rootClear (fun bad => candidateClear ((feedback_candidateK2 order state.current root).mpr bad))
  · intro reason
    exact .rejected ((rejection order roleEq state root).mp reason)
  · intro keyOne childrenOne keyTwo childrenTwo ready one two different
    exact .ambiguous ((safe order roleEq state root).mp ready)
      ((survivor order roleEq state.current.context root _ _).mp one)
      ((survivor order roleEq state.current.context root _ _).mp two) different
  · intro key children ready unique
    exact .selected ((safe order roleEq state root).mp ready)
      ⟨(survivor order roleEq state.current.context root _ _).mp unique.1,
        fun key children found => unique.2 key children ((survivor order roleEq state.current.context root key children).mpr found)⟩

theorem local_iff (order : Reorders first last) (roleEq : first.roles = roles)
    (state : GeneralNominalSupport.Tracked roles) (root : Occurrence roles) (frontier : Frontier (Occurrence roles)) :
    GeneralNominalSupportBoundary.Local first state root frontier ↔
      GeneralNominalSupportBoundary.Local last state root frontier :=
  ⟨local_forward order roleEq state root frontier,
    local_forward (GeneralRegistryChildOrder.reorders_symm order) (order.2.1.symm.trans roleEq) state root frontier⟩

theorem boundary_local (order : Reorders first last) (roleEq : first.roles = roles)
    (state : GeneralNominalSupport.Tracked roles) (root : Occurrence roles) (frontier : Frontier (Occurrence roles)) :
    B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary first state root frontier ↔
      B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary last state root frontier :=
  (GeneralNominalSupportBoundary.local_correspondence first state root frontier).trans
    ((local_iff order roleEq state root frontier).trans
      (GeneralNominalSupportBoundary.local_correspondence last state root frontier).symm)

/-- The complete diagnostic tree is preserved, including unsuccessful children. -/
theorem resolves (order : Reorders first last) (roleEq : first.roles = roles)
    (state : GeneralNominalSupport.Tracked roles) (root : Occurrence roles) (tree : Tree) :
    Resolves (B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary first state) root tree ↔
      Resolves (B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary last state) root tree :=
  ⟨B4Skeleton.resolves_transport (fun d f => (boundary_local order roleEq state d f).mp),
    B4Skeleton.resolves_transport (fun d f => (boundary_local order roleEq state d f).mpr)⟩

theorem child (order : Reorders first last) (roleEq : first.roles = roles)
    (state : GeneralNominalSupport.Tracked roles) (descendant parent : Occurrence roles) :
    Child (B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary first state) descendant parent ↔
      Child (B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary last state) descendant parent := by
  constructor
  · rintro ⟨key, children, selected, member⟩
    exact ⟨key, children, (boundary_local order roleEq state parent _).mp selected, member⟩
  · rintro ⟨key, children, selected, member⟩
    exact ⟨key, children, (boundary_local order roleEq state parent _).mpr selected, member⟩

/-- Order transport does not construct the required accessibility witness. -/
theorem whereAccessible_iff (order : Reorders first last) (roleEq : first.roles = roles)
    (state : GeneralNominalSupport.Tracked roles) (root : Occurrence roles) :
    Acc (Child (B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary first state)) root ↔
      Acc (Child (B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary last state)) root := by
  have same := funext (fun d => funext (fun p => propext (child order roleEq state d p)))
  rw [same]

/-- Exact four-way classification and selected payload at one shared state.
This preserves any classification that exists, not totality of classification. -/
theorem classify (order : Reorders first last) (roleEq : first.roles = roles)
    (state : GeneralNominalSupport.Tracked roles) (root : Occurrence roles) (outcome : Result) :
    B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary first state root outcome ↔
      B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary last state root outcome := by
  constructor
  · intro given
    obtain ⟨tree,resolved,completed⟩ := B4TargetV3.classify_tree
      (b := (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary) given
    exact B4TargetV3.tree_classifies (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
      last state tree root outcome ((resolves order roleEq state root tree).mp resolved) completed
  · intro given
    obtain ⟨tree,resolved,completed⟩ := B4TargetV3.classify_tree
      (b := (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary) given
    exact B4TargetV3.tree_classifies (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
      first state tree root outcome ((resolves order roleEq state root tree).mpr resolved) completed

end Yulang.GeneralDictionarySupportLocalOrder
