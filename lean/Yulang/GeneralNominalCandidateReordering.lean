import Yulang.GeneralNominalRegistryOrder

/-! All candidate-side predicates are invariant under the permitted registry
reordering in one fixed general context. Exact canonical children, failed
branches, unresolved inspection, and both cycle rules are retained. -/
namespace Yulang.GeneralNominalCandidateReordering

open GeneralDeclarations GeneralRegistryReordering GeneralSourceDictionaries
open GeneralNominalRecursiveCandidates
open GeneralDictionaryRecursiveOrder (report_reorders)

variable {roles : Roles.RoleDecls} {first last : Registry}

theorem checked_declaration (order : Reorders first last) (pair : DeclarationReorders a b)
    (valid : DeclarationChecked first.constructors roles a) : DeclarationChecked last.constructors roles b :=
  order.1 ▸ (declarationReorders_checked pair).mp valid

theorem survivor_forward (order : Reorders first last) (roleEq : first.roles = roles)
    (context : Context) (root : Occurrence roles) (key : Nat) (emitted : List (Occurrence roles))
    (valid : Survivor first context root key emitted) : Survivor last context root key emitted := by
  obtain ⟨ready,a,visible,ac,identity,role,bounds,located,prepared,emission⟩ := valid
  obtain ⟨b,present,pair⟩ := reorders_visible order a visible
  let bc := checked_declaration order pair ac
  refine ⟨ready,b,present,bc,pair.id.symm.trans identity,pair.role.symm.trans role,bounds,located,
    (GeneralNominalRegistryOrder.prepared order roleEq pair context root ac bc).mp prepared,?_⟩
  rw [emission,report_reorders context a b pair bounds]
  exact GeneralNominalRegistryOrder.children order pair context.state root ac bc _

theorem survivor (order : Reorders first last) (roleEq : first.roles = roles)
    (context : Context) (root : Occurrence roles) (key : Nat) (emitted : List (Occurrence roles)) :
    Survivor first context root key emitted ↔ Survivor last context root key emitted :=
  ⟨survivor_forward order roleEq context root key emitted,
    survivor_forward (GeneralRegistryChildOrder.reorders_symm order) (order.2.1.symm.trans roleEq) context root key emitted⟩

theorem inspection_pending_forward (order : Reorders first last) (roleEq : first.roles = roles)
    (context : Context) (root : Occurrence roles) (valid : InspectionPending first context root) :
    InspectionPending last context root := by
  obtain ⟨ready,a,visible,ac,role,notFailed,notPrepared⟩ := valid
  obtain ⟨b,present,pair⟩ := reorders_visible order a visible
  let bc := checked_declaration order pair ac
  exact ⟨ready,b,present,bc,pair.role.symm.trans role,
    fun failed => notFailed ((GeneralNominalRegistryOrder.failed order roleEq pair context root ac bc).mpr failed),
    fun prepared => notPrepared ((GeneralNominalRegistryOrder.prepared order roleEq pair context root ac bc).mpr prepared)⟩

theorem inspection_pending (order : Reorders first last) (roleEq : first.roles = roles)
    (context : Context) (root : Occurrence roles) :
    InspectionPending first context root ↔ InspectionPending last context root :=
  ⟨inspection_pending_forward order roleEq context root,
    inspection_pending_forward (GeneralRegistryChildOrder.reorders_symm order) (order.2.1.symm.trans roleEq) context root⟩

/-- Inspecting a position is transported independently of the cycle predicate
that will be tested there. The report and inspected source slots are identical. -/
theorem inspection_witness (order : Reorders first last)
    (context : Context) (root : Occurrence roles)
    (property : GeneralNominalInspection.Bounds context.state → Prop) :
    (∃ a ∈ first.declarations, ∃ _ac : DeclarationChecked first.constructors roles a,
      a.role = root.demand.role ∧ HeadReady first context root a ∧
      ∃ bounds, arguments context root = some bounds ∧
        ∃ visited ∈ (report context a bounds).inspected, property visited) ↔
    (∃ b ∈ last.declarations, ∃ _bc : DeclarationChecked last.constructors roles b,
      b.role = root.demand.role ∧ HeadReady last context root b ∧
      ∃ bounds, arguments context root = some bounds ∧
        ∃ visited ∈ (report context b bounds).inspected, property visited) := by
  constructor
  · rintro ⟨a,visible,ac,role,ready,bounds,located,visited,member,valid⟩
    obtain ⟨b,present,pair⟩ := reorders_visible order a visible
    refine ⟨b,present,checked_declaration order pair ac,pair.role.symm.trans role,
      (GeneralNominalRegistryOrder.head_ready order pair context root).mp ready,bounds,located,visited,?_,valid⟩
    rwa [← report_reorders context a b pair bounds]
  · rintro ⟨b,visible,bc,role,ready,bounds,located,visited,member,valid⟩
    obtain ⟨a,present,pair⟩ := reorders_visible_back order b visible
    refine ⟨a,present,checked_declaration (GeneralRegistryChildOrder.reorders_symm order)
      (declarationReorders_symm pair) bc,pair.role.trans role,
      (GeneralNominalRegistryOrder.head_ready order pair context root).mpr ready,bounds,located,visited,?_,valid⟩
    rwa [report_reorders context a b pair bounds]

theorem recursive_candidateK2 (order : Reorders first last) (context : Context) (root : Occurrence roles) :
    GeneralNominalRecursiveCandidates.CandidateK2 first context root ↔
      GeneralNominalRecursiveCandidates.CandidateK2 last context root :=
  and_congr_right (fun _ => inspection_witness order context root _)

theorem cycle_candidateK2 (order : Reorders first last) (context : Context) (root : Occurrence roles) :
    GeneralNominalCycleK2.CandidateK2 first context root ↔ GeneralNominalCycleK2.CandidateK2 last context root :=
  and_congr_right (fun _ => inspection_witness order context root _)

theorem cycle_inspection_pending (order : Reorders first last) (roleEq : first.roles = roles)
    (context : Context) (root : Occurrence roles) :
    GeneralNominalCycleK2.InspectionPending first context root ↔
      GeneralNominalCycleK2.InspectionPending last context root := by
  simp only [GeneralNominalCycleK2.InspectionPending,inspection_pending order roleEq context root,
    recursive_candidateK2 order context root,cycle_candidateK2 order context root]

theorem feedback_candidateK2 (order : Reorders first last)
    (state : GeneralNominalSaturationState.State roles) (root : Occurrence roles) :
    GeneralNominalFeedbackK2.CandidateK2 first state root ↔ GeneralNominalFeedbackK2.CandidateK2 last state root := by
  unfold GeneralNominalFeedbackK2.CandidateK2
  exact or_congr (cycle_candidateK2 order state.context root)
    (and_congr_right (fun _ => inspection_witness order state.context root _))

end Yulang.GeneralNominalCandidateReordering
