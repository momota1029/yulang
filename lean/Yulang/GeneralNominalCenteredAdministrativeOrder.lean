import Yulang.GeneralNominalCenteredAdministrativeWhere
import Yulang.GeneralNominalCandidateReordering

/-! Declaration and clause permutations preserve centered diagnostics at a
fixed snapshot, including actual-position cycles and required merge closure. -/
namespace Yulang.GeneralNominalCenteredAdministrativeOrder
open GeneralDeclarations GeneralRegistryReordering GeneralSourceDictionaries
open GeneralNominalCenteredSteps GeneralNominalCenters
open GeneralNominalCenteredAdministrativeLocal

variable {roles : Roles.RoleDecls} {first last : Registry}

theorem decision_forward (order : Reorders first last) (state : State roles) (root : Occurrence roles)
    (guard : DecisionGuard first state root) : DecisionGuard last state root := by
  refine ⟨guard.1,?_⟩
  intro declaration member role bounds located slot visited
  obtain ⟨other,present,pair⟩ := reorders_visible_back order declaration member
  apply guard.2 other present (pair.role.trans role) bounds located slot
  simpa only [GeneralNominalInspection.queries,Declaration.normalHead,pair.head] using visited

theorem decision_iff (order : Reorders first last) (state : State roles) (root : Occurrence roles) :
    DecisionGuard first state root ↔ DecisionGuard last state root :=
  ⟨decision_forward order state root,decision_forward (GeneralRegistryChildOrder.reorders_symm order) state root⟩

theorem candidate_cycle_forward (order : Reorders first last) (state : State roles) (root : Occurrence roles)
    (cycle : CandidateCycle first state root) : CandidateCycle last state root := by
  obtain ⟨plan,recorded,input,registryEq,contextEq,visible,role,ready,located,entry,member,cyclic⟩ := cycle
  obtain ⟨other,present,pair⟩ := reorders_visible order plan.packet.declaration visible
  have checked : DeclarationChecked first.constructors roles plan.packet.declaration := registryEq ▸ plan.packet.checked
  let packet : GeneralNominalSaturationState.Packet roles :=
    ⟨last,plan.packet.context,plan.packet.site,other,
      GeneralNominalCandidateReordering.checked_declaration order pair checked,plan.packet.bounds⟩
  let next : Plan roles := ⟨packet,plan.input,plan.input_exact⟩
  refine ⟨next,recorded,input,rfl,contextEq,present,pair.role.symm.trans role,
    (GeneralNominalRegistryOrder.head_ready order pair plan.packet.context root).mp ready,
    located,entry,?_,cyclic⟩
  simpa only [inspection,next,packet,GeneralNominalInspection.queries,Declaration.normalHead,pair.head] using member

theorem candidate_cycle_iff (order : Reorders first last) (state : State roles) (root : Occurrence roles) :
    CandidateCycle first state root ↔ CandidateCycle last state root :=
  ⟨candidate_cycle_forward order state root,
    candidate_cycle_forward (GeneralRegistryChildOrder.reorders_symm order) state root⟩

theorem local_iff (order : Reorders first last) (roleEq : first.roles = roles)
    (state : State roles) (root : Occurrence roles) (frontier) :
    Local first state root frontier ↔ Local last state root frontier := by
  apply GeneralLocalPredicateCongruence.local_iff (first := fields roles) (last := fields roles)
    (r₁ := first) (r₂ := last) Iff.rfl Iff.rfl ?_ ?_ ?_ frontier
  · exact or_congr (GeneralNominalCandidateReordering.feedback_candidateK2 order state.erased.current root)
      (candidate_cycle_iff order state root)
  · exact or_congr
      (or_congr (GeneralNominalCandidateReordering.cycle_inspection_pending order roleEq state.erased.current.context root)
        (not_congr (decision_iff order state root))) Iff.rfl
  · exact GeneralNominalCandidateReordering.survivor order roleEq state.erased.current.context root

theorem boundary_local_iff (order : Reorders first last) (roleEq : first.roles = roles)
    (state : State roles) (root : Occurrence roles) (frontier) :
    B4TargetV3.Local (boundary roles).toSourceBoundary first state root frontier ↔
      B4TargetV3.Local (boundary roles).toSourceBoundary last state root frontier :=
  (local_correspondence first state root frontier).trans
    ((local_iff order roleEq state root frontier).trans (local_correspondence last state root frontier).symm)

end Yulang.GeneralNominalCenteredAdministrativeOrder
