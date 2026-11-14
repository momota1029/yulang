import Yulang.GeneralNominalCenteredClassLocalBoundary

set_option backward.isDefEq.respectTransparency false

/-! Registry and journal transport include all branches of the alias class. -/
namespace Yulang.GeneralNominalCenteredClassLocalOrder
open GeneralDeclarations GeneralSourceDictionaries GeneralRegistryReordering GeneralNominalCenteredSteps
open GeneralNominalCenteredClassLocalBoundary
variable {roles : Roles.RoleDecls} {first last : Registry}

theorem local_iff (order : Reorders first last) (roleEq : first.roles = roles)
    (state : State roles) (root : Occurrence roles) (frontier) :
    Local first state root frontier ↔ Local last state root frontier := by
  apply GeneralLocalPredicateCongruence.local_iff (first := fields roles) (last := fields roles)
    (r₁ := first) (r₂ := last) Iff.rfl Iff.rfl ?_ ?_ ?_ frontier
  · exact or_congr (GeneralNominalCandidateReordering.feedback_candidateK2 order state.erased.current root)
      (GeneralNominalCenteredAdministrativeOrder.candidate_cycle_iff order state root)
  · exact or_congr
      (or_congr (GeneralNominalCandidateReordering.cycle_inspection_pending order roleEq state.erased.current.context root)
        (not_congr (GeneralNominalCenteredAdministrativeOrder.decision_iff order state root))) Iff.rfl
  · intro key children
    exact and_congr (GeneralNominalCandidateReordering.survivor order roleEq state.erased.current.context root key children)
      (GeneralDictionaryJointReordering.joint order roleEq state.erased.current root key)

variable {relation : GeneralNominalSaturationState.Packet roles → GeneralNominalSaturationState.Packet roles → Prop}
variable {left right : State roles}
open GeneralNominalCenteredLedgerPermutation

theorem paired_local_iff (same : Related relation left right) (registry : Registry) (roleEq : registry.roles = roles)
    (root : Occurrence roles) (frontier) :
    Local registry left root frontier ↔
      Local registry right root frontier := by
  apply GeneralLocalPredicateCongruence.local_iff
    (first := fields roles)
    (last := fields roles)
    (GeneralNominalMetadataEquivalence.pending same.erased.current.context.state root.demand) ?_ ?_ ?_ ?_ frontier
  · exact or_congr (GeneralNominalCenteredPermutationApplicability.feedback_root same.erased.current root)
      (GeneralNominalCenteredPermutationSafety.root_cycle same root)
  · exact or_congr (GeneralNominalCenteredPermutationApplicability.feedback_candidate same.erased.current registry root)
      (GeneralNominalCenteredPermutationObservations.candidate same (GeneralRegistryReordering.reorders_refl registry) roleEq root)
  · exact or_congr (or_congr (GeneralNominalCenteredPermutationApplicability.inspection_pending same.erased.current.context registry root)
      (not_congr (GeneralNominalCenteredPermutationGuards.centered_decision same
        (GeneralRegistryReordering.reorders_refl registry) root))) (not_congr (GeneralNominalCenteredPermutationObservations.administrative_ready same root))
  · intro key children
    exact and_congr (GeneralNominalCenteredPermutationApplicability.survivor same.erased.current.context registry root key children)
      (GeneralNominalCenteredPermutationApplicability.joint same.erased.current registry root key)

theorem observations (roleEq : last.roles = roles)
    (same : GeneralNominalCenteredPermutationSimulation.Related first last left right) (demand frontier) :
    Local last left demand frontier ↔ Local last right demand frontier := by
  obtain ⟨_,_,_,ledger⟩ := same.1
  exact paired_local_iff ledger last roleEq demand frontier

end Yulang.GeneralNominalCenteredClassLocalOrder
