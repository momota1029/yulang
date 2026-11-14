import Yulang.GeneralNominalCenteredPermutationSymmetry
import Yulang.GeneralNominalCenteredCanonicalTransport

set_option backward.isDefEq.respectTransparency false

/-! Reachable packet-free inputs carry a reversible simulation through every
centered constructor. Recorded commitment is the invariant needed for table growth. -/
namespace Yulang.GeneralNominalCenteredPermutationSimulation
open GeneralDeclarations GeneralSourceDictionaries GeneralRegistryReordering GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredPermutationRepresentation
open GeneralNominalCenteredCommitment
variable {roles : Roles.RoleDecls} {first last : Registry} {root : Occurrence roles}
variable {left right next : State roles}

def Related (first last : Registry) (left right : State roles) : Prop :=
  Corresponds first last left right ∧ RecordedCommitted left ∧ RecordedCommitted right

theorem related_symm (same : Related first last left right) : Related last first right left :=
  ⟨GeneralNominalCenteredPermutationSymmetry.corresponds_symm same.1,same.2.2,same.2.1⟩

theorem step_forward (order : Reorders first last) (roleEq : first.roles = roles)
    (same : Related first last left right) (step : Step first root left next) :
    ∃ other, Step last root right other ∧ Related first last next other := by
  rcases step_transport_or_install same.1 step with ⟨other,stepOther,correspondence⟩ |
      ⟨plan,support,generated,result,enabled,novel,guard⟩
  · exact ⟨other,stepOther,correspondence,recorded_at same.2.1 step.choose_spec.2,
      recorded_at same.2.2 stepOther.choose_spec.2⟩
  · obtain ⟨table,_,_,ledger⟩ := same.1
    obtain ⟨other,matched,rebased,enabledOther,novelOther,guardOther⟩ :=
      GeneralNominalCenteredPermutationInstallationGuard.counterpart_enabled ledger order roleEq enabled novel support guard
    have oneNew : plan.packet ∉ left.erased.current.packets := fun member => novel (same.2.1 _ member)
    have twoNew : other.packet ∉ right.erased.current.packets := fun member => novelOther (same.2.2 _ member)
    have generatedOther : GeneralNominalSaturationState.Generated right.erased.current root other.packet.site.occurrence := by
      rw [← matched.packet.site]
      exact (ledger.erased.current.generated root _).mp generated
    have stepOther : Step last root right (install right other support) :=
      ⟨other.packet.site.occurrence,generatedOther,.install other support enabledOther novelOther guardOther⟩
    refine ⟨install right other support,stepOther,?_,recorded_at same.2.1 step.choose_spec.2,
      recorded_at same.2.2 stepOther.choose_spec.2⟩
    rw [result]
    exact GeneralNominalCenteredPermutationExtension.installed_corresponds same.1 order roleEq matched rebased oneNew twoNew enabled enabledOther support

theorem step_backward (order : Reorders first last) (roleEq : first.roles = roles)
    (same : Related first last left right) (step : Step last root right next) :
    ∃ other, Step first root left other ∧ Related first last other next := by
  obtain ⟨other,step,related⟩ := step_forward (GeneralRegistryChildOrder.reorders_symm order)
    (order.2.1.symm.trans roleEq) (related_symm same) step
  exact ⟨other,step,related_symm related⟩

theorem observations (roleEq : last.roles = roles) (same : Related first last left right) (demand frontier) :
    GeneralNominalCenteredAdministrativeLocal.Local last left demand frontier ↔
      GeneralNominalCenteredAdministrativeLocal.Local last right demand frontier := by
  obtain ⟨_,_,_,ledger⟩ := same.1
  exact GeneralNominalCenteredPermutationObservations.local_iff ledger last roleEq demand frontier

theorem simulation (order : Reorders first last) (roleEq : first.roles = roles) (root : Occurrence roles) :
    GeneralNominalCenteredCanonicalTransport.Simulation first last root (Related first last) :=
  ⟨fun _ _ same _ step => step_forward order roleEq same step,
    fun _ _ same _ step => step_backward order roleEq same step,
    fun _ _ same => observations (order.2.1.symm.trans roleEq) same⟩

theorem reachable_permutation_simulation : GeneralNominalCenteredCanonicalTransport.ReachablePermutationSimulation roles := by
  intro registry checked state root reachable empty
  have recorded := recorded_reachable reachable
  refine ⟨Related registry (GeneralCanonicalRegistry.canonical registry),
    ⟨reachable_packet_free _ reachable empty,recorded,recorded⟩,?_⟩
  exact simulation (GeneralCanonicalRegistry.reorders_canonical registry) checked.1 root

theorem canonical_exit_lifting : GeneralNominalCenteredCanonicalExecutor.CanonicalExitLifting roles :=
  GeneralNominalCenteredCanonicalTransport.canonical_exit_lifting reachable_permutation_simulation

theorem canonicalLocalOrder : GeneralNominalCenteredCanonicalExecutor.CanonicalLocalOrder roles :=
  GeneralNominalCenteredCanonicalTransport.canonicalLocalOrder reachable_permutation_simulation

theorem bridges
    (evidenceNode : B4SkeletonV5.EvidenceNode (GeneralNominalCenteredAdministrativeLocal.boundary roles))
    (generatedChildren : B4SkeletonV5.GeneratedChildren (GeneralNominalCenteredAdministrativeLocal.boundary roles)) :
    B4SkeletonV5.B4Bridges (GeneralNominalCenteredAdministrativeLocal.boundary roles)
      (GeneralNominalCenteredCanonicalExecutor.executor roles)
      (GeneralNominalCenteredAdministrativeLocal.frontiers roles) :=
  GeneralNominalCenteredCanonicalExecutor.bridges ⟨canonical_exit_lifting,evidenceNode,generatedChildren⟩

theorem composition
    (evidenceNode : B4SkeletonV5.EvidenceNode (GeneralNominalCenteredAdministrativeLocal.boundary roles))
    (generatedChildren : B4SkeletonV5.GeneratedChildren (GeneralNominalCenteredAdministrativeLocal.boundary roles)) :
    B4TargetV5.Statement (GeneralNominalCenteredAdministrativeLocal.boundary roles)
      (GeneralNominalCenteredCanonicalExecutor.executor roles) :=
  GeneralNominalCenteredCanonicalTransport.composition reachable_permutation_simulation evidenceNode generatedChildren

end Yulang.GeneralNominalCenteredPermutationSimulation
