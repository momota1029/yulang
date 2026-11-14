import Yulang.GeneralNominalCenteredPermutationGuards

set_option backward.isDefEq.respectTransparency false

/-! Actual inspected cycles and the universal alternative guard quantify over
all current-context plans. They use the total counterpart construction. -/
namespace Yulang.GeneralNominalCenteredPermutationObservations
open GeneralDeclarations GeneralSourceDictionaries GeneralRegistryReordering GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredLedgerPermutation
open GeneralNominalCenteredPermutationCounterparts
variable {roles : Roles.RoleDecls}
variable {relation : GeneralNominalSaturationState.Packet roles → GeneralNominalSaturationState.Packet roles → Prop}
variable {left right : State roles} {r s : Registry}

theorem alternatives_forward (same : Related relation left right) (order : Reorders r s) (roleEq : r.roles = roles)
    (input : Site roles) (valid : AlternativesSafe r left input) : AlternativesSafe s right input := by
  intro plan inputEq registryEq contextEq visible role ready located
  have backOrder : Reorders plan.packet.registry r := registryEq ▸ GeneralRegistryChildOrder.reorders_symm order
  have backRoles : plan.packet.registry.roles = roles := registryEq ▸ order.2.1.symm.trans roleEq
  obtain ⟨other,oldRegistry,oldContext,oldVisible,matched,_⟩ := counterpart plan backOrder backRoles
    same.erased.current.context.symm contextEq (registryEq ▸ visible)
  have otherInput : other.input = input := matched.input.symm.trans inputEq
  have otherRole : other.packet.declaration.role = input.occurrence.demand.role := matched.declaration.role.symm.trans role
  have oldReady : GeneralNominalRecursiveCandidates.HeadReady r left.erased.current.context input.occurrence other.packet.declaration := by
    have before : GeneralNominalRecursiveCandidates.HeadReady plan.packet.registry plan.packet.context input.occurrence plan.packet.declaration := by
      simpa only [registryEq,contextEq] using ready
    simpa only [oldRegistry,oldContext] using (matched.ready input.occurrence).mp before
  have siteEq : plan.packet.site.occurrence = input.occurrence := plan.input_exact.symm.trans (congrArg Site.occurrence inputEq)
  have otherSite : other.packet.site.occurrence = input.occurrence := (congrArg GeneralNominalDemandMerging.Site.occurrence matched.packet.site).symm.trans siteEq
  have oldLocated : GeneralNominalRecursiveCandidates.arguments other.packet.context input.occurrence = some other.packet.bounds := by
    have before : GeneralNominalRecursiveCandidates.arguments plan.packet.context plan.packet.site.occurrence = some plan.packet.bounds := siteEq ▸ located
    simpa only [otherSite] using matched.located.mp before
  exact (safe (GeneralNominalCenteredPermutationSafety.symm same) matched).mpr
    (valid other otherInput oldRegistry oldContext oldVisible otherRole oldReady oldLocated)

theorem alternatives (same : Related relation left right) (order : Reorders r s) (roleEq : r.roles = roles)
    (input : Site roles) : AlternativesSafe r left input ↔ AlternativesSafe s right input :=
  ⟨alternatives_forward same order roleEq input,
    alternatives_forward (GeneralNominalCenteredPermutationSafety.symm same)
      (GeneralRegistryChildOrder.reorders_symm order) (order.2.1.symm.trans roleEq) input⟩

theorem candidate_forward (same : Related relation left right) (order : Reorders r s) (roleEq : r.roles = roles)
    (root : Occurrence roles) (valid : CandidateCycle r left root) : CandidateCycle s right root := by
  obtain ⟨plan,member,inputEq,registryEq,contextEq,visible,role,ready,located,entry,test,cyclic⟩ := valid
  have nextOrder : Reorders plan.packet.registry s := registryEq ▸ order
  have nextRoles : plan.packet.registry.roles = roles := registryEq ▸ roleEq
  obtain ⟨other,nextRegistry,nextContext,nextVisible,matched,_⟩ := counterpart plan nextOrder nextRoles
    same.erased.current.context contextEq (registryEq ▸ visible)
  have otherInput : other.input.occurrence = root := (congrArg Site.occurrence matched.input).symm.trans inputEq
  have otherRole : other.packet.declaration.role = root.demand.role := matched.declaration.role.symm.trans role
  have nextReady : GeneralNominalRecursiveCandidates.HeadReady s other.packet.context root other.packet.declaration := by
    have before : GeneralNominalRecursiveCandidates.HeadReady plan.packet.registry plan.packet.context root plan.packet.declaration := registryEq ▸ ready
    simpa only [nextRegistry] using (matched.ready root).mp before
  have siteEq : plan.packet.site.occurrence = root := plan.input_exact.symm.trans inputEq
  have otherSite : other.packet.site.occurrence = root := (congrArg GeneralNominalDemandMerging.Site.occurrence matched.packet.site).symm.trans siteEq
  have nextLocated : GeneralNominalRecursiveCandidates.arguments other.packet.context root = some other.packet.bounds := by
    have before : GeneralNominalRecursiveCandidates.arguments plan.packet.context plan.packet.site.occurrence = some plan.packet.bounds := siteEq ▸ located
    simpa only [otherSite] using matched.located.mp before
  exact ⟨other,(matched.input ▸ (same.sites plan.input).mp member),otherInput,nextRegistry,nextContext,nextVisible,
    otherRole,nextReady,nextLocated,entry,matched.tests ▸ test,(GeneralNominalCenteredPermutationSafety.cyclic same _).mp cyclic⟩

theorem candidate (same : Related relation left right) (order : Reorders r s) (roleEq : r.roles = roles)
    (root : Occurrence roles) : CandidateCycle r left root ↔ CandidateCycle s right root :=
  ⟨candidate_forward same order roleEq root,
    candidate_forward (GeneralNominalCenteredPermutationSafety.symm same)
      (GeneralRegistryChildOrder.reorders_symm order) (order.2.1.symm.trans roleEq) root⟩

theorem administrative_ready (same : Related relation left right) (root : Occurrence roles) :
    GeneralNominalCenteredAdministrativeLocal.AdministrativeReady left root ↔
      GeneralNominalCenteredAdministrativeLocal.AdministrativeReady right root := by
  have models := funext (fun model => propext (same.models model))
  simp only [GeneralNominalCenteredAdministrativeLocal.AdministrativeReady,
    GeneralNominalCenteredAdministrativeLocal.Registered,GeneralNominalCenteredAdministrativeLocal.RawMergesClosed,
    GeneralNominalCenteredAdministrativeLocal.CenterMergesClosed,same.sites,same.erased.current.sites,
    GeneralNominalCenteredPermutationInstallable.feedback_merges same.erased.current,models,same.erased.current.alias]

theorem local_iff (same : Related relation left right) (registry : Registry) (roleEq : registry.roles = roles)
    (root : Occurrence roles) (frontier) :
    GeneralNominalCenteredAdministrativeLocal.Local registry left root frontier ↔
      GeneralNominalCenteredAdministrativeLocal.Local registry right root frontier := by
  apply GeneralLocalPredicateCongruence.local_iff
    (first := GeneralNominalCenteredAdministrativeLocal.fields roles)
    (last := GeneralNominalCenteredAdministrativeLocal.fields roles)
    (GeneralNominalMetadataEquivalence.pending same.erased.current.context.state root.demand) ?_ ?_ ?_ ?_ frontier
  · exact or_congr (GeneralNominalCenteredPermutationApplicability.feedback_root same.erased.current root)
      (GeneralNominalCenteredPermutationSafety.root_cycle same root)
  · exact or_congr (GeneralNominalCenteredPermutationApplicability.feedback_candidate same.erased.current registry root)
      (candidate same (GeneralRegistryReordering.reorders_refl registry) roleEq root)
  · exact or_congr (or_congr (GeneralNominalCenteredPermutationApplicability.inspection_pending same.erased.current.context registry root)
      (not_congr (GeneralNominalCenteredPermutationGuards.centered_decision same
        (GeneralRegistryReordering.reorders_refl registry) root))) (not_congr (administrative_ready same root))
  · exact GeneralNominalCenteredPermutationApplicability.survivor same.erased.current.context registry root

end Yulang.GeneralNominalCenteredPermutationObservations
