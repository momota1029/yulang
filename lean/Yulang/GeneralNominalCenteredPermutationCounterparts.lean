import Yulang.GeneralNominalCenteredPermutationSafety
import Yulang.GeneralDictionaryJointReordering

set_option backward.isDefEq.respectTransparency false

/-! Every hypothetical plan over a visible declaration has a counterpart over
the paired current context. This construction also covers unrecorded alternatives. -/
namespace Yulang.GeneralNominalCenteredPermutationCounterparts
open GeneralDeclarations GeneralSourceDictionaries GeneralRegistryReordering GeneralNominalCenters
open GeneralNominalCenteredPermutationRepresentation
open GeneralNominalCenteredLedgerPermutation
variable {roles : Roles.RoleDecls}

structure Match (first last : Plan roles) : Prop where
  packet : GeneralNominalLedgerPermutation.PacketObservation first.packet last.packet
  input : first.input = last.input
  declaration : DeclarationReorders first.packet.declaration last.packet.declaration
  plans : PlanPair (fun _ _ => True) first last
  located : GeneralNominalRecursiveCandidates.arguments first.packet.context first.packet.site.occurrence = some first.packet.bounds ↔
    GeneralNominalRecursiveCandidates.arguments last.packet.context last.packet.site.occurrence = some last.packet.bounds
  prepared : GeneralNominalRecursiveCandidates.Prepared first.packet.registry first.packet.context first.packet.site.occurrence first.packet.declaration first.packet.checked ↔
    GeneralNominalRecursiveCandidates.Prepared last.packet.registry last.packet.context last.packet.site.occurrence last.packet.declaration last.packet.checked
  ready : ∀ root : Occurrence roles, GeneralNominalRecursiveCandidates.HeadReady first.packet.registry first.packet.context root first.packet.declaration ↔
    GeneralNominalRecursiveCandidates.HeadReady last.packet.registry last.packet.context root last.packet.declaration
  inspected : (GeneralNominalCenteredSteps.inspection first).inspected.length = (GeneralNominalCenteredSteps.inspection last).inspected.length
  tests : (GeneralNominalCenteredSteps.inspection first).tests = (GeneralNominalCenteredSteps.inspection last).tests

variable (plan : Plan roles) {registry : Registry} {decl : Declaration}
variable (order : Reorders plan.packet.registry registry) (roleEq : plan.packet.registry.roles = roles)
variable (pair : DeclarationReorders plan.packet.declaration decl)
variable (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)
variable (keys : ∀ key, key ∈ allocated ↔ key ∈ plan.packet.context.state.allocated)
variable (names : ∀ name, name ∈ reserved ↔ name ∈ plan.packet.context.state.reserved)

def rebase : Plan roles :=
  GeneralNominalCenteredPermutationPlans.metadata (GeneralNominalCenteredPlanReordering.rebase plan order pair) allocated reserved

include roleEq keys names

omit roleEq in
theorem rebased : RebasedPacket plan.packet.registry registry plan.packet (rebase plan order pair allocated reserved).packet :=
  ⟨rfl,decl,order,pair,allocated,reserved,keys,names,rfl⟩

theorem matched : Match plan (rebase plan order pair allocated reserved) := by
  have ctx : GeneralNominalMetadataEquivalence.Same plan.packet.context.state
      (GeneralNominalMetadataEquivalence.replace plan.packet.context.state allocated reserved) :=
    ⟨allocated,reserved,rfl,keys,names⟩
  have one := GeneralNominalCenteredPlanLedgerReordering.paired (relation := fun _ _ => True) order pair roleEq trivial
  have two := GeneralNominalCenteredPermutationPlans.paired (GeneralNominalCenteredPlanReordering.rebase plan order pair)
    allocated reserved (relation := fun _ _ => True) trivial
  refine ⟨packet_observation (rebased plan order pair allocated reserved keys names) roleEq,rfl,pair,
    ⟨trivial,rfl,fun m => (one.inputs m).trans (two.inputs m),fun m => (one.outputs m).trans (two.outputs m),
      fun m => (one.equations m).trans (two.equations m),fun e => (one.tests e).trans (two.tests e)⟩,Iff.rfl,?_,?_,?_,?_⟩
  · exact (GeneralNominalRegistryOrder.prepared order roleEq pair plan.packet.context plan.packet.site.occurrence
      plan.packet.checked (GeneralNominalCandidateReordering.checked_declaration order pair plan.packet.checked)).trans
      (GeneralNominalCenteredPermutationContext.prepared plan.packet.context allocated reserved ctx registry
        plan.packet.site.occurrence decl _).symm
  · intro root
    exact (GeneralNominalRegistryOrder.head_ready order pair plan.packet.context root).trans
      (GeneralNominalCenteredPermutationContext.head_ready plan.packet.context allocated reserved ctx registry root decl).symm
  · change _ = (GeneralNominalCenteredSteps.inspection
      (GeneralNominalCenteredPermutationPlans.metadata _ allocated reserved)).inspected.length
    rw [GeneralNominalCenteredPermutationPlans.inspection]
    change _ = (GeneralNominalCenteredSteps.inspection (GeneralNominalCenteredPlanReordering.rebase plan order pair)).inspected.length
    rw [GeneralNominalCenteredPlanReordering.inspection]
  · change _ = (GeneralNominalCenteredSteps.inspection
      (GeneralNominalCenteredPermutationPlans.metadata _ allocated reserved)).tests
    rw [GeneralNominalCenteredPermutationPlans.inspection]
    change _ = (GeneralNominalCenteredSteps.inspection (GeneralNominalCenteredPlanReordering.rebase plan order pair)).tests
    rw [GeneralNominalCenteredPlanReordering.inspection]

omit keys names
include order

theorem counterpart {one two : GeneralNominalCandidates.Context}
    (same : GeneralNominalJournalPermutation.ContextPair one two)
    (contextEq : plan.packet.context = one) (visible : plan.packet.declaration ∈ plan.packet.registry.declarations) :
    ∃ other : Plan roles, other.packet.registry = registry ∧ other.packet.context = two ∧
      other.packet.declaration ∈ registry.declarations ∧ Match plan other ∧
      RebasedPacket plan.packet.registry registry plan.packet other.packet := by
  obtain ⟨decl,present,pair⟩ := reorders_visible order plan.packet.declaration visible
  have contexts : GeneralNominalJournalPermutation.ContextPair plan.packet.context two := contextEq ▸ same
  obtain ⟨allocated,reserved,contextEq,keys,names⟩ := contexts.replace_form
  exact ⟨rebase plan order pair allocated reserved,rfl,contextEq.symm,present,
    matched plan order roleEq pair allocated reserved keys names,
    rebased plan order pair allocated reserved keys names⟩

omit order roleEq in
theorem safe {relation : GeneralNominalSaturationState.Packet roles → GeneralNominalSaturationState.Packet roles → Prop}
    {left right : GeneralNominalCenteredSteps.State roles} (same : Related relation left right)
    {first last : Plan roles} (matched : Match first last) :
    GeneralNominalCenteredSteps.Safe left first ↔ GeneralNominalCenteredSteps.Safe right last := by
  simp only [GeneralNominalCenteredSteps.Safe,matched.inspected,matched.tests,
    GeneralNominalCenteredPermutationSafety.cyclic same]

omit order roleEq in
theorem Match.symm {first last : Plan roles} (same : Match first last) : Match last first :=
  ⟨same.packet.symm,same.input.symm,declarationReorders_symm same.declaration,
    GeneralNominalCenteredPermutationSafety.plan_symm same.plans,same.located.symm,same.prepared.symm,
    fun root => (same.ready root).symm,same.inspected.symm,same.tests.symm⟩

end Yulang.GeneralNominalCenteredPermutationCounterparts
