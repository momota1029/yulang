import Yulang.GeneralNominalCenteredPermutationInstallable

set_option backward.isDefEq.respectTransparency false

/-! Support and decision guards retain the same dependency witness. Inspection
readback is transported at every visible candidate, including failed branches. -/
namespace Yulang.GeneralNominalCenteredPermutationGuards
open GeneralDeclarations GeneralSourceDictionaries GeneralRegistryReordering GeneralNominalCenters
open GeneralNominalCenteredPermutationCounterparts
variable {roles : Roles.RoleDecls}
variable {relation : GeneralNominalSaturationState.Packet roles → GeneralNominalSaturationState.Packet roles → Prop}
variable {first last : GeneralNominalSupport.Tracked roles} {r s : Registry}

theorem admissible (same : GeneralNominalLedgerPermutation.Related relation first last) (root support) :
    GeneralNominalSupport.Admissible first root support ↔ GeneralNominalSupport.Admissible last root support := by
  simp only [GeneralNominalSupport.Admissible,GeneralNominalSupport.External,
    same.current.discharged,same.current.generated]

theorem decision_forward (same : GeneralNominalLedgerPermutation.Related relation first last)
    (order : Reorders r s) (root : Occurrence roles) (support)
    (valid : GeneralNominalSupport.DecisionGuard first r root support) :
    GeneralNominalSupport.DecisionGuard last s root support := by
  refine ⟨(admissible same root support).mp valid.1,fun index => (same.ready support _).mp (valid.2.1 index),?_⟩
  intro decl visible role bounds located slot visited
  obtain ⟨other,present,pair⟩ := reorders_visible_back order decl visible
  obtain ⟨oldBounds,oldSlot,oldLocated,oldVisited,source⟩ := same.current.context.symm.inspection
    (declarationReorders_symm pair) root bounds located slot visited
  rw [← source]
  exact (same.ready support _).mp (valid.2.2 other present (pair.role.trans role) oldBounds oldLocated oldSlot oldVisited)

theorem decision (same : GeneralNominalLedgerPermutation.Related relation first last)
    (order : Reorders r s) (root : Occurrence roles) (support) :
    GeneralNominalSupport.DecisionGuard first r root support ↔ GeneralNominalSupport.DecisionGuard last s root support :=
  ⟨decision_forward same order root support,decision_forward same.symm (GeneralRegistryChildOrder.reorders_symm order) root support⟩

theorem choices_forward (same : GeneralNominalLedgerPermutation.Related relation first last)
    {plan other : Plan roles} (order : Reorders plan.packet.registry other.packet.registry) (matched : Match plan other)
    (oneContext : plan.packet.context = first.current.context) (twoContext : other.packet.context = last.current.context)
    (twoVisible : other.packet.declaration ∈ other.packet.registry.declarations)
    (twoRole : other.packet.declaration.role = other.packet.site.occurrence.demand.role)
    (twoLocated : GeneralNominalRecursiveCandidates.arguments other.packet.context other.packet.site.occurrence = some other.packet.bounds)
    (support) (valid : GeneralNominalSupportChoices.PacketGuard first plan.packet support) :
    GeneralNominalSupportChoices.PacketGuard last other.packet support := by
  have before : GeneralNominalSupport.DecisionGuard first plan.packet.registry plan.packet.site.occurrence support := by
    simpa only [oneContext] using valid.2
  have after := (decision same order _ support).mp before
  rw [matched.packet.site] at after
  have target : GeneralNominalSupport.DecisionGuard
      {last with current := {last.current with context := other.packet.context}}
      other.packet.registry other.packet.site.occurrence support := by
    simpa only [twoContext] using after
  exact ⟨⟨target.1,target.2.1,target.2.2 _ twoVisible twoRole _ twoLocated⟩,target⟩

theorem choices (same : GeneralNominalLedgerPermutation.Related relation first last)
    {plan other : Plan roles} (order : Reorders plan.packet.registry other.packet.registry) (matched : Match plan other)
    (oneContext : plan.packet.context = first.current.context) (twoContext : other.packet.context = last.current.context)
    (oneVisible : plan.packet.declaration ∈ plan.packet.registry.declarations)
    (twoVisible : other.packet.declaration ∈ other.packet.registry.declarations)
    (oneRole : plan.packet.declaration.role = plan.packet.site.occurrence.demand.role)
    (twoRole : other.packet.declaration.role = other.packet.site.occurrence.demand.role)
    (oneLocated : GeneralNominalRecursiveCandidates.arguments plan.packet.context plan.packet.site.occurrence = some plan.packet.bounds)
    (twoLocated : GeneralNominalRecursiveCandidates.arguments other.packet.context other.packet.site.occurrence = some other.packet.bounds)
    (support) : GeneralNominalSupportChoices.PacketGuard first plan.packet support ↔
      GeneralNominalSupportChoices.PacketGuard last other.packet support :=
  ⟨choices_forward same order matched oneContext twoContext twoVisible twoRole twoLocated support,
    choices_forward same.symm (GeneralRegistryChildOrder.reorders_symm order) matched.symm twoContext oneContext oneVisible oneRole oneLocated support⟩

variable {left right : GeneralNominalCenteredSteps.State roles}

theorem centered_decision_forward (same : GeneralNominalCenteredLedgerPermutation.Related relation left right)
    (order : Reorders r s) (root : Occurrence roles) (valid : GeneralNominalCenteredSteps.DecisionGuard r left root) :
    GeneralNominalCenteredSteps.DecisionGuard s right root := by
  refine ⟨fun index => (GeneralNominalCenteredPermutationSafety.ready same _).mp (valid.1 index),?_⟩
  intro decl visible role bounds located slot visited
  obtain ⟨other,present,pair⟩ := reorders_visible_back order decl visible
  obtain ⟨oldBounds,oldSlot,oldLocated,oldVisited,source⟩ := same.erased.current.context.symm.inspection
    (declarationReorders_symm pair) root bounds located slot visited
  rw [← source]
  exact (GeneralNominalCenteredPermutationSafety.ready same _).mp
    (valid.2 other present (pair.role.trans role) oldBounds oldLocated oldSlot oldVisited)

theorem centered_decision (same : GeneralNominalCenteredLedgerPermutation.Related relation left right)
    (order : Reorders r s) (root : Occurrence roles) :
    GeneralNominalCenteredSteps.DecisionGuard r left root ↔ GeneralNominalCenteredSteps.DecisionGuard s right root :=
  ⟨centered_decision_forward same order root,
    centered_decision_forward (GeneralNominalCenteredPermutationSafety.symm same) (GeneralRegistryChildOrder.reorders_symm order) root⟩

end Yulang.GeneralNominalCenteredPermutationGuards
