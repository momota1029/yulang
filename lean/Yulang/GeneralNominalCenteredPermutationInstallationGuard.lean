import Yulang.GeneralNominalCenteredPermutationObservations

set_option backward.isDefEq.respectTransparency false

/-! The complete installation guard has a counterpart with the same support
witness. No selected-candidate or reachability premise is added to the rule. -/
namespace Yulang.GeneralNominalCenteredPermutationInstallationGuard
open GeneralDeclarations GeneralSourceDictionaries GeneralRegistryReordering GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredLedgerPermutation
open GeneralNominalCenteredPermutationCounterparts
variable {roles : Roles.RoleDecls}
variable {relation : GeneralNominalSaturationState.Packet roles → GeneralNominalSaturationState.Packet roles → Prop}
variable {left right : State roles} {r s : Registry} {plan other : Plan roles}

theorem packet_guard_forward (same : Related relation left right) (order : Reorders r s) (roleEq : r.roles = roles)
    (matched : Match plan other)
    (one : GeneralNominalFeedbackSteps.Installable r left.erased.current plan.packet)
    (two : GeneralNominalFeedbackSteps.Installable s right.erased.current other.packet)
    (support) (valid : PacketGuard left plan support) : PacketGuard right other support := by
  obtain ⟨⟨r₁,c₁,_,v₁,h₁,b₁,_⟩,_⟩ := one
  obtain ⟨⟨r₂,c₂,_,v₂,h₂,b₂,_⟩,_⟩ := two
  have packetOrder : Reorders plan.packet.registry other.packet.registry := by simpa only [r₁,r₂] using order
  obtain ⟨member,values,decision,safeBefore,alternatives,cycles,model,models,holds⟩ := valid
  refine ⟨matched.input ▸ (same.sites _).mp member,?_,?_,safe same matched |>.mp safeBefore,?_,?_,?_⟩
  · exact ⟨(GeneralNominalCenteredPermutationGuards.choices same.erased packetOrder matched c₁ c₂
      (r₁ ▸ v₁) (r₂ ▸ v₂) h₁ h₂ b₁ b₂ support).mp values.1,
      (same.erased.supported packetOrder support).mp values.2⟩
  · have before : DecisionGuard r left plan.packet.site.occurrence := by simpa only [GeneralNominalCenteredSteps.DecisionGuard,r₁,c₁] using decision
    have after := (GeneralNominalCenteredPermutationGuards.centered_decision same order _).mp before
    simpa only [DecisionGuard,r₂,c₂,matched.packet.site] using after
  · have before : AlternativesSafe r left plan.input := r₁ ▸ alternatives
    have after := (GeneralNominalCenteredPermutationObservations.alternatives same order roleEq plan.input).mp before
    simpa only [r₂,matched.input] using after
  · constructor
    · intro cycle
      rw [← matched.packet.site] at cycle
      exact cycles.1 ((GeneralNominalCenteredPermutationSafety.root_cycle same _).mpr cycle)
    · intro cycle
      rw [r₂,← matched.packet.site] at cycle
      have before := (GeneralNominalCenteredPermutationObservations.candidate same order roleEq _).mpr cycle
      exact cycles.2 (r₁ ▸ before)
  · exact ⟨model,(same.models model).mp models,(matched.packet.holds model).mp holds.1,
      (matched.plans.equations model).mp holds.2⟩

theorem packet_guard (same : Related relation left right) (order : Reorders r s) (roleEq : r.roles = roles)
    (matched : Match plan other)
    (one : GeneralNominalFeedbackSteps.Installable r left.erased.current plan.packet)
    (two : GeneralNominalFeedbackSteps.Installable s right.erased.current other.packet)
    (support) : PacketGuard left plan support ↔ PacketGuard right other support :=
  ⟨packet_guard_forward same order roleEq matched one two support,
    packet_guard_forward (GeneralNominalCenteredPermutationSafety.symm same)
      (GeneralRegistryChildOrder.reorders_symm order) (order.2.1.symm.trans roleEq) matched.symm two one support⟩

theorem counterpart_enabled (same : Related relation left right) (order : Reorders r s) (roleEq : r.roles = roles)
    (enabled : GeneralNominalFeedbackSteps.Installable r left.erased.current plan.packet)
    (novel : ¬ GeneralNominalFeedbackSteps.Committed left.erased.current plan.packet)
    (support) (guard : PacketGuard left plan support) :
    ∃ other : Plan roles, Match plan other ∧
      GeneralNominalCenteredPermutationRepresentation.RebasedPacket r s plan.packet other.packet ∧
      GeneralNominalFeedbackSteps.Installable s right.erased.current other.packet ∧
      ¬ GeneralNominalFeedbackSteps.Committed right.erased.current other.packet ∧ PacketGuard right other support := by
  have reg := enabled.1.1
  have ctx := enabled.1.2.1
  have visible := enabled.1.2.2.2.1
  obtain ⟨other,otherRegistry,otherContext,otherVisible,matched,rebased⟩ :=
    counterpart plan (reg ▸ order) (reg ▸ roleEq) same.erased.current.context ctx (reg ▸ visible)
  have otherEnabled := GeneralNominalCenteredPermutationInstallable.installable_forward same.erased.current order roleEq
    matched otherRegistry otherContext otherVisible enabled
  exact ⟨other,matched,reg ▸ rebased,otherEnabled,
    fun committed => novel ((same.erased.current.committed matched.packet.toPacketPair).mpr committed),
    (packet_guard same order roleEq matched enabled otherEnabled support).mp guard⟩

end Yulang.GeneralNominalCenteredPermutationInstallationGuard
