import Yulang.GeneralVersionedHarmlessRefresh312
import Yulang.GeneralVersionedProtectedName312

set_option backward.isDefEq.respectTransparency false
/-! Registry-wide reservations can include an aggregate for a declaration
other than the one actually installed. Matching semantic entries must still
come from the right invocation and the right declaration key. -/
namespace Yulang.GeneralVersionedReservedOther312
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedInstall232 (install)
open GeneralVersionedProtectedName312 (atSlot)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralNominalVersionedAggregateRealization236 (member_iff)
open GeneralNominalAllocation (occurrences)
open GeneralNominalSaturationState (Packet)
variable {roles : Roles.RoleDecls}

theorem reserved {s : State roles} {e : Effect roles} {p : Packet roles}
    (seed : e.plan.packet.context.state.seed = p.context.state.seed)
    (invocation : e.plan.packet.site.occurrence.identity = p.site.occurrence.identity)
    (visible : p.declaration ∈ e.plan.packet.registry.declarations)
    (named : name ∈ p.declaration.inputNames)
    (version : occurrences e.plan.packet.bindings name = occurrences p.bindings name) :
    atSlot p 0 name ∈ GeneralNominalState.sources (install s e).core.erased.current.context.state ∧
    atSlot p 1 name ∈ GeneralNominalState.sources (install s e).core.erased.current.context.state := by
  have old := GeneralNominalVersionedAllocation231.aggregate_reserved
    (state := e.plan.packet.context.state) (root := e.plan.packet.site.occurrence.identity)
    (bindings := e.plan.packet.bindings) visible named
  have equal (mode : Nat) :
      GeneralNominalAggregateVersion231.slot e.plan.packet.context.state.seed
        e.plan.packet.site.occurrence.identity p.declaration.id mode name e.plan.packet.bindings = atSlot p mode name := by
    have code := GeneralNominalAggregateVersion231.version_eq_iff.mpr version
    unfold atSlot GeneralNominalAggregateVersion231.slot GeneralNominalAggregateVersion231.key
    rw [seed,invocation,code]
  rw [equal 0,equal 1] at old
  have fromReserved (n : Nat) (seen : n ∈ GeneralNominalVersionedInstallation231.reserved e.plan.packet) :
      n ∈ GeneralNominalState.sources (install s e).core.erased.current.context.state := by
    apply List.mem_append_left
    apply List.mem_append_right
    change n ∈ e.plan.packet.context.state.reserved ++ GeneralNominalVersionedInstallation231.reserved e.plan.packet
    exact List.mem_append_right _ seen
  exact ⟨fromReserved _ old.1,fromReserved _ old.2⟩

theorem recorded_owner {p : Packet roles} {past : Plan roles}
    (seed : past.packet.context.state.seed = p.context.state.seed)
    {row : GeneralNominalFiniteEquationRealization236.Entry}
    (rowMember : row ∈ packetEntries past.packet)
    (hit : row.1 = atSlot p mode name) :
    past.packet.site.occurrence.identity = p.site.occurrence.identity ∧
      past.packet.declaration.id = p.declaration.id := by
  obtain ⟨earlier,_,_,left | right⟩ := (member_iff ..).mp rowMember
  · have atRow : atSlot past.packet 0 earlier = atSlot p mode name :=
      (congrArg Prod.fst left).symm.trans hit
    unfold atSlot at atRow
    rw [seed] at atRow
    have same := GeneralNominalVersionedAggregateReuse236.slot_fields atRow
    exact ⟨same.1,same.2.1⟩
  · have atRow : atSlot past.packet 1 earlier = atSlot p mode name :=
      (congrArg Prod.fst right).symm.trans hit
    unfold atSlot at atRow
    rw [seed] at atRow
    have same := GeneralNominalVersionedAggregateReuse236.slot_fields atRow
    exact ⟨same.1,same.2.1⟩

theorem absent_with_different_key {s : State roles} {p : Packet roles}
    (seeds : ∀ old ∈ s.plans, old.packet.context.state.seed = p.context.state.seed)
    (foreign : ∀ old ∈ s.plans, old.packet.site.occurrence.identity = p.site.occurrence.identity →
      old.packet.declaration.id ≠ p.declaration.id) :
    ∀ old ∈ s.plans, ∀ row ∈ packetEntries old.packet, row.1 ≠ atSlot p mode name := by
  intro plan stored row seen equal
  obtain ⟨owner,key⟩ := recorded_owner (seeds plan stored) seen equal
  exact foreign plan stored owner key

end Yulang.GeneralVersionedReservedOther312
