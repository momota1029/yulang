import Yulang.GeneralNominalAcyclicEquations237
import Yulang.GeneralNominalVersionedMixedSeedLedger237
import Yulang.GeneralNominalVersionedDependency236
set_option backward.isDefEq.respectTransparency false
/-! One explicit solution for all actual historical aggregate equations.
This is not a solution of the full journal, actual-head or output subsystem. -/
namespace Yulang.GeneralNominalVersionedHistoryEquations237
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedMixedSeedLedger237 (entries Recorded)
open GeneralNominalVersionedAggregateLedger236 (packetEntries)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls}

theorem packet_descending (packet : GeneralNominalSaturationState.Packet roles) :
 GeneralNominalAcyclicEquations237.Descending (packetEntries packet) := by
 intro entry member identity within
 obtain ⟨name,_,_,rfl | rfl⟩ := (GeneralNominalVersionedAggregateRealization236.member_iff ..).mp member
 · apply List.mem_range.mp
   apply GeneralNominalAllocationSupport.lower_sources _ (pool := List.range _)
     (fun pair present => ?_) within
   have bounds := GeneralNominalVersionedDependency236.endpoints_below_slot packet.context.state.seed
     packet.site.occurrence.identity packet.declaration.id 0 name packet.bindings present
   exact ⟨List.mem_range.mpr bounds.1,List.mem_range.mpr bounds.2⟩
 · apply List.mem_range.mp
   apply GeneralNominalAllocationSupport.upper_sources _ (pool := List.range _)
     (fun pair present => ?_) within
   have bounds := GeneralNominalVersionedDependency236.endpoints_below_slot packet.context.state.seed
     packet.site.occurrence.identity packet.declaration.id 1 name packet.bindings present
   exact ⟨List.mem_range.mpr bounds.1,List.mem_range.mpr bounds.2⟩

theorem descending (state : State roles) : GeneralNominalAcyclicEquations237.Descending (entries state) := by
 intro entry member
 obtain ⟨plan,_,member⟩ := List.mem_flatMap.mp member
 exact packet_descending plan.packet entry member

theorem coherent (recorded : Recorded state) : GeneralNominalAcyclicEquations237.Coherent (entries state) :=
 fun _ one _ two same => GeneralNominalVersionedMixedSeedLedger237.same_entry recorded one two same

noncomputable def solution (state : State roles) (base : Assignment) : Assignment :=
 GeneralNominalAcyclicEquations237.solution (entries state) base

theorem all_equations (recorded : Recorded state) (base : Assignment) :
 ∀ entry ∈ entries state, PresenceNormalForm.All CommonNominalFullCarrier.model (solution state base)
   (GeneralNominalAllocation.equations entry.1 entry.2) :=
 GeneralNominalAcyclicEquations237.equations _ base (coherent recorded) (descending state)

theorem all_merges (recorded : Recorded state) (base : Assignment) :
 ∀ plan ∈ state.plans, PresenceNormalForm.All CommonNominalFullCarrier.model (solution state base)
   (GeneralNominalVersionedAllocation231.merges plan.packet.context.state plan.packet.registry
     plan.packet.site.occurrence.identity plan.packet.declaration plan.packet.bindings) := by
 intro plan member
 apply (GeneralNominalVersionedAggregateEntries236.holds_iff ..).mpr
 intro entry present
 exact all_equations recorded base entry (List.mem_flatMap.mpr ⟨plan,member,present⟩)

theorem source_merges
 (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
 (base : Assignment) :
 ∀ plan ∈ state.plans, PresenceNormalForm.All CommonNominalFullCarrier.model (solution state base)
   (GeneralNominalVersionedAllocation231.merges plan.packet.context.state plan.packet.registry
     plan.packet.site.occurrence.identity plan.packet.declaration plan.packet.bindings) :=
 all_merges (GeneralNominalVersionedMixedSeedLedger237.reachable path) base

theorem external (state : State roles) (base : Assignment)
 (absent : ∀ entry ∈ entries state, entry.1 ≠ identity) : solution state base identity = base identity :=
 GeneralNominalAcyclicEquations237.outside _ base absent

theorem rows (state : State roles) (base : Assignment) (identity : Nat) :
 (solution state base identity).2 = (base identity).2 := rfl
end Yulang.GeneralNominalVersionedHistoryEquations237
