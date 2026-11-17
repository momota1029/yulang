import Yulang.GeneralDictionaryVersionLoopNext237
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryVersionLoopFresh238
open GeneralDictionaryVersionLoopSource237
open GeneralDictionaryVersionLoopPacket237 (lo hi)
open GeneralDictionaryVersionLoopNext237 (current)

theorem source_cover : GeneralNominalState.sources current.state ⊆ [0,1,2,3,lo,hi] := by
 decide +kernel

theorem lower_allocated : GeneralNominalAggregateVersion231.key 0 0 0 0 [(0,2,2),(0,2,2)] ∈ current.state.allocated := by
 decide +kernel

theorem upper_allocated : GeneralNominalAggregateVersion231.key 0 0 1 0 [(0,2,2),(0,2,2)] ∈ current.state.allocated := by
 decide +kernel

/-- All proposed reservation keys are fresh or already owned, independently
of which candidate packet asks for them. This does not prove a full install. -/
theorem owned (key : GeneralNominalIdentities.Origin)
 (present : GeneralNominalIdentities.source current.state.seed key ∈ GeneralNominalState.sources current.state) :
 key ∈ current.state.allocated := by
 have within := source_cover present
 simp only [List.mem_cons,List.not_mem_nil,or_false] at within
 have above := GeneralNominalIdentities.source_above_seed current.state.seed key
 change 3 < GeneralNominalIdentities.source 3 key at above
 change GeneralNominalIdentities.source 3 key = 0 ∨ GeneralNominalIdentities.source 3 key = 1 ∨
   GeneralNominalIdentities.source 3 key = 2 ∨ GeneralNominalIdentities.source 3 key = 3 ∨
   GeneralNominalIdentities.source 3 key = lo ∨ GeneralNominalIdentities.source 3 key = hi at within
 rcases within with a | a | a | a | a | a
 · omega
 · omega
 · omega
 · omega
 · have equal := (GeneralNominalIdentities.source_identity 3 key _).mp a
   exact equal ▸ lower_allocated
 · have equal := (GeneralNominalIdentities.source_identity 3 key _).mp a
   exact equal ▸ upper_allocated

theorem fresh : GeneralNominalVersionedAllocation231.Fresh current.state registry root.identity
 GeneralDictionaryVersionLoopNext237.packet.bindings := fun key _ present => owned key present
end Yulang.GeneralDictionaryVersionLoopFresh238
