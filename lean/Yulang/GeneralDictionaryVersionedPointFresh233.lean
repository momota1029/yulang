import Yulang.GeneralDictionaryVersionedPointStage233
import Yulang.GeneralDictionaryVersionedPointFrame233
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace Yulang.GeneralDictionaryVersionedPointFresh233
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryVersionedInitialModel233 (names)
open GeneralDictionaryVersionedNames231 (freshName oldVersionName newBindings oldBindings)
open GeneralDictionaryVersionedPointStage233

abbrev pool := [0,1,2,3,4,names 0,names 1]

theorem source_support : GeneralNominalState.sources point.core.erased.current.context.state ⊆ pool := by decide +kernel

theorem new_old_distinct (purpose previous : Nat) : freshName purpose ≠ oldVersionName previous := by
  by_cases same : purpose = previous
  · subst previous
    exact (GeneralDictionaryVersionedNames231.version_changed purpose).symm
  · exact GeneralNominalAggregateVersion231.distinct_purpose _ _ _ _ _ _ newBindings oldBindings same

theorem fresh_outside (purpose : Nat) : freshName purpose ∉ GeneralNominalState.sources point.core.erased.current.context.state := by
  intro member
  have present := source_support member
  have high := GeneralDictionaryVersionedNames231.fresh_above purpose
  simp only [pool,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with same | same | same | same | same | same | same
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact new_old_distinct purpose 0 same
  · exact new_old_distinct purpose 1 same

end Yulang.GeneralDictionaryVersionedPointFresh233
