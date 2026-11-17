import Yulang.GeneralDictionaryUpper230Raw
import Yulang.GeneralDictionaryUpper230Support
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryUpper230Prepared
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryOptionalStage229 (allocated reserved ordinary)
open GeneralDictionaryUpper230Base GeneralDictionaryUpper230Snapshot
open GeneralDictionaryUpper230Current GeneralDictionaryUpper230Models

theorem current_prepared : GeneralNominalCenteredHeadCandidates.Prepared registry extendedContext root declaration := by
  refine ⟨GeneralDictionaryOptionalInitial229.source.metadata,⟨?_,by intro output member; cases member⟩,?_,
    [(0,0)],rfl,?_,modelHigh,GeneralDictionaryUpper230Raw.head_model high_raw⟩
  · intro index
    constructor <;> exact GeneralNominalAllocationSupport.slot_source extendedSnapshot (0 : Fin 6)
  · intro key member _
    change key ∈ snapshot.allocated ++ GeneralNominalAllocation.keys registry root.identity
    exact List.mem_append_right _ member
  · rw [report_exact]
    exact ⟨rfl,rfl,rfl⟩

theorem known : ¬ GeneralNominalState.RootPending extendedSnapshot root.demand := by
  rintro ⟨index,unknown⟩
  exact unknown GeneralDictionaryUpper230Support.known_zero

end Yulang.GeneralDictionaryUpper230Prepared
