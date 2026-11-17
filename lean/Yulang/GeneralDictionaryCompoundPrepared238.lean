import Yulang.GeneralDictionaryCompoundPointHead238
import Yulang.GeneralDictionaryCompoundSites238
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace Yulang.GeneralDictionaryCompoundPrepared238
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238 GeneralDictionaryCompoundPoint238
open GeneralDictionaryCompoundObstruction238 GeneralDictionaryCompoundSites238
open GeneralNominalCenters GeneralNominalVersionedCandidates231
open GeneralDictionaryCompoundPointModel238 (extended)

theorem values : GeneralDictionaryCompoundPointHead238.Values extended := by
  constructor
  · rw [GeneralDictionaryCompoundPointModel238.old_value 0 (by simp [GeneralDictionaryCompoundPointModel238.pool,GeneralDictionaryCompoundVersionedModel238.pool]),
      GeneralDictionaryCompoundVersionedModel238.old_value 0 (by simp [GeneralDictionaryCompoundVersionedModel238.pool])]
    unfold GeneralDictionaryCompoundVersionedModel238.baseModel
    rw [GeneralDictionaryCompoundModel238.old_value 0 (by simp [GeneralDictionaryCompoundModel238.pool])]
    rfl
  · rw [GeneralDictionaryCompoundPointModel238.old_value 2 (by simp [GeneralDictionaryCompoundPointModel238.pool,GeneralDictionaryCompoundVersionedModel238.pool]),
      GeneralDictionaryCompoundVersionedModel238.old_value 2 (by simp [GeneralDictionaryCompoundVersionedModel238.pool])]
    unfold GeneralDictionaryCompoundVersionedModel238.baseModel
    rw [GeneralDictionaryCompoundModel238.old_value 2 (by simp [GeneralDictionaryCompoundModel238.pool])]
    rfl
  · rw [GeneralDictionaryCompoundPointModel238.old_value GeneralDictionaryCompoundPacket238.actual (by simp [GeneralDictionaryCompoundPointModel238.pool,GeneralDictionaryCompoundVersionedModel238.pool]),
      GeneralDictionaryCompoundVersionedModel238.old_value _ (by simp [GeneralDictionaryCompoundVersionedModel238.pool])]
    unfold GeneralDictionaryCompoundVersionedModel238.baseModel
    rw [GeneralDictionaryCompoundModel238.old_value _ (by simp [GeneralDictionaryCompoundModel238.pool])]
    exact GeneralDictionaryCompoundPacket238.actual_value
  · rw [GeneralDictionaryCompoundPointModel238.old_value 4 (by simp [GeneralDictionaryCompoundPointModel238.pool,GeneralDictionaryCompoundVersionedModel238.pool]),
      GeneralDictionaryCompoundVersionedModel238.old_value 4 (by simp [GeneralDictionaryCompoundVersionedModel238.pool])]
    unfold GeneralDictionaryCompoundVersionedModel238.baseModel
    rw [GeneralDictionaryCompoundModel238.old_value 4 (by simp [GeneralDictionaryCompoundModel238.pool])]
    rfl
  · exact GeneralDictionaryCompoundPointModel238.next_value 0
  · exact GeneralDictionaryCompoundPointModel238.next_value 1

theorem raw_model : GeneralNominalState.Models point.core.erased.current.context.state extended :=
  GeneralDictionaryCompoundPointModel238.model.1.1

theorem head_model : GeneralNominalVersionedPlans231.HeadModels currentPlan.packet extended :=
  GeneralDictionaryCompoundPointHead238.head_models allocated reserved ordinary values raw_model

theorem fresh : GeneralNominalVersionedAllocation231.Fresh point.core.erased.current.context.state registry root.identity currentPlan.packet.bindings := by
  rw [GeneralDictionaryCompoundCurrent238.bindings_exact]
  intro key member collision
  change key ∈ [GeneralNominalAggregateVersion231.key root.identity declaration.id 0 0 [(0,2,2),(0,2,2)],
    GeneralNominalAggregateVersion231.key root.identity declaration.id 1 0 [(0,2,2),(0,2,2)],
    GeneralNominalAggregateVersion231.key root.identity declaration.id 0 0 [(0,2,2),(0,2,2)],
    GeneralNominalAggregateVersion231.key root.identity declaration.id 1 0 [(0,2,2),(0,2,2)],
    GeneralNominalAllocation.origin root.identity declaration.id 6 0 0,
    GeneralNominalAllocation.origin root.identity declaration.id 3 0 0,
    GeneralNominalAllocation.origin root.identity declaration.id 4 0 0] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact False.elim ((by decide +kernel : GeneralDictionaryCompoundPointModel238.nextName 0 ∉ GeneralNominalState.sources point.core.erased.current.context.state) collision)
    | exact False.elim ((by decide +kernel : GeneralDictionaryCompoundPointModel238.nextName 1 ∉ GeneralNominalState.sources point.core.erased.current.context.state) collision)
    | decide +kernel

theorem prepared : Prepared registry point.core.erased.current.context root declaration := by
  rw [context_exact]
  refine ⟨source.metadata,⟨?_,by intro output member; cases member⟩,[(0,0)],rfl,?_,?_,extended,head_model⟩
  · intro index
    constructor <;> exact GeneralNominalAllocationSupport.slot_source (GeneralDictionaryCompoundCurrent238.currentContext allocated reserved ordinary).state (0 : Fin 5)
  · have h := fresh; rw [context_exact] at h; exact h
  · rw [GeneralDictionaryCompoundCurrent238.report_exact]
    exact ⟨rfl,rfl,rfl⟩

theorem frame : GeneralNominalVersionedEvidence231.Frame registry point.core root declaration.id currentPlan := by
  refine ⟨rfl,context_exact.symm,rfl,rfl,?_,?_,List.mem_singleton_self _,rfl,rfl,prepared⟩
  · rw [raw_sites]; exact List.mem_cons_self ..
  · rw [centers]; exact List.mem_cons_self ..

end Yulang.GeneralDictionaryCompoundPrepared238
