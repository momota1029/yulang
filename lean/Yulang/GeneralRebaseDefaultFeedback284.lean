import Yulang.GeneralRebaseWatchGuardSteps284

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28900
set_option maxHeartbeats 10800000
namespace Yulang.GeneralRebaseDefaultFeedback284
open GeneralDictionaryDefaultGap206Source (roles registry root)
open GeneralDictionaryVersionedGap206Install233 (installed reachable)
open GeneralDictionaryVersionedGap206Feedback234 (feedback installed_equal not_raw_equal)
open GeneralRebaseHistoryOrder282 (history)
open GeneralRebaseActualWatch284 (Cache)
open GeneralRebaseWatchGuardQueries284 (Cached)
open GeneralRebaseSliceJournal283 (journalReads)
open GeneralRebaseWatchGuardSteps284 (EquateInput)
open GeneralRebaseMixedCounts277 (Actual)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable)
open GeneralPresenceUsedSupport245 (typedReads)
open CommonNominalFullCarrier (Equivalent)

noncomputable def watch : List Nat := [0,1] ++ journalReads installed ++ (history installed).flatMap (fun row => typedReads row.2)

noncomputable def defs := GeneralRebaseInstallCache283.initial installed

theorem seen : Reachable registry root installed :=
  GeneralNominalVersionedMixedEmbedding234.reachable reachable

theorem cache_valid : Cache installed watch defs := by
  have valid := GeneralRebaseInstallCache283.initial_valid (GeneralNominalVersionedMixedSeedLedger237.reachable seen)
  refine ⟨⟨?_,fun {_} h => (valid.content _).mp h,fun row h _ => (valid.content row).mpr h⟩,valid.increasing⟩
  intro row h _ name read
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨row,h,read⟩)

theorem retains_eq : ∀ m, Cached installed defs m → Equivalent (m 0).1 (m 1).1 := by
  have required : journalReads installed ⊆ watch := fun {_} req => List.mem_append_left _ (List.mem_append_right _ req)
  have a : 0 ∈ watch := List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..))
  have b : 1 ∈ watch := List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))
  exact (GeneralRebaseWatchGuardQueries284.equality cache_valid seen required 0 1 a b).mp installed_equal

theorem actual_feedback : Actual registry root installed feedback := by
  have required : journalReads installed ⊆ watch := fun {_} req => List.mem_append_left _ (List.mem_append_right _ req)
  have ready : EquateInput installed root root 0 1 := by
    refine ⟨.root,?_,?_,not_raw_equal⟩ <;> simp only [GeneralNominalState.sources,List.mem_append]
    · exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨(0 : Fin 3),rfl⟩)))
    · exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨(1 : Fin 3),rfl⟩)))
  exact GeneralRebaseWatchGuardSteps284.equate_sound cache_valid seen required ready
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..)))
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))) retains_eq

end Yulang.GeneralRebaseDefaultFeedback284
