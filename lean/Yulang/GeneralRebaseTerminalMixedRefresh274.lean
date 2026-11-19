import Yulang.GeneralRebaseTerminalStoreBoundary274

set_option maxRecDepth 25000
set_option maxHeartbeats 8500000
namespace Yulang.GeneralRebaseTerminalMixedRefresh274
open CommonNominalFullCarrier
open GeneralNominalCandidates (Context)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedJournal232 (Models)
open GeneralDictionaryVersionedSecondInstall233 (installed installed_model)
open GeneralDictionaryVersionedBothModel233 (extended)
open GeneralDictionaryVersionedSecondRaw233 (oldLo oldHi newLo newHi)
open GeneralNominalState (Known sources)
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryOptionalInitial229 (registry sourceRegistry start)

noncomputable abbrev raw := installed.core.erased.current.context.state

def widthCandidates : List Nat := [oldHi,newLo,newHi]

theorem known_zero : Known raw 0 := ⟨(0 : Fin 5),rfl,Or.inr ⟨_,rfl⟩⟩
theorem known_one : Known raw 1 := ⟨(1 : Fin 5),rfl,Or.inr ⟨_,rfl⟩⟩
theorem known_two : Known raw 2 := ⟨(2 : Fin 5),rfl,Or.inl (by intro never; cases never)⟩

theorem head_of_refresh (context : Context) (cert : Refresh installed context) (id : Nat)
 (known : Known context.state id) :
 ∃ t : GeneralNominalRecursiveInspection.Test, t.Holds (extended id).1 := by
 have all : Models (GeneralNominalVersionedRefresh232.refresh installed context) extended :=
   (refresh_models cert).mpr installed_model
 obtain ⟨test,o,head⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head known
 exact ⟨test,GeneralNominalCenteredHeadAllocMergeStable.head_holds head
   (GeneralCanonicalObservations.recorded_sound context.state extended all.1.1 (GeneralNominalSupport.head_recorded head))⟩

theorem no_new_top (context : Context) (cert : Refresh installed context) : ¬ Known context.state 3 := by
 intro new
 obtain ⟨test,held⟩ := head_of_refresh context cert 3 new
 have source := GeneralDictionaryVersionedSecondEquality233.index_model .three
 change (extended 3).1 = .top at source
 rw [source] at held
 exact GeneralDictionaryGroundCopy218Refresh.top_no_head test held

theorem no_new_output (context : Context) (cert : Refresh installed context) : ¬ Known context.state 4 := by
 intro new
 obtain ⟨test,held⟩ := head_of_refresh context cert 4 new
 have source := GeneralDictionaryVersionedSecondEquality233.index_model .four
 change (extended 4).1 = GeneralDictionaryOptionalOutput229.value at source
 rw [source] at held
 exact GeneralDictionaryOptionalOutput229.no_test test held

theorem no_new_old_lo (context : Context) (cert : Refresh installed context) : ¬ Known context.state oldLo := by
 intro new
 obtain ⟨test,held⟩ := head_of_refresh context cert oldLo new
 have source := GeneralDictionaryVersionedSecondEquality233.index_model .oldLower
 change (extended oldLo).1 = GeneralDictionaryOptionalOutput229.value at source
 rw [source] at held
 exact GeneralDictionaryOptionalOutput229.no_test test held

theorem only_width (context : Context) (cert : Refresh installed context) (id : Nat)
 (tracked : id ∈ sources raw) (novel : ¬ Known raw id) (new : Known context.state id) :
 id ∈ widthCandidates := by
 have listed := GeneralDictionaryVersionedSecondRaw233.source_support tracked
 simp only [GeneralDictionaryVersionedSecondRaw233.pool,List.mem_cons,List.not_mem_nil,or_false] at listed
 rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
 · exact False.elim (novel known_zero)
 · exact False.elim (novel known_one)
 · exact False.elim (novel known_two)
 · exact False.elim (no_new_top context cert new)
 · exact False.elim (no_new_output context cert new)
 · exact False.elim (no_new_old_lo context cert new)
 · simp [widthCandidates]
 · simp [widthCandidates]
 · simp [widthCandidates]

theorem candidates_tracked (id : Nat) (candidate : id ∈ widthCandidates) : id ∈ sources raw := by
 simp only [widthCandidates,List.mem_cons,List.not_mem_nil,or_false] at candidate
 rcases candidate with rfl | rfl | rfl <;> decide +kernel

theorem candidates_novel (id : Nat) (candidate : id ∈ widthCandidates) : ¬ Known raw id := by
 rintro ⟨slot,equal,_⟩
 have bound : slot.val < 5 := slot.isLt
 have same : slot.val = id := equal
 have high : 4 < id := by
   simp only [widthCandidates,List.mem_cons,List.not_mem_nil,or_false] at candidate
   rcases candidate with rfl | rfl | rfl <;> decide +kernel
 omega

theorem mixed_reachable :
 B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry root installed :=
 ⟨GeneralDictionaryVersionedInitialFrame233.before,
   ⟨start,GeneralDictionaryOptionalInitial229.initial,rfl⟩,
   GeneralNominalVersionedMixedKernel234.old_steps GeneralDictionaryVersionedSecondStep233.path⟩

end Yulang.GeneralRebaseTerminalMixedRefresh274
