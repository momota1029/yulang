import Yulang.GeneralRebaseTerminalProgram274

set_option maxRecDepth 21000
set_option maxHeartbeats 7000000
namespace Yulang.GeneralRebaseTerminalStoreBoundary274
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralDictionaryJournalRefinement228Source (snapshot modelHigh)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralDictionaryRebase230Private241 (publicAtoms oldBindings)
open GeneralRebaseTerminalStableCells274 (StoreChecked)
open GeneralRebaseTerminalDecode274 (decode stable_lo stable_hi)
open GeneralRebaseCompoundSourceTypes273 (PublicSource)
open PresenceNormalForm (All all_append)

theorem atoms_of_source (m : Assignment) (source : GeneralNominalState.Models snapshot m) :
 All model m publicAtoms := by
 have lower := GeneralDictionaryJournalRefinement228Source.lower_width m source
 unfold publicAtoms
 rw [all_append]
 constructor
 · apply (GeneralNominalAllocation.cross_exact oldBindings m).mpr
   intro a aa b bb _
   change a ∈ [(0,4,2),(0,4,2)] at aa
   change b ∈ [(0,4,2),(0,4,2)] at bb
   simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at aa bb
   subst a
   subst b
   exact lower
 · rw [GeneralDictionaryOptionalInstall229.report_exact]
   intro atom found
   simp only [GeneralNominalRecursiveInspection.selfChecks,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at found
   rcases found with rfl | rfl | rfl | rfl
   all_goals first | exact lower | exact subtype_refl _

theorem admits_uncommitted_output (m : Assignment) (source : PublicSource m) : StoreChecked (decode m) := by
 have raw := GeneralRebaseCompoundSourceTypes273.source_write (decode m)
   ((GeneralRebaseCompoundSourceTypes273.source_depends_on_types _ _
      (fun id small => congrArg Prod.fst ((GeneralRebaseTerminalDecode274.agrees m).1 id small))).mpr source)
 unfold StoreChecked
 rw [GeneralDictionaryRebase230Executor242.run_eq_final]
 refine ⟨atoms_of_source _ raw,?_⟩
 intro key member
 cases List.mem_singleton.mp member
 rw [GeneralDictionaryRebase230Scheduler242.final_block]
 exact GeneralRebaseTerminalDecode274.current_body _ (stable_lo m) (stable_hi m)

theorem width_source : PublicSource modelHigh :=
 GeneralRebaseCompoundSourceTypes273.source_reads _ (GeneralDictionaryJournalRefinement228Source.source_models true)

theorem width_only_store : StoreChecked (decode modelHigh) :=
 admits_uncommitted_output modelHigh width_source

theorem width_not_terminal : ¬ Models installed (decode modelHigh) := by
 intro valid
 have committed := GeneralRebaseTerminalPublic274.final_fixed _ valid 4 (by decide)
 rw [(GeneralRebaseTerminalDecode274.agrees modelHigh).1 4 (by decide),
     GeneralDictionaryJournalRefinement228Source.high_value] at committed
 exact GeneralDictionaryOptionalOutput229.not_width ⟨committed.2,committed.1⟩

/-- The stable merge store and the real journal must be checked together.
Even a genuine initial public boundary can satisfy the finished store
without respecting the source's associated-output equality. -/
theorem store_not_evidence :
 ∃ m, StoreChecked m ∧ ¬ Models installed m :=
 ⟨decode modelHigh,width_only_store,width_not_terminal⟩

end Yulang.GeneralRebaseTerminalStoreBoundary274
