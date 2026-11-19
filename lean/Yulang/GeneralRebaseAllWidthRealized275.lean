import Yulang.GeneralRebaseAllWidthCertificate275
import Yulang.GeneralRebaseWidthRealized275
import Yulang.GeneralNominalVersionedMixedRefreshEquality234

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 21000
set_option maxHeartbeats 6800000
namespace Yulang.GeneralRebaseAllWidthRealized275
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedKernel234 (Step Stable)
open GeneralDictionaryVersionedSecondInstall233 (installed installed_model)
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryOptionalInitial229 (registry sourceRegistry)
open GeneralRebaseTerminalMixedRefresh274 (raw widthCandidates candidates_novel candidates_tracked)
open GeneralRebaseAllWidthRefinement275 (registered refines support)
open GeneralRebaseAllWidthCertificate275 (context certificate)
open GeneralNominalState (Known)
open GeneralDictionaryVersionedSecondRaw233 (oldLo oldHi)

noncomputable def successor := GeneralNominalVersionedRefresh232.refresh installed context

theorem realized : Step registry root installed successor :=
 ⟨root,.root,.refresh root context certificate oldHi
    (candidates_tracked oldHi List.mem_cons_self) (candidates_novel oldHi List.mem_cons_self)
    (registered oldHi List.mem_cons_self)⟩

theorem model_exact (m : Assignment) : Models successor m ↔ Models installed m :=
 GeneralNominalVersionedMixedObservations233.refresh_models certificate

theorem reachable :
 B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles)
   sourceRegistry root successor := by
 obtain ⟨start,initial,steps⟩ := GeneralRebaseTerminalMixedRefresh274.mixed_reachable
 exact ⟨start,initial,.tail steps realized⟩

theorem all_three_known (id : Nat) (candidate : id ∈ widthCandidates) :
 Known successor.core.erased.current.context.state id :=
 registered id candidate

theorem equality_closed : GeneralNominalVersionedMixedTerminalStable234.EqualityClosed successor :=
 GeneralNominalVersionedMixedRefreshEquality234.old_equality_closed
   certificate GeneralDictionaryVersionedSecondEquality233.equality_closed

theorem headless : GeneralNominalVersionedMixedTerminalStable234.HeadlessUnknown successor := by
 refine ⟨_,(model_exact _).mpr installed_model,?_⟩
 intro id member unknown test yes
 have earlier := GeneralDictionaryVersionedSecondRaw233.source_support (support id member)
 simp only [GeneralDictionaryVersionedSecondRaw233.pool,List.mem_cons,List.not_mem_nil,or_false] at earlier
 rcases earlier with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 · exact unknown (refines.known _ GeneralRebaseTerminalMixedRefresh274.known_zero)
 · exact unknown (refines.known _ GeneralRebaseTerminalMixedRefresh274.known_one)
 · exact unknown (refines.known _ GeneralRebaseTerminalMixedRefresh274.known_two)
 · have e := GeneralDictionaryVersionedSecondEquality233.index_model .three
   change (GeneralDictionaryVersionedBothModel233.extended 3).1 = .top at e
   rw [e] at yes
   exact GeneralDictionaryGroundCopy218Refresh.top_no_head test yes
 · have e := GeneralDictionaryVersionedSecondEquality233.index_model .four
   change (GeneralDictionaryVersionedBothModel233.extended 4).1 = GeneralDictionaryOptionalOutput229.value at e
   rw [e] at yes
   exact GeneralDictionaryOptionalOutput229.no_test test yes
 · have e := GeneralDictionaryVersionedSecondEquality233.index_model .oldLower
   change (GeneralDictionaryVersionedBothModel233.extended oldLo).1 = GeneralDictionaryOptionalOutput229.value at e
   rw [e] at yes
   exact GeneralDictionaryOptionalOutput229.no_test test yes
 · exact unknown (all_three_known _ (by decide +kernel))
 · exact unknown (all_three_known _ (by decide +kernel))
 · exact unknown (all_three_known _ (by decide +kernel))

end Yulang.GeneralRebaseAllWidthRealized275
