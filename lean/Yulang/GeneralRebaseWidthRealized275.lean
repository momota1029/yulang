import Yulang.GeneralRebaseWidthCertificate275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 19000
set_option maxHeartbeats 6800000
namespace Yulang.GeneralRebaseWidthRealized275
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedKernel234 (Step Stable)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralDictionaryOptionalInitial229 (registry)
open GeneralRebaseTerminalMixedRefresh274 (widthCandidates raw candidates_novel candidates_tracked)
open GeneralRebaseWidthRefinement275 (registered)
open GeneralRebaseWidthCertificate275 (context certificate)
open GeneralNominalState (Known)

noncomputable def successor (id : Nat) (tracked : id ∈ widthCandidates) :=
 GeneralNominalVersionedRefresh232.refresh installed (context id tracked)

theorem realized (id : Nat) (tracked : id ∈ widthCandidates) :
 Step registry root installed (successor id tracked) :=
 ⟨root,.root,.refresh root (context id tracked) (certificate id tracked) id
   (candidates_tracked id tracked) (candidates_novel id tracked) (registered id tracked)⟩

theorem model_exact (id : Nat) (tracked : id ∈ widthCandidates) (m : Assignment) :
 Models (successor id tracked) m ↔ Models installed m :=
 GeneralNominalVersionedMixedObservations233.refresh_models (certificate id tracked)

theorem width_refresh : GeneralRebaseTerminalMixedFrontier274.WidthRefresh :=
 ⟨context _ List.mem_cons_self,certificate _ List.mem_cons_self,_,List.mem_cons_self,registered _ List.mem_cons_self⟩

theorem not_mixed_stable : ¬ Stable registry installed root :=
 fun stable => (GeneralRebaseTerminalMixedFrontier274.mixed_stable_iff.mp stable) width_refresh

theorem added (id : Nat) (tracked : id ∈ widthCandidates) :
 Known (successor id tracked).core.erased.current.context.state id ∧ ¬ Known raw id :=
 ⟨registered id tracked,candidates_novel id tracked⟩

theorem different (id : Nat) (tracked : id ∈ widthCandidates) : successor id tracked ≠ installed := by
 intro same
 have newer := (added id tracked).1
 rw [same] at newer
 exact (added id tracked).2 newer

end Yulang.GeneralRebaseWidthRealized275
