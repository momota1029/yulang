import Yulang.GeneralDeclarativeStoppedFold340
import Yulang.GeneralLiveCompoundFullResult316

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStoppedObstruction341
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry boundary_checked)
open GeneralLiveCompoundLeafInstall316 (after reachable after_model)
open GeneralLiveCompoundPost316 (generated_after)
open GeneralLiveCompoundChildSite316 (child)
open GeneralLiveCompoundPostFrames316 (root_frame_plan no_root_packet no_root_evidence)
open GeneralLiveCompoundStable316 (halted)
open GeneralLiveCompoundFullResult316 (classified)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalSaturationState (Generated)
open GeneralDeclarativeStoppedSelected340 (FitFrame)
open GeneralDeclarativeStoppedFold340 (Produces)
open GeneralNominalVersionedJournal232 (Models)

/-- The original reachable current frame cannot supply a full root
packet in any model of the final state. No assumption about local
diagnostic equivalence or declarative selection is used. -/
theorem packet_impossible (frame : Frame registry after.core root key plan)
    (fit : Models after m) : ¬ GeneralNominalVersionedPlans231.Holds plan m := by
  rw [root_frame_plan frame]
  exact no_root_packet fit

theorem not_root_producer :
    ¬ ∃ key plan, Frame registry after.core root key plan ∧ FitFrame (s := after) root plan := by
  rintro ⟨_,_,frame,fit⟩
  obtain ⟨_,current,packet,_⟩ := fit.feasible
  exact packet_impossible frame current packet

theorem not_produces : ¬ Produces sourceRegistry after root := by
  intro produces
  obtain ⟨plan,frame,fit⟩ := produces root .root _ _ GeneralLiveCompoundPostRootSelect316.selected
  exact not_root_producer ⟨_,plan,frame,fit⟩

theorem actual_obstruction :
    B4TargetV8.Reachable (boundary roles) sourceRegistry root after ∧
    (∀ next, ¬ Step registry root after next) ∧
    Generated after.core.erased.current root child ∧
    B4TargetV8.Classify (boundary roles) sourceRegistry after root
      (.selected GeneralLiveCompoundFullResult316.dictionary) ∧
    ¬ Produces sourceRegistry after root :=
  ⟨reachable,halted,generated_after,classified,not_produces⟩

end Yulang.GeneralDeclarativeStoppedObstruction341
