import Yulang.GeneralMixedCompoundPointExact307
import Yulang.GeneralMixedCompoundUpperOutcome307

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 19000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralMixedCompoundPointEvidence307
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryCompoundSource238 (registry sourceRegistry)
open GeneralDictionaryCompoundSites238 (childSite raw_sites)
open GeneralMixedCompoundRefreshBound307 (Run)
open GeneralMixedCompoundPointSpine307 (reach sites spine)
open GeneralMixedCompoundPointRoot307 (frame_plan same_read no_packet)
open GeneralMixedCompoundTail307 (registered)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalCommonBridge (Assignment)

variable {s : State roles} {n : Nat}

theorem no_child_evidence (path : Run n s) (m : Assignment) (payload : GeneralDictionaryReadback.Payload) :
    ¬ Evidence registry s.core m childSite.occurrence payload := by
  intro ev
  have indexed := (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr ev
  cases indexed with
  | node instanceProof _ =>
    obtain ⟨p,framed⟩ := instanceProof
    exact GeneralMixedCompoundPointChild307.no_frame path p framed.frame

theorem no_root_evidence (path : Run n s) (m : Assignment) (valid : Models s m)
    (payload : GeneralDictionaryReadback.Payload) :
    ¬ Evidence registry s.core m root payload := by
  intro ev
  obtain ⟨coordinates⟩ := spine path
  have indexed := (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr ev
  cases indexed with
  | node instanceProof _ =>
    obtain ⟨p,certificate⟩ := instanceProof
    have exactPlan := frame_plan path coordinates certificate.frame
    have held := certificate.packet
    rw [exactPlan] at held
    exact no_packet path coordinates m valid held

theorem evidenceAt (path : Run n s) : B4SkeletonV8.EvidenceAt (boundary roles) sourceRegistry s root := by
  intro m valid focus key kids dict reached _ _ chosen evidence
  have which : focus = root ∨ focus = childSite.occurrence :=
    reached.elim Or.inl (registered (reach path) ((sites path).trans raw_sites))
  obtain ⟨p,frame,children⟩ := GeneralNominalVersionedMixedSelectedFrame235.source_frame (reach path) chosen
  rcases which with rfl|rfl
  · obtain ⟨coordinates⟩ := spine path
    have eq := frame_plan path coordinates frame
    rw [eq,GeneralDeferredLadderTransport302.children_eq (same_read _ coordinates),
      GeneralDictionaryCompoundVacuity239.current_children] at children
    subst kids
    cases evidence with
    | cons one _ => exact False.elim (no_child_evidence path m _ one)
  · exact False.elim (GeneralMixedCompoundPointChild307.no_frame path p frame)

end Yulang.GeneralMixedCompoundPointEvidence307
