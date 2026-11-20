import Yulang.GeneralDepthTwoEarlyShared300
import Yulang.GeneralDepthTwoPhaseCut300

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralDepthTwoOnlySecond300
open GeneralGeneratedNestedSource299 (root model)
open GeneralGeneratedNestedPredictions299 (compiled middle)
open GeneralDepthTwoFirstInstall300 (after)
open GeneralDepthTwoSecondInstall300 (final rootSite middleSite)
open GeneralDepthTwoMiddleContext300 (env after_raw_sites after_center_sites)
open GeneralDepthTwoMiddleFrame300 (after_model effect)
open GeneralDepthTwoFinalParents300 (oldRoot)
open GeneralDepthTwoEarlyShared300
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedMixedTerminalStable234 (no_refresh)
open GeneralNominalVersionedMixedKernel234 (Step Installable)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedCandidates231 (Prepared inputs)
open GeneralNominalExamples (registry intDisplay)
open GeneralDeclarationExamples (roles display)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalSaturationState (Generated)

theorem after_scope (d : Occurrence roles) (known : Generated after.core.erased.current root d) :
    d = root ∨ d = middle := by
  induction known with
  | root => exact .inl rfl
  | child _ edge _ =>
    rw [GeneralDepthTwoPhaseCut300.after_edges] at edge
    exact .inr (Prod.mk.inj (List.mem_singleton.mp edge)).2
  | alias _ first last _ _ =>
    rw [after_raw_sites] at last
    rcases List.mem_cons.mp last with rfl|last
    · exact .inl rfl
    · cases List.mem_singleton.mp last
      exact .inr GeneralDepthTwoRootPlan300.child_data.1

theorem recorded (d : Occurrence roles) (scope : d = root ∨ d = middle) :
    ∃ site ∈ after.core.erased.current.sites, site.occurrence = d := by
  rcases scope with rfl|rfl
  · exact ⟨_,after_raw_sites ▸ List.mem_cons_self ..,rfl⟩
  · exact ⟨middleSite.observed,after_raw_sites ▸ List.mem_cons_of_mem _ (List.mem_singleton_self _),
      GeneralDepthTwoRootPlan300.child_data.1⟩

theorem wrong_root : ¬ Prepared compiled env root intDisplay := by
  rintro ⟨_,_,bounds,located,_,finished,_⟩
  have right : GeneralNominalRecursiveCandidates.arguments env (inputs root) =
      some [((0 : Fin 3),(0 : Fin 3))] := by decide +kernel
  cases Option.some.inj (located.symm.trans right)
  exact (by decide +kernel : (GeneralNominalRecursiveCandidates.report env intDisplay
    [((0 : Fin 3),(0 : Fin 3))]).conflicts ≠ []) finished.2.1

theorem root_frame {p : GeneralNominalCenters.Plan roles} {key}
    (frame : Frame compiled after.core root key p) : p = oldRoot := by
  have old : Frame compiled after.core root 1 oldRoot :=
    GeneralNominalVersionedInstalledEvidence233.frame rfl after_model
  apply GeneralRebaseScopedFrame276.same_frame frame old
  · rcases GeneralRebaseCompiledDisplay277.compiled_members frame.visible frame.role_eq with bad|right
    · exact False.elim (wrong_root (bad ▸ frame.prepared))
    · exact right
  · have member := frame.raw_recorded
    rw [after_raw_sites] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with left|right
    · exact left
    · have bad : root = middle :=
        frame.occurrence_eq.symm.trans ((congrArg (fun s => s.occurrence) right).trans GeneralDepthTwoRootPlan300.child_data.1)
      exact False.elim (GeneralGeneratedNestedPredictions299.different_occurrences.1 (congrArg Occurrence.identity bad))
  · have member := frame.center_recorded
    rw [after_center_sites] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with left|right
    · exact left
    · have bad : root = middle := (p.input_exact.trans frame.occurrence_eq).symm.trans
        ((congrArg (fun s => s.occurrence) right).trans GeneralDepthTwoRootPlan300.child_data.1)
      exact False.elim (GeneralGeneratedNestedPredictions299.different_occurrences.1 (congrArg Occurrence.identity bad))

theorem only_step (next : State roles) (given : Step compiled root after next) : next = final := by
  obtain ⟨focus,g,op⟩ := given
  have scope := after_scope focus g
  cases op with
  | administrative action =>
    cases action with
    | enqueue _ absent =>
      obtain ⟨s,seen,eq⟩ := recorded _ scope
      exact False.elim (absent s seen eq)
    | refresh ctx cert id tracked unknown known =>
      exact False.elim (no_refresh headless_after cert tracked unknown known)
    | equate a b first last same novel => exact False.elim (novel (equality_after a b first last same))
    | reobserve rev _ improves =>
      exact False.elim (GeneralNominalReobservationSteps.pointClosed_no_revision closed_after rev improves)
  | refresh focus ctx cert id tracked unknown known =>
    exact False.elim (no_refresh headless_after cert tracked unknown known)
  | install candidate enabled novel =>
    have frame := candidate.frame
    rw [enabled.registry_eq,enabled.snapshot_eq] at frame
    rcases scope with atRoot|atMid
    · rw [atRoot] at frame
      have eq := root_frame frame
      apply False.elim
      apply novel
      rw [eq]
      exact GeneralNominalVersionedCommitted232.replay_committed _ _
    · rw [atMid] at frame
      have eq := GeneralDepthTwoSecondInstall300.frame_unique frame
      cases same_effect candidate effect enabled.registry_eq enabled.snapshot_eq eq
      rfl
  | merge first last a b same novel =>
    rw [after_center_sites] at a b
    simp only [List.mem_cons,List.not_mem_nil,or_false] at a b
    rcases a with rfl|rfl <;> rcases b with rfl|rfl
    · exact False.elim (novel (.refl _))
    · exact False.elim (GeneralDepthTwoCenters300.distinct_center after_model
        GeneralDepthTwoSecondInstall300.root_observed GeneralDepthTwoSecondInstall300.middle_observed
        (by decide) (by decide) (by decide) same)
    · exact False.elim (GeneralDepthTwoCenters300.distinct_center after_model
        GeneralDepthTwoSecondInstall300.middle_observed GeneralDepthTwoSecondInstall300.root_observed
        (by decide) (by decide) (by decide) same)
    · exact False.elim (novel (.refl _))

theorem exact_second (next : State roles) :
    (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Step registry root after next ↔ next = final :=
  ⟨only_step next,fun h => h.symm ▸ GeneralDepthTwoSecondInstall300.actual⟩

end Yulang.GeneralDepthTwoOnlySecond300
