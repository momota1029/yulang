import Yulang.GeneralRebaseDepthBudgetExact286

/-! The finite driver observes exactly strict narrowing of complete raw
models for this fixture. Its visible installation preserves the conditional
same-assignment realizations (Models together with leaf Evidence). -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseDepthSemanticTransitions286
open GeneralDictionaryOutputDepth252 (roles root registry initial)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralRebaseDepthPhase286 (Hop InstallHop)
open GeneralRebaseOutputDepthTrace271 (observe)

def SameModels (s t : State roles) : Prop := ∀ m, Models s m ↔ Models t m

def StrictFilter (s t : State roles) : Prop :=
  (∀ m, Models t m → Models s m) ∧ ∃ m, Models s m ∧ ¬ Models t m

theorem refresh_same {s t : State roles} (h : Hop s t) : SameModels s t := by
  cases h with
  | refresh _ cert _ _ _ _ =>
    exact fun _ => (GeneralNominalVersionedMixedObservations233.refresh_models cert).symm

theorem installs_strict {s t : State roles} {n : Nat} (prior : ActualPath initial s n)
    (install : InstallHop s t) : StrictFilter s t := by
  rcases GeneralRebaseDepthFullTrace286.decomposes prior with pure|crossed
  · have linked := GeneralRebaseDepthFullTrace286.linked_after pure
    have pre := GeneralRebaseDepthEnableShape286.as_pre linked
    exact GeneralRebaseDepthReachableReadback286.strict_raw_filter pre
      (GeneralRebaseDepthPhase286.cross pre install)
  · exact (GeneralRebaseDepthSimulation286.no_install_after
      (GeneralRebaseDepthFullTrace286.crosses_post crossed) install).elim

theorem visible_iff_strict {s t : State roles} {n : Nat}
    (prior : ActualPath initial s n) (step : Step registry root s t) :
    observe t ≠ observe s ↔ StrictFilter s t := by
  constructor
  · intro visible
    exact installs_strict prior ((GeneralRebaseDepthSimulation286.visible_iff_install prior step).mp visible)
  · intro strict equal
    rcases GeneralRebaseDepthSimulation286.shadow prior step with ⟨h,_⟩|⟨installed,_⟩
    · obtain ⟨m,earlier,gone⟩ := strict.2
      exact gone ((refresh_same h m).mp earlier)
    · exact ((GeneralRebaseDepthSimulation286.visible_iff_install prior step).mpr installed) equal

theorem silent_iff_same_models {s t : State roles} {n : Nat}
    (prior : ActualPath initial s n) (step : Step registry root s t) :
    observe t = observe s ↔ SameModels s t := by
  constructor
  · intro same
    rcases GeneralRebaseDepthSimulation286.shadow prior step with ⟨h,_⟩|⟨installed,_⟩
    · exact refresh_same h
    · exact (((GeneralRebaseDepthSimulation286.visible_iff_install prior step).mpr installed) same).elim
  · intro equal
    apply Classical.byContradiction
    intro visible
    obtain ⟨m,old,no⟩ := ((visible_iff_strict prior step).mp visible).2
    exact no ((equal m).mp old)

theorem joint_unchanged {s t : State roles} {n : Nat}
    (prior : ActualPath initial s n) (step : Step registry root s t) (m : Assignment) (p : Payload) :
    Models s m ∧ Evidence registry s.core m root p ↔
      Models t m ∧ Evidence registry t.core m root p :=
  (GeneralRebaseDepthPreEvidence286.same_joint_everywhere prior m p).trans
    (GeneralRebaseDepthPreEvidence286.same_joint_everywhere (.more prior step) m p).symm

/-- The compiled two-state view identifies exactly the full-model equivalence
classes of all reachable raw states, including states on unrelated paths. -/
theorem same_view_iff_same_models {s t : State roles} {i j : Nat}
    (left : ActualPath initial s i) (right : ActualPath initial t j) :
    observe s = observe t ↔ SameModels s t := by
  have a := GeneralRebaseDepthProjectedPath286.observed_phase left
  have b := GeneralRebaseDepthProjectedPath286.observed_phase right
  rcases GeneralRebaseDepthPhase286.path_covered (.inl GeneralRebaseDepthPhase286.start) left with preL|postL <;>
    rcases GeneralRebaseDepthPhase286.path_covered (.inl GeneralRebaseDepthPhase286.start) right with preR|postR
  · exact ⟨fun _ m => (preL.anchor.models m).trans (preR.anchor.models m).symm,
      fun _ => (a.2.mpr preL).trans (b.2.mpr preR).symm⟩
  · constructor
    · intro equal
      have wrong : GeneralRebaseDepthPhase286.Post s := a.1.mp (equal.trans (b.1.mpr postR))
      exact (GeneralRebaseDepthPhase286.exclusive preL wrong).elim
    · intro models
      obtain ⟨m,valid,notAfter⟩ := (GeneralRebaseDepthReachableReadback286.strict_raw_filter preL postR).2
      exact (notAfter ((models m).mp valid)).elim
  · constructor
    · intro equal
      have wrong : GeneralRebaseDepthPhase286.Post t := b.1.mp (equal.symm.trans (a.1.mpr postL))
      exact (GeneralRebaseDepthPhase286.exclusive preR wrong).elim
    · intro models
      obtain ⟨m,valid,notAfter⟩ := (GeneralRebaseDepthReachableReadback286.strict_raw_filter preR postL).2
      exact (notAfter ((models m).mpr valid)).elim
  · exact ⟨fun _ m => (GeneralRebaseDepthPostQueries286.models postL m).trans
      (GeneralRebaseDepthPostQueries286.models postR m).symm,
      fun _ => (a.1.mpr postL).trans (b.1.mpr postR).symm⟩

theorem next_none_iff_post {s : State roles} {n : Nat} (path : ActualPath initial s n) :
    GeneralRebaseSourceStepDriver270.next GeneralRebaseOutputDepthSuccessor271.support (observe s) =
      none ↔ GeneralRebaseDepthPhase286.Post s := by
  have view := GeneralRebaseDepthProjectedPath286.observed_phase path
  rcases GeneralRebaseDepthPhase286.path_covered (.inl GeneralRebaseDepthPhase286.start) path with pre|post
  · rw [view.2.mpr pre]
    change GeneralRebaseOutputDepthSuccessor271.driveStep = none ↔ _
    rw [GeneralRebaseOutputDepthSuccessor271.one_step]
    constructor
    · intro eq
      cases eq
    · intro after
      exact (GeneralRebaseDepthPhase286.exclusive pre after).elim
  · rw [view.1.mpr post]
    constructor
    · exact fun _ => post
    · intro _
      cases h : GeneralRebaseSourceStepDriver270.next GeneralRebaseOutputDepthSuccessor271.support
        (GeneralRebaseStep258.done GeneralRebaseOutputDepthSuccessor271.support) with
      | none => rfl
      | some target =>
        exact (GeneralRebaseSourceStepDriver270.terminal _ target
          ((GeneralRebaseSourceStepDriver270.next_exact ..).mp h)).elim

theorem raw_halt_iff {s : State roles} {n : Nat} (path : ActualPath initial s n) :
    GeneralRebaseDepthSchedule286.Halted s ↔
      GeneralRebaseSourceStepDriver270.next GeneralRebaseOutputDepthSuccessor271.support (observe s) =
        none ∧ GeneralRebaseDepthSchedule286.Both s :=
  (GeneralRebaseDepthSchedule286.exact_terminal path).trans
    (and_congr (next_none_iff_post path).symm Iff.rfl)

theorem finished_driver_unfinished_raw :
    GeneralRebaseSourceStepDriver270.next GeneralRebaseOutputDepthSuccessor271.support
      (observe GeneralDictionaryOutputDepthInstall252.installed) = none ∧
    ¬ GeneralRebaseDepthSchedule286.Halted GeneralDictionaryOutputDepthInstall252.installed := by
  have path : ActualPath initial GeneralDictionaryOutputDepthInstall252.installed 1 :=
    .more (.empty _) GeneralDictionaryOutputDepthInstall252.step
  exact ⟨(next_none_iff_post path).mpr GeneralRebaseDepthPhase286.installed_post,
    fun stops => stops _ GeneralRebaseDepthScalar285.actual_silent_refresh⟩

end Yulang.GeneralRebaseDepthSemanticTransitions286
