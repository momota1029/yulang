import Yulang.GeneralRebaseDepthScheduleWord286

/-! Exact reachable raw Known frontier and the two possible maximal lengths.
Even when stable, the nested output is semantic but not raw Known. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseDepthExactEnd286
open GeneralDictionaryOutputDepth252 (roles root registry initial)
open GeneralDictionaryOutputDepthInstall252 (installed)
open GeneralRebaseDepthPathAnchor285 (snapshot)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralRebaseDepthPhase286 (Hop InstallHop)
open GeneralRebaseDepthSchedule286 (Halted exact_terminal halt_of_done)
open GeneralRebaseDepthFullTrace286 (RefreshTrace)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalState (Known)

theorem known_initial_small {n : Nat} (seen : Known (snapshot initial) n) : n ≤ 2 := by
  obtain ⟨slot,whereAt,head|⟨d,nominal⟩⟩ := seen
  · exact (head rfl).elim
  · let i : Fin 4 := slot
    have found : (if i = 2 then some GeneralDictionaryOutputDepth252.foo else none) = some d := nominal
    split at found
    · rename_i eq
      have number : i.val = 2 := congrArg Fin.val eq
      change i.val = n at whereAt
      omega
    · cases found

theorem known_small_at_refresh {s t : State roles}
    (phase : GeneralRebaseDepthPhase286.Covered s)
    (before : ∀ n, Known (snapshot s) n → n ≤ 2) (move : Hop s t) :
    ∀ n, Known (snapshot t) n → n ≤ 2 := by
  intro n recognized
  by_cases old : Known (snapshot s) n
  · exact before n old
  cases move with
  | refresh ctx cert _ _ _ _ =>
    rcases phase with pre|post
    · have result := GeneralRebaseDepthPreAnchor286.novel_position pre.anchor ctx cert n old recognized
      omega
    · have result := GeneralRebaseDepthPathAnchor285.fresh_position post.anchor ctx cert n old recognized
      omega

theorem known_small {s : State roles} {n : Nat} (path : ActualPath initial s n) :
    ∀ i, Known (snapshot s) i → i ≤ 2 := by
  induction path with
  | empty => exact fun _ seen => known_initial_small seen
  | more earlier h ih =>
    have phase := GeneralRebaseDepthPhase286.path_covered (.inl GeneralRebaseDepthPhase286.start) earlier
    rcases phase with pre|post
    · rcases GeneralRebaseDepthPhase286.pre_partition pre h with go|execute
      · exact known_small_at_refresh (.inl pre) ih go
      · exact fun i k => ih i ((GeneralRebaseDepthSchedule286.known_same_on_install pre execute i).mp k)
    · exact known_small_at_refresh (.inr post) ih (GeneralRebaseDepthPhase286.post_step post h)

theorem exact_terminal_known {s : State roles} {steps : Nat}
    (path : ActualPath initial s steps) (halted : Halted s) (i : Nat) :
    Known (snapshot s) i ↔ i = 0 ∨ i = 1 ∨ i = 2 := by
  have terminal := (exact_terminal path).mp halted
  constructor
  · intro k
    have below := known_small path i k
    omega
  · rintro (rfl | rfl | rfl)
    · exact terminal.2.1
    · exact terminal.2.2
    · obtain ⟨slot,whereAt,d,seen⟩ := terminal.1.anchor.nominal_two
      exact ⟨slot,whereAt,Or.inr ⟨d,seen⟩⟩

theorem no_short {s : State roles} {n : Nat} (path : ActualPath initial s n)
    (halted : Halted s) : 2 ≤ n := by
  obtain ⟨before,middle,first,last,pre,install,post,number⟩ :=
    (GeneralRebaseDepthFullTrace286.maximal_crosses path halted).trace
  apply Classical.byContradiction
  intro short
  have preZero : first = 0 := by omega
  have postZero : last = 0 := by omega
  subst first; subst last
  cases pre
  cases post
  exact GeneralRebaseDepthPreSharp286.previously_unknown 0 (by decide)
    ((GeneralRebaseDepthSchedule286.known_same_on_install GeneralRebaseDepthPhase286.start install 0).mp
      ((exact_terminal path).mp halted).2.1)

theorem maximal_lengths {s : State roles} {n : Nat} (path : ActualPath initial s n)
    (halted : Halted s) : n = 2 ∨ n = 3 := by
  have lower := no_short path halted
  have upper := GeneralRebaseDepthFullRank286.complete_bound path
  omega

theorem short_maximal :
    ActualPath initial GeneralRebaseDepthScalar285.refreshed 2 ∧
      Halted GeneralRebaseDepthScalar285.refreshed := by
  have first : ActualPath initial installed 1 := .more (.empty _) GeneralDictionaryOutputDepthInstall252.step
  have path : ActualPath initial GeneralRebaseDepthScalar285.refreshed 2 :=
    .more first GeneralRebaseDepthScalar285.actual_silent_refresh
  have after := GeneralRebaseDepthPhase286.post_refresh GeneralRebaseDepthPhase286.installed_post
    (.refresh GeneralRebaseDepthScalar285.target GeneralRebaseDepthScalar285.cert 0
      (GeneralRebaseDepthScalar285.present 0 (by decide))
      (GeneralRebaseDepthScalar285.previously_unknown 0 (by decide)) GeneralRebaseDepthScalar285.new_zero)
  exact ⟨path,halt_of_done after ⟨GeneralRebaseDepthScalar285.new_zero,GeneralRebaseDepthScalar285.new_one⟩⟩

theorem output_gap {s : State roles} {n : Nat} (path : ActualPath initial s n) (halted : Halted s) :
    (¬ Known (snapshot s) 3) ∧
      ∀ model, GeneralNominalVersionedJournal232.Models s model →
        CommonNominalFullCarrier.Equivalent (model 3).1 GeneralDictionaryOutputDepth252.P := by
  refine ⟨fun marked => by simpa using (exact_terminal_known path halted 3).mp marked,?_⟩
  intro m valid
  exact ((GeneralRebaseDepthPostQueries286.models ((exact_terminal path).mp halted).1 m).mp valid).2

end Yulang.GeneralRebaseDepthExactEnd286
