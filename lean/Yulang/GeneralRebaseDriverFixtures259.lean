import Yulang.GeneralRebaseClosedObserver259
namespace Yulang.GeneralRebaseDriverFixtures259
open GeneralRebaseStep258 GeneralRebaseScheduler259 GeneralRebaseSettle259

theorem loose_closed (n : Nat) : GeneralRebaseClosedObserver259.Closed (GeneralDictionaryObservedRebase259.observeAt n) := by
 intro state proposal member
 rw [GeneralDictionaryObservedRebase259.observed_exact] at member
 have same : proposal = GeneralDictionaryRebaseStep258.facts := by simpa [GeneralDictionaryRebaseStep258.observe] using member
 subst proposal; exact fun _ member => member

theorem version_closed (n : Nat) : GeneralRebaseClosedObserver259.Closed (GeneralVersionRebaseStep259.observeAt n) := by
 intro state proposal member
 have same : proposal = GeneralVersionRebaseStep259.facts := by
   simpa only [GeneralVersionRebaseStep259.observe_exact,List.mem_singleton] using member
 subst proposal; exact fun _ member => member

theorem loose_next (n : Nat) (state : State GeneralDictionaryRebaseStep258.facts) :
 next (GeneralDictionaryObservedRebase259.observeAt n) state = .ok (GeneralDictionaryRebaseCurrent259.run state) := by
 rw [next,GeneralDictionaryObservedRebase259.observed_exact]
 change scan state [GeneralDictionaryRebaseStep258.facts] = _
 unfold scan
 rw [GeneralRebaseCheckedWrite259.supported state _ (fun _ member => member)]
 rw [GeneralDictionaryRebaseCurrent259.run,GeneralDictionaryRebaseRun259.run_exact]
 cases tryWrite state GeneralDictionaryRebaseStep258.facts <;> rfl

theorem version_next (n : Nat) (state : State GeneralVersionRebaseStep259.facts) :
 next (GeneralVersionRebaseStep259.observeAt n) state = .ok (GeneralVersionRebaseStep259.run state) := by
 rw [next,GeneralVersionRebaseStep259.observe_exact]
 change scan state [GeneralVersionRebaseStep259.facts] = _
 unfold scan
 rw [GeneralRebaseCheckedWrite259.supported state _ (fun _ member => member),GeneralVersionRebaseStep259.run_exact]
 cases tryWrite state GeneralVersionRebaseStep259.facts <;> rfl

theorem loose_final (n : Nat) : settle (GeneralDictionaryObservedRebase259.observeAt n)
 GeneralDictionaryRebaseStep258.finalState = .ok GeneralDictionaryRebaseStep258.finalState := by
 rw [settle,loose_next,GeneralDictionaryRebaseCurrent259.stops]

theorem loose_initial (n : Nat) : settle (GeneralDictionaryObservedRebase259.observeAt n)
 GeneralDictionaryRebaseStep258.initialState = .ok GeneralDictionaryRebaseStep258.finalState := by
 rw [settle,loose_next,GeneralDictionaryRebaseCurrent259.first]
 exact loose_final n

theorem version_final (n : Nat) : settle (GeneralVersionRebaseStep259.observeAt n)
 GeneralVersionRebaseStep259.finalState = .ok GeneralVersionRebaseStep259.finalState := by
 rw [settle,version_next,GeneralVersionRebaseStep259.run_stop]

theorem version_initial (n : Nat) : settle (GeneralVersionRebaseStep259.observeAt n)
 GeneralVersionRebaseStep259.initialState = .ok GeneralVersionRebaseStep259.finalState := by
 rw [settle,version_next,GeneralVersionRebaseStep259.run_first]
 exact version_final n

/-- A noop first proposal must not hide a later genuinely new proposal. -/
theorem skip_noop : scan GeneralVersionRebaseStep259.initialState [[],GeneralVersionRebaseStep259.facts] =
 .ok (some GeneralVersionRebaseStep259.finalState) := by
 change GeneralRebaseCheckedWrite259.commit GeneralVersionRebaseStep259.initialState GeneralVersionRebaseStep259.facts = _
 rw [GeneralRebaseCheckedWrite259.supported _ _ (fun _ member => member)]
 exact congrArg Except.ok ((GeneralVersionRebaseStep259.run_exact _).symm.trans GeneralVersionRebaseStep259.run_first)
end Yulang.GeneralRebaseDriverFixtures259
