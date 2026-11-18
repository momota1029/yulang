import Yulang.GeneralRebaseMergeObservation261
namespace Yulang.GeneralRebaseStableMergeDriver261
open GeneralRebaseStep258
open GeneralNominalCenteredHeadAllocMergeState
open GeneralNominalCenteredHeadAllocMergeConflict (focus)
open GeneralRebaseMergeRequests261 (candidate outputs)
open GeneralRebaseStableMerge261 (facts initialState finalState)

noncomputable def proposal (fixed observed) := GeneralRebaseStableClass261.facts (candidate fixed) 38
 (GeneralNominalCenteredHeadOutputs.requests (stage observed).core focus)

theorem membership (fixed observed) (fact : Fact) : fact ∈ proposal fixed observed ↔ fact ∈ facts fixed :=
 GeneralRebaseStableClass261.reordered _ _ _ _ (GeneralRebaseMergeRequests261.requests_exact observed) fact

theorem write_full (atoms) (state : State (facts atoms)) : write state (facts atoms) = finalState atoms := by
 apply state_ext
 apply List.eq_nil_iff_forall_not_mem.mpr
 intro fact member
 obtain ⟨inside,outside⟩ := List.mem_filter.mp member
 have belongs := state.canonical.subset inside
 simp [belongs] at outside

theorem write_actual (fixed observed) (state : State (facts fixed)) :
 write state (proposal fixed observed) = finalState fixed :=
 (GeneralRebaseBatchOrder259.write_membership state _ _ (membership fixed observed)).trans (write_full fixed state)

theorem try_actual (fixed observed) (state : State (facts fixed)) :
 tryWrite state (proposal fixed observed) = tryWrite state (facts fixed) := by
 unfold tryWrite
 rw [write_actual,write_full]

noncomputable def run (fixed) (inspect : State (facts fixed) → List (PresenceNormalForm.Atom Nat))
 (state : State (facts fixed)) := GeneralRebaseCheckedWrite259.commit state (proposal fixed (inspect state))

/-- Exact executable representative of this stage-independent fixture runner.
No arbitrary source inspection algorithm is extracted by this equality. -/
def executable (fixed) (state : State (facts fixed)) : Except (List Fact) (Option (State (facts fixed))) :=
 .ok (tryWrite state (facts fixed))

theorem run_exact (fixed) (inspect) (state : State (facts fixed)) : run fixed inspect state = executable fixed state := by
 unfold run executable
 rw [GeneralRebaseCheckedWrite259.supported state _ (fun fact member => (membership fixed (inspect state) fact).mp member)]
 rw [try_actual]

theorem function_exact (fixed) (inspect) : run fixed inspect = executable fixed := by
 funext state; exact run_exact fixed inspect state

theorem first (fixed) (inspect) : run fixed inspect (initialState fixed) = .ok (some (finalState fixed)) := by
 rw [run_exact]
 unfold executable tryWrite
 rw [write_full]
 have different : (finalState fixed).remaining ≠ (initialState fixed).remaining := by
   intro same
   have length := congrArg List.length same
   change 0 = 6 at length
   cases length
 simp [different]

theorem stops (fixed) (inspect) : run fixed inspect (finalState fixed) = .ok none := by
 rw [run_exact]
 simp [executable,tryWrite,write_full]

noncomputable abbrev observe (fixed) (inspect) := GeneralRebaseCandidateDriver261.observe (candidate fixed) 38 outputs
 (GeneralRebaseStableMerge261.select fixed inspect)

theorem step_final (fixed) (inspect) (before after : State (facts fixed))
 (step : Step (observe fixed inspect) before after) : after = finalState fixed := by
 obtain ⟨p,member,same,_⟩ := step
 have eq : p = proposal fixed (inspect before) := by simpa [observe,GeneralRebaseCandidateDriver261.observe,GeneralRebaseStableMerge261.select,proposal] using member
 subst p
 exact same.trans (write_actual fixed (inspect before) before)

theorem no_step_final (fixed) (inspect) (after : State (facts fixed)) :
 ¬ Step (observe fixed inspect) (finalState fixed) after := by
 intro step
 have same := step_final fixed inspect _ _ step
 obtain ⟨_,_,_,different⟩ := step
 exact different (congrArg State.remaining same)

theorem budget (fixed) (inspect) {n after}
 (run : GeneralRebaseBudget258.Runs (observe fixed inspect) n (initialState fixed) after) : n ≤ 1 := by
 cases run with
 | nil => omega
 | next step rest =>
   have same := step_final fixed inspect _ _ step
   subst_vars
   cases rest with
   | nil => omega
   | next step _ => exact False.elim (no_step_final fixed inspect _ step)
end Yulang.GeneralRebaseStableMergeDriver261
