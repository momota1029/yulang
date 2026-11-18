import Yulang.GeneralRebaseSelectedRegression262

namespace Yulang.GeneralRebaseSelectedUnused262
open GeneralRebaseStep258
open GeneralRebaseSelectedRegression262 (fixed candidates unused good_ready)
open GeneralRebaseMergeRequests261 (outputs)
open GeneralNominalCenteredHeadAllocMergeState (stage)
open GeneralNominalCenteredHeadAllocMergeConflict (focus)
open GeneralRebaseSelectedSettle262 (Current run)

abbrev proposal := GeneralRebaseStableClass261.facts fixed 38 outputs
abbrev observe := GeneralRebaseObservedPlan262.observe fixed 38 candidates
 (fun _ => (stage []).core) (fun _ => [focus]) (fun _ _ => fixed)

theorem supported : proposal ⊆ GeneralRebaseStableClass261.facts fixed 38 candidates :=
 GeneralRebaseStableClass261.monotone fixed 38 outputs candidates (fun _ member => List.mem_append_left _ member)

theorem next_exact (state : Current fixed 38 candidates) :
 GeneralRebaseScheduler259.next observe state = .ok (tryWrite state proposal) := by
 change GeneralRebaseScheduler259.scan state
   [GeneralRebaseStableClass261.facts fixed 38 (GeneralRebaseExecutableRequests262.requests (stage []).core focus)] = _
 rw [GeneralRebaseAliasRegression262.actual_requests]
 unfold GeneralRebaseScheduler259.scan
 rw [GeneralRebaseCheckedWrite259.supported state _ supported]
 cases tryWrite state proposal <;> rfl

theorem next_written (state : Current fixed 38 candidates) :
 GeneralRebaseScheduler259.next observe (write state proposal) = .ok none := by
 rw [next_exact]
 simp [tryWrite,GeneralRebaseBudget258.idempotent]

/-- A nonempty actual selection finishes in at most one write even though
its fixed pool contains an unselected missing body. -/
theorem run_exact (state : Current fixed 38 candidates) :
 run fixed 38 candidates (fun _ => (stage []).core) (fun _ => [focus]) (fun _ _ => fixed) state =
 .ok (write state proposal) := by
 by_cases unchanged : (write state proposal).remaining = state.remaining
 · have same := state_ext (write state proposal) state unchanged
   have stopped : GeneralRebaseScheduler259.next observe state = .ok none := by
     rw [next_exact]
     simp only [tryWrite,unchanged,ite_true]
   rw [same]
   exact GeneralRebaseSelectedSettle262.trace_success _ _ _ _ _ _ (.done good_ready stopped)
 · have advanced : GeneralRebaseScheduler259.next observe state = .ok (some (write state proposal)) := by
     rw [next_exact]
     simp only [tryWrite,unchanged,ite_false]
   exact GeneralRebaseSelectedSettle262.trace_success _ _ _ _ _ _
     (.next good_ready advanced (.done good_ready (next_written state)))

theorem unused_not_requested : unused ∉ outputs := by
 intro member
 rcases List.mem_cons.mp member with same | member
 · have names := congrArg GeneralSourceState.Output.name same
   cases names
 · have names := congrArg GeneralSourceState.Output.name (List.mem_singleton.mp member)
   cases names

theorem unused_pair_outside : GeneralRebasePairKeys261.key 38 unused unused ∉ proposal := by
 intro member
 rcases List.mem_append.mp member with body | pair
 · obtain ⟨output,_,inside⟩ := (GeneralRebaseBodyTable261.member ..).mp body
   exact GeneralRebaseStableBody261.pair_outside fixed 38 unused unused output inside
 · obtain ⟨first,member,last,_,_,same⟩ := (GeneralRebasePairKeys261.member ..).mp pair
   have equal := (GeneralRebasePairKeys261.key_injective same).2.1
   exact unused_not_requested (equal ▸ member)

theorem unused_pair_retained : GeneralRebasePairKeys261.key 38 unused unused ∈
 (write (initial (GeneralRebaseStableClass261.facts fixed 38 candidates)) proposal).remaining := by
 apply List.mem_filter.mpr
 constructor
 · apply List.mem_append_right
   exact (GeneralRebasePairKeys261.member ..).mpr
     ⟨unused,List.mem_append_right _ (List.mem_singleton_self _),
      unused,List.mem_append_right _ (List.mem_singleton_self _),rfl,rfl⟩
 · simpa using unused_pair_outside

/-- This is not merely the empty-selection case: actual valid requests are
processed, while an unused unknown candidate's own fact remains untouched. -/
theorem nonempty_success :
 ∃ final : Current fixed 38 candidates,
 run fixed 38 candidates (fun _ => (stage []).core) (fun _ => [focus]) (fun _ _ => fixed)
   (initial (GeneralRebaseStableClass261.facts fixed 38 candidates)) = .ok final ∧
 GeneralRebasePairKeys261.key 38 unused unused ∈ final.remaining :=
 ⟨_,run_exact _,unused_pair_retained⟩
end Yulang.GeneralRebaseSelectedUnused262
