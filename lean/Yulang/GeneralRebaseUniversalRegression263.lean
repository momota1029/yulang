import Yulang.GeneralRebaseUniversalObserver263
import Yulang.GeneralRebaseTwoOwnerRegression263
import Yulang.GeneralRebaseSelectedUnused262
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseUniversalRegression263
open GeneralRebaseStep258
open GeneralRebaseTwoOwnerRegression263 (first last firstPlan lastPlan owners p q first_requests last_requests)
open GeneralRebaseMergeRequests261 (outputs)
open GeneralRebaseSelectedRegression262 (unused)
open GeneralNominalCenteredHeadAllocMergeState (stage)
open GeneralRebaseUniversalBasis263 (basis bodyKey)

/-- Reserve an extra named request for which the actual leaf has no body. -/
def pool := outputs ++ [unused]
abbrev Current := GeneralRebaseUniversalObserver263.Current owners pool
def inspect (_ : Current) := (stage []).core
def select (_ : Current) := [first,last]
def observe := GeneralRebaseUniversalObserver263.observe owners pool inspect select
abbrev start : Current := initial (basis owners pool)
abbrev middle : Current := write start p
abbrev finish : Current := write middle q

theorem observed (state : Current) : observe state = [p,q] := by
 change [GeneralRebaseMultiSelection263.proposal (stage []).core first,
   GeneralRebaseMultiSelection263.proposal (stage []).core last] = _
 unfold GeneralRebaseMultiSelection263.proposal
 rw [first_requests,last_requests]
 rfl

theorem supported_p : p ⊆ basis owners pool :=
 GeneralRebaseUniversalBasis263.proposal_covered owners pool firstPlan first.owner
   List.mem_cons_self outputs (fun _ member => List.mem_append_left _ member)
theorem supported_q : q ⊆ basis owners pool :=
 GeneralRebaseUniversalBasis263.proposal_covered owners pool lastPlan last.owner
   (List.mem_cons_of_mem _ (List.mem_singleton_self _)) outputs (fun _ member => List.mem_append_left _ member)

theorem checked (state : Current) : GeneralRebaseUniversalObserver263.validate owners pool inspect select state = .ok () :=
 GeneralRebaseTwoOwnerRegression263.checked GeneralRebaseTwoOwnerRegression263.start

private theorem progress {b : List Fact} (state : State b) (proposal : Proposal)
 (fact : Fact) (present : fact ∈ state.remaining) (included : fact ∈ proposal) :
 (write state proposal).remaining ≠ state.remaining := by
 intro same
 have kept : fact ∈ (write state proposal).remaining := same ▸ present
 have impossible := (List.mem_filter.mp kept).2
 simp [included] at impossible

private theorem nonempty_member (values : List Fact) (nonempty : values ≠ []) : ∃ fact, fact ∈ values := by
 cases values with
 | nil => exact False.elim (nonempty rfl)
 | cons fact rest => exact ⟨fact,List.mem_cons_self⟩

theorem first_progress : middle.remaining ≠ start.remaining := by
 obtain ⟨fact,member⟩ := nonempty_member p GeneralRebaseTwoOwnerRegression263.p_nonempty
 exact progress start p fact (supported_p member) member

theorem last_progress : finish.remaining ≠ middle.remaining := by
 obtain ⟨fact,member⟩ := nonempty_member q GeneralRebaseTwoOwnerRegression263.q_nonempty
 have retained : fact ∈ middle.remaining := by
  apply List.mem_filter.mpr
  refine ⟨supported_q member,?_⟩
  have outside : fact ∉ p := fun prior => GeneralRebaseTwoOwnerRegression263.disjoint fact ⟨prior,member⟩
  simpa using outside
 exact progress middle q fact retained member

theorem first_advance : GeneralRebaseScheduler259.next observe start = .ok (some middle) := by
 unfold GeneralRebaseScheduler259.next
 rw [observed]
 unfold GeneralRebaseScheduler259.scan
 rw [GeneralRebaseCheckedWrite259.supported start p supported_p]
 simp only [tryWrite,first_progress,ite_false]

theorem last_advance : GeneralRebaseScheduler259.next observe middle = .ok (some finish) := by
 unfold GeneralRebaseScheduler259.next
 rw [observed]
 unfold GeneralRebaseScheduler259.scan
 rw [GeneralRebaseCheckedWrite259.supported middle p supported_p,GeneralRebaseBudget258.duplicate_noop]
 change GeneralRebaseScheduler259.scan middle [q] = _
 unfold GeneralRebaseScheduler259.scan
 rw [GeneralRebaseCheckedWrite259.supported middle q supported_q]
 simp only [tryWrite,last_progress,ite_false]

private theorem write_commute {b : List Fact} (state : State b) (one two : Proposal) :
 write (write state one) two = write (write state two) one := by
 apply state_ext
 change (state.remaining.filter _).filter _ = (state.remaining.filter _).filter _
 rw [List.filter_filter,List.filter_filter]
 congr 1
 funext fact
 exact Bool.and_comm _ _

theorem terminal : GeneralRebaseScheduler259.next observe finish = .ok none := by
 apply (GeneralRebaseScheduler259.scan_none finish _).mpr
 intro proposal member
 change proposal ∈ observe finish at member
 rw [observed] at member
 rcases List.mem_cons.mp member with rfl | member
 · rw [GeneralRebaseCheckedWrite259.supported finish p supported_p]
   have unchanged : write finish p = finish := by
    change write (write (write start p) q) p = write (write start p) q
    rw [write_commute (write start p) q p,GeneralRebaseBudget258.idempotent]
   simp [tryWrite,unchanged]
 · cases List.mem_singleton.mp member
   rw [GeneralRebaseCheckedWrite259.supported finish q supported_q,GeneralRebaseBudget258.duplicate_noop]

theorem checked_trace : GeneralRebaseValidatedDriver263.Trace observe
 (GeneralRebaseUniversalObserver263.validate owners pool inspect select) [start,middle] start finish :=
 .next (checked start) first_advance (.next (checked middle) last_advance (.done (checked finish) terminal))

theorem run_success : GeneralRebaseUniversalObserver263.run owners pool inspect select start = .ok finish :=
 GeneralRebaseValidatedDriver263.trace_success _ _ checked_trace

theorem exactly_two_writes : GeneralRebaseBudget258.Runs observe 2 start finish :=
 GeneralRebaseValidatedDriver263.to_runs _ _ checked_trace

theorem reserved_present : bodyKey first.owner unused ∈ start.remaining := by
 apply List.mem_flatMap.mpr
 refine ⟨first.owner,List.mem_cons_self,?_⟩
 apply List.mem_append_left
 exact List.mem_map.mpr ⟨unused,List.mem_append_right _ (List.mem_singleton_self _),rfl⟩

theorem reserved_outside_p : bodyKey first.owner unused ∉ p := by
 intro member
 rcases List.mem_append.mp member with body | pair
 · obtain ⟨output,requested,key⟩ := (GeneralRebaseBodyTable261.member ..).mp body
   have same := GeneralRebaseUniversalBasis263.body_key_exact firstPlan first.owner output _ key
   have address := (GeneralRebaseOwnedOutputKeys260.key_identity same).1
   have codes := (GeneralRebaseRequestBodyKeys260.space_identity address).2.2
   have equal := GeneralRebaseNamedRequest260.code_injective codes
   exact GeneralRebaseSelectedUnused262.unused_not_requested (equal ▸ requested)
 · obtain ⟨one,_,two,_,_,same⟩ := (GeneralRebasePairKeys261.member ..).mp pair
   exact GeneralRebasePairKeys261.body_separate first.owner one two (GeneralRebaseNamedRequest260.code unused) 0 same.symm

theorem reserved_outside_q : bodyKey first.owner unused ∉ q := by
 intro member
 have tagged : GeneralRebaseOwnerTags263.Tagged first.owner (bodyKey first.owner unused) :=
  ⟨1,GeneralRebaseNamedRequest260.code unused,0,rfl⟩
 exact GeneralRebaseTwoOwnerRegression263.owners_distinct
   (GeneralRebaseOwnerTags263.owner_unique _ _ _ tagged (GeneralRebaseOwnerTags263.tagged lastPlan last.owner outputs _ member))

/-- An unknown reserved body is not required by the current actual selection.
It stays unwritten even though both selected owners finish successfully. -/
theorem reserved_retained : bodyKey first.owner unused ∈ finish.remaining := by
 apply List.mem_filter.mpr
 constructor
 · apply List.mem_filter.mpr
   exact ⟨reserved_present,by simpa using reserved_outside_p⟩
 · simpa using reserved_outside_q

theorem terminal_not_done : finish ≠ done (basis owners pool) := by
 intro same
 have member := reserved_retained
 rw [same] at member
 cases member

theorem unused_unknown : (GeneralRebaseBodyTable261.schema firstPlan unused).unknown = true := rfl

end Yulang.GeneralRebaseUniversalRegression263
