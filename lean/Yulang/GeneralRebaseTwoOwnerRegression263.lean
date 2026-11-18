import Yulang.GeneralRebaseMultiTrace263
import Yulang.GeneralRebaseAliasRegression262

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralRebaseTwoOwnerRegression263
open GeneralNominalCenters GeneralRebaseStep258
open GeneralNominalCenteredHeadAllocMergeSource (roles registry)
open GeneralNominalCenteredHeadAllocMergeInstall (aSite bSite aTarget)
open GeneralNominalCenteredHeadAllocMergeState (stage child_ids_distinct)
open GeneralNominalCenteredHeadAllocMergeConflict (chosen chosen_checked current)
open GeneralRebaseMergeRequests261 (outputs)
open GeneralRebaseMultiSelection263 (Selection ofPlan)

abbrev firstPlan : Plan roles := GeneralRebaseMergeRequests261.candidate []
abbrev lastPacket : GeneralNominalSaturationState.Packet roles :=
 ⟨registry,current [],bSite.observed,chosen,chosen_checked,[]⟩
abbrev lastPlan : Plan roles := ⟨lastPacket,bSite,rfl⟩
def first : Selection roles := ofPlan firstPlan
def last : Selection roles := ofPlan lastPlan

theorem owners_distinct : first.owner ≠ last.owner := by
 intro same
 have equal : (aSite.occurrence.identity,38) = (bSite.occurrence.identity,38) := GeneralNominalIdentities.pair_injective same
 exact child_ids_distinct (congrArg Prod.fst equal)

def owners := [first.owner,last.owner]
def representative (owner : Nat) : Plan roles := if owner = first.owner then firstPlan else lastPlan

theorem rep_first : representative first.owner = firstPlan := by simp [representative]
theorem rep_last : representative last.owner = lastPlan := by simp [representative,Ne.symm owners_distinct]

def pool := outputs
abbrev Current := GeneralRebaseMultiObserver263.Current owners representative pool
def inspect (_ : Current) := (stage []).core
def select (_ : Current) := [first,last]
def observe := GeneralRebaseMultiObserver263.observe owners representative pool inspect select
abbrev p := GeneralRebaseStableClass261.facts firstPlan first.owner outputs
abbrev q := GeneralRebaseStableClass261.facts lastPlan last.owner outputs

theorem first_requests : GeneralRebaseMultiSelection263.requests (stage []).core first = outputs :=
 GeneralRebaseAliasRegression262.actual_requests []
theorem last_requests : GeneralRebaseMultiSelection263.requests (stage []).core last = outputs := by
 unfold GeneralRebaseMultiSelection263.requests GeneralRebaseExecutableRequests262.requests
 dsimp only
 change ((stage []).core.erased.current.sites.filter fun site =>
   GeneralFiniteAliasSearch262.connected (stage []).core.erased.current.aliases
     bSite.occurrence.identity site.occurrence.identity).flatMap (fun site => site.occurrence.demand.outputs) = outputs
 have same : (fun site : GeneralNominalDemandMerging.Site roles =>
   GeneralFiniteAliasSearch262.connected (stage []).core.erased.current.aliases bSite.occurrence.identity site.occurrence.identity) =
   (fun site => GeneralFiniteAliasClosure262.connected (stage []).core.erased.current.aliases bSite.occurrence.identity site.occurrence.identity) :=
   funext fun site => GeneralFiniteAliasSearch262.reference_eq (stage []).core.erased.current bSite.occurrence.identity site.occurrence.identity
 rw [same]
 rfl

theorem observed (state : Current) : observe state = [p,q] := by
 change [GeneralRebaseMultiSelection263.proposal (stage []).core first,
   GeneralRebaseMultiSelection263.proposal (stage []).core last] = _
 unfold GeneralRebaseMultiSelection263.proposal
 rw [first_requests,last_requests]
 rfl

theorem basis_exact : GeneralRebaseOwnerTable263.basis owners representative pool = p ++ q := by
 simp only [GeneralRebaseOwnerTable263.basis,owners,List.flatMap_cons,List.flatMap_nil,List.append_nil,rep_first,rep_last]
 rfl

theorem disjoint (fact : Fact) : ¬ (fact ∈ p ∧ fact ∈ q) :=
 GeneralRebaseOwnerTags263.tables_separate firstPlan lastPlan _ _ owners_distinct outputs outputs fact

theorem p_nonempty : p ≠ [] := by
 intro empty
 have member : GeneralRebasePairKeys261.key first.owner ⟨0,aTarget⟩ ⟨0,aTarget⟩ ∈ p :=
  List.mem_append_right _ ((GeneralRebasePairKeys261.member ..).mpr
    ⟨_,List.mem_cons_self,_,List.mem_cons_self,rfl,rfl⟩)
 rw [empty] at member
 cases member

theorem q_nonempty : q ≠ [] := by
 intro empty
 have member : GeneralRebasePairKeys261.key last.owner ⟨0,aTarget⟩ ⟨0,aTarget⟩ ∈ q :=
  List.mem_append_right _ ((GeneralRebasePairKeys261.member ..).mpr
    ⟨_,List.mem_cons_self,_,List.mem_cons_self,rfl,rfl⟩)
 rw [empty] at member
 cases member

theorem checked (state : Current) : GeneralRebaseMultiRun263.validate owners representative pool inspect select state = .ok () := by
 apply (GeneralRebaseMultiSelection263.check_exact _ _).mpr
 intro entry member
 change entry ∈ [first,last] at member
 rcases List.mem_cons.mp member with rfl | member
 · change GeneralRebaseClassCheck261.Ready firstPlan (GeneralRebaseMultiSelection263.requests (stage []).core first)
   rw [first_requests]
   exact GeneralRebaseMergeRequests261.ready []
 · cases List.mem_singleton.mp member
   change GeneralRebaseClassCheck261.Ready lastPlan (GeneralRebaseMultiSelection263.requests (stage []).core last)
   rw [last_requests]
   intro output member
   rcases List.mem_cons.mp member with rfl | member
   · rfl
   · cases List.mem_singleton.mp member
     rfl

abbrev start : Current := initial (GeneralRebaseOwnerTable263.basis owners representative pool)
abbrev middle : Current := write start p
abbrev finish : Current := write middle q

theorem middle_remaining : middle.remaining = q := by
 change (GeneralRebaseOwnerTable263.basis owners representative pool).filter (fun fact => !p.contains fact) = q
 rw [basis_exact,List.filter_append]
 have left : p.filter (fun fact => !p.contains fact) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro fact member
  simp [member]
 have right : q.filter (fun fact => !p.contains fact) = q := by
  apply List.filter_eq_self.mpr
  intro fact member
  have outside : fact ∉ p := fun found => disjoint fact ⟨found,member⟩
  simp [outside]
 rw [left,right,List.nil_append]

theorem finish_remaining : finish.remaining = [] := by
 change middle.remaining.filter (fun fact => !q.contains fact) = []
 rw [middle_remaining]
 apply List.filter_eq_nil_iff.mpr
 intro fact member
 simp [member]

theorem first_progress : middle.remaining ≠ start.remaining := by
 rw [middle_remaining]
 change q ≠ GeneralRebaseOwnerTable263.basis owners representative pool
 rw [basis_exact]
 intro same
 have lengths := congrArg List.length same
 have empty : p.length = 0 := by simp only [List.length_append] at lengths; omega
 exact p_nonempty (List.eq_nil_of_length_eq_zero empty)

theorem last_progress : finish.remaining ≠ middle.remaining := by
 rw [finish_remaining,middle_remaining]
 exact Ne.symm q_nonempty

private theorem supported_p : p ⊆ GeneralRebaseOwnerTable263.basis owners representative pool := by
 rw [basis_exact]; exact fun _ member => List.mem_append_left _ member
private theorem supported_q : q ⊆ GeneralRebaseOwnerTable263.basis owners representative pool := by
 rw [basis_exact]; exact fun _ member => List.mem_append_right _ member

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

theorem terminal : GeneralRebaseScheduler259.next observe finish = .ok none := by
 apply (GeneralRebaseScheduler259.scan_none finish _).mpr
 intro proposal member
 change proposal ∈ observe finish at member
 rw [observed] at member
 have support : proposal ⊆ GeneralRebaseOwnerTable263.basis owners representative pool := by
  rcases List.mem_cons.mp member with rfl | member
  · exact supported_p
  · cases List.mem_singleton.mp member; exact supported_q
 rw [GeneralRebaseCheckedWrite259.supported finish proposal support]
 have noop : (write finish proposal).remaining = finish.remaining := by
  change finish.remaining.filter (fun fact => !proposal.contains fact) = finish.remaining
  rw [finish_remaining]; rfl
 simp [tryWrite,noop]

theorem checked_trace : GeneralRebaseValidatedDriver263.Trace observe
 (GeneralRebaseMultiRun263.validate owners representative pool inspect select) [start,middle] start finish :=
 .next (checked start) first_advance (.next (checked middle) last_advance (.done (checked finish) terminal))

theorem run_success : GeneralRebaseMultiRun263.run owners representative pool inspect select start = .ok finish :=
 GeneralRebaseValidatedDriver263.trace_success _ _ checked_trace

theorem exactly_two_writes : GeneralRebaseBudget258.Runs observe 2 start finish :=
 GeneralRebaseValidatedDriver263.to_runs _ _ checked_trace


/-- Both writes retain their actual snapshot, root, and own Plan. -/
theorem event_trace : GeneralRebaseMultiTrace263.Trace owners representative pool inspect select
 [⟨(stage []).core,first⟩,⟨(stage []).core,last⟩] start finish := by
 refine .next (middle := middle) List.mem_cons_self ?_ first_progress ?_
 · change middle = write start (GeneralRebaseStableClass261.facts firstPlan first.owner
     (GeneralRebaseMultiSelection263.requests (stage []).core first))
   rw [first_requests]
 refine .next (middle := finish) (List.mem_cons_of_mem _ (List.mem_singleton_self _)) ?_ last_progress (.nil finish)
 change finish = write middle (GeneralRebaseStableClass261.facts lastPlan last.owner
   (GeneralRebaseMultiSelection263.requests (stage []).core last))
 rw [last_requests]

private theorem effects_actual (selected : Selection roles)
 (requests : GeneralRebaseMultiSelection263.requests (stage []).core selected = outputs)
 (assignment : GeneralNominalCommonBridge.Assignment) :
 GeneralRebaseClassTable261.Effects selected.plan outputs assignment ↔
 GeneralNominalVersionedEffects231.ClassEffects (stage []).core selected.root selected.plan assignment := by
 have exactRequests : GeneralNominalCenteredHeadOutputs.requests (stage []).core selected.root = outputs := by
  rw [GeneralRebaseMultiSelection263.requests,GeneralRebaseExecutableRequests262.requests_eq] at requests
  exact requests
 change GeneralRebaseClassTable261.Effects selected.plan outputs assignment ↔
   GeneralRebaseClassTable261.Effects selected.plan
     (GeneralNominalCenteredHeadOutputs.requests (stage []).core selected.root) assignment
 rw [exactRequests]

/-- Success installs constraints; it does not assert that the resulting models
exist, nor that these supplied Plans were produced by a source compiler. -/
theorem models_exact (base : GeneralNominalCommonBridge.Assignment → Prop)
 (assignment : GeneralNominalCommonBridge.Assignment) :
 GeneralRebaseOwnerTable263.Models base owners representative finish assignment ↔
 base assignment ∧
 GeneralNominalVersionedEffects231.ClassEffects (stage []).core first.root first.plan assignment ∧
 GeneralNominalVersionedEffects231.ClassEffects (stage []).core last.root last.plan assignment := by
 have finished : finish = done (GeneralRebaseOwnerTable263.basis owners representative pool) :=
   state_ext _ _ finish_remaining
 rw [finished,GeneralRebaseOwnerTable263.done_exact]
 simp only [owners,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,
   rep_first,rep_last]
 change (base assignment ∧ GeneralRebaseClassTable261.Effects first.plan outputs assignment ∧
   GeneralRebaseClassTable261.Effects last.plan outputs assignment) ↔ _
 rw [effects_actual first first_requests,effects_actual last last_requests]

end Yulang.GeneralRebaseTwoOwnerRegression263
