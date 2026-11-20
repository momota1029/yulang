import Yulang.GeneralObservedLadderLedger301

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 7000000
namespace Yulang.GeneralObservedLadderStage301
open GeneralObservedLadderSource301 (snapshot)
open GeneralObservedLadderInitial301 (context)
open GeneralObservedLadderReport301
open GeneralObservedLadderPlan301
open GeneralObservedLadderRoute301
open GeneralObservedLadderLedger301
open GeneralDeclarationExamples (roles display display_checked displayChild)
open GeneralNominalExamples (intDisplay)
open GeneralNominalOutputGrowth (finiteModel)
open GeneralNominalVersionedCandidates231
open GeneralNominalVersionedFrame231 (children)
open GeneralNominalRecursiveCandidates (arguments report Metadata)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalRecursiveInspection (Finished)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCenters (Site)

theorem model (p : Phase n k) : GeneralNominalVersionedJournal232.Models p.state (finiteModel n) :=
  (p.models _).mpr (GeneralObservedLadderInitial301.models n)

theorem metadata (p : Phase n k) : Metadata compiled (env p) :=
  GeneralObservedLadderSelection301.metadata n

theorem located (p : Phase n k) (bound : k ≤ n+1) :
    arguments (env p) (inputs (focus n k)) = some [point n k bound] :=
  GeneralObservedLadderSelection301.located n k (invocation n k) bound

theorem linked (p : Phase n k) (bound : k ≤ n+1) :
    GeneralNominalState.Linked (env p).state (inputs (focus n k)).demand := by
  constructor
  · intro _
    have seen := GeneralNominalAllocationSupport.slot_source (env p).state (pos n k bound)
    exact ⟨seen,seen⟩
  · intro _ impossible; cases impossible

theorem known (p : Phase n k) (bound : k ≤ n+1) :
    ¬ GeneralNominalState.RootPending (env p).state (inputs (focus n k)).demand :=
  GeneralObservedLadderSelection301.known n k (invocation n k) bound

theorem finished_iff (p : Phase n k) (d : GeneralDeclarations.Declaration) (bound : k ≤ n+1) :
    Finished (report (env p) d [point n k bound]) ↔ Finished (report (context n) d [point n k bound]) := by
  rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended]
  rfl

theorem list_prepared (p : Phase n k) (hi : k ≤ n) :
    Prepared compiled (env p) (focus n k) display := by
  refine ⟨metadata p,linked p (by omega),[point n k (by omega)],located p (by omega),fresh p _,?_,
    finiteModel n,?_⟩
  · exact (finished_iff p display (by omega)).mpr ((exact_at n k (by omega)).1.mpr hi)
  · exact GeneralNominalVersionedPlans231.head_models (stage_held p hi _ (model p))

theorem wrong_list (p : Phase n (n+1)) : Failed compiled (env p) (focus n (n+1)) display := by
  refine ⟨metadata p,[point n (n+1) (Nat.le_refl _)],located p (Nat.le_refl _),fresh p _,?_,?_,.inl ?_⟩
  all_goals rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,int_as_list]
  all_goals try rfl
  intro opposite
  cases opposite

theorem wrong_int (p : Phase n k) (hi : k ≤ n) : Failed compiled (env p) (focus n k) intDisplay := by
  refine ⟨metadata p,[point n k (by omega)],located p (by omega),fresh p _,?_,?_,.inl ?_⟩
  all_goals rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,list_as_int n k hi]
  all_goals try rfl
  intro opposite
  cases opposite

theorem no_int (p : Phase n k) (hi : k ≤ n) : ¬ Prepared compiled (env p) (focus n k) intDisplay := by
  rintro ⟨_,_,bs,matching,_,done,_⟩
  cases Option.some.inj (matching.symm.trans (located p (by omega)))
  have last := (exact_at n k (by omega)).2.mp ((finished_iff p _ (by omega)).mp done)
  omega

theorem no_list (p : Phase n (n+1)) : ¬ Prepared compiled (env p) (focus n (n+1)) display := by
  rintro ⟨_,_,bs,matching,_,done,_⟩
  cases Option.some.inj (matching.symm.trans (located p (Nat.le_refl _)))
  have short := (exact_at n (n+1) (Nat.le_refl _)).1.mp ((finished_iff p _ (Nat.le_refl _)).mp done)
  omega

theorem stage_emits (p : Phase n k) (hi : k ≤ n) :
    GeneralNominalVersionedChildren232.emitted (stagePlan p hi) = [site n (k+1)] := by
  let s := GeneralNominalVersionedFrame231.childSite (stagePlan p hi) displayChild
    (display_checked.signature.2.2.2 _ (by simp))
  have one : (GeneralNominalVersionedChildren232.emitted (stagePlan p hi)).length = 1 :=
    GeneralNominalVersionedChildren232.emitted_length _
  have occurs : s ∈ GeneralNominalVersionedChildren232.emitted (stagePlan p hi) := by
    unfold GeneralNominalVersionedChildren232.emitted
    have member : displayChild ∈ GeneralCanonicalChildOrder.canonicalRequirements
        (stagePlan p hi).packet.declaration.requirements :=
      (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mp (List.mem_singleton_self _)
    exact List.mem_map.mpr ⟨⟨_,member⟩,List.mem_attach _ _,rfl⟩
  obtain ⟨oneSite,eq⟩ := List.length_eq_one_iff.mp one
  rw [eq] at occurs ⊢
  rw [← List.mem_singleton.mp occurs]
  have exactSite : s = child n k (invocation n k) hi := GeneralNominalVersionedTransport231.childSite_eq .. 
  rw [exactSite,child_site]

theorem stage_children (p : Phase n k) (hi : k ≤ n) :
    children (stagePlan p hi).packet = [focus n (k+1)] := by
  rw [← GeneralNominalVersionedChildren232.emitted_occurrences (stagePlan p hi),stage_emits]
  rfl

theorem unique (p : Phase n k) (hi : k ≤ n) :
    Unique compiled (env p) (focus n k) 1 [focus n (k+1)] := by
  have chosen : Survivor compiled (env p) (focus n k) 1 [focus n (k+1)] :=
    ⟨known p (by omega),display,List.mem_cons_of_mem _ (List.mem_cons_self ..),display_checked,
      rfl,rfl,[point n k (by omega)],located p (by omega),list_prepared p hi,(stage_children p hi).symm⟩
  refine ⟨chosen,?_⟩
  intro key kids other
  have kept := other
  obtain ⟨_,d,visible,_,eq,role,_,_,ready,_⟩ := other
  rcases GeneralRebaseCompiledDisplay277.compiled_members visible role with rfl|rfl
  · exact False.elim (no_int p hi ready)
  · subst key
    exact ⟨rfl,survivor_children_functional GeneralRebaseCompiledDisplay277.compiled_checked kept chosen⟩

theorem center_recorded (p : Phase n k) : site n k ∈ p.state.core.sites := by
  rw [p.centers_eq]
  exact (sites_exact ..).mpr ⟨k,Nat.le_refl _,rfl⟩

theorem raw_recorded (p : Phase n k) : GeneralNominalDemandMerging.pointSite (focus n k) ∈
    p.state.core.erased.current.sites := by
  rw [p.raw_eq,← observed n k]
  exact List.mem_map.mpr ⟨site n k,(sites_exact ..).mpr ⟨k,Nat.le_refl _,rfl⟩,rfl⟩

theorem frame (p : Phase n k) (hi : k ≤ n) :
    Frame compiled p.state.core (focus n k) 1 (stagePlan p hi) := by
  refine ⟨rfl,p.context_eq.symm,rfl,rfl,raw_recorded p,center_recorded p,
    List.mem_cons_of_mem _ (List.mem_cons_self ..),rfl,located p (by omega),?_⟩
  rw [p.context_eq]
  exact list_prepared p hi

theorem raw_is (p : Phase n k) (s : GeneralNominalDemandMerging.Site roles)
    (member : s ∈ p.state.core.erased.current.sites) (eq : s.occurrence = focus n i) :
    s = GeneralNominalDemandMerging.pointSite (focus n i) := by
  rw [p.raw_eq] at member
  obtain ⟨origin,prior,rfl⟩ := List.mem_map.mp member
  rw [unique_row n k i origin prior eq,observed]

theorem current_requests (p : Phase n k) (focus : Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.requests p.state.core focus = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output member
  obtain ⟨row,listed,_,listedOutput⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  rw [p.raw_eq] at listed
  obtain ⟨center,seen,rfl⟩ := List.mem_map.mp listed
  obtain ⟨i,_,rfl⟩ := (sites_exact ..).mp seen
  cases listedOutput

end Yulang.GeneralObservedLadderStage301
