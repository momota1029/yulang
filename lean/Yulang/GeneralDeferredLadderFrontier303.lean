import Yulang.GeneralDeferredLadderUniversalLeaf302

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 7500000
namespace Yulang.GeneralDeferredLadderFrontier303
open GeneralDeferredLadderLedger302 (Phase)
open GeneralDeferredLadderRetargetData302 (lift listPlan list_report wrong_int intPlan scalar_report wrong_list argument_exact)
open GeneralDeferredLadderRetargetFrames302 (metadata linked list_held int_held raw_recorded center_recorded)
open GeneralObservedLadderRoute301 (focus invocation site)
open GeneralObservedLadderPlan301 (compiled)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedCandidates231 (Prepared)
open GeneralNominalRecursiveCandidates (Context)
open GeneralDeclarationExamples (roles display)
open GeneralNominalExamples (intDisplay)

theorem frontier_fresh (p : Phase n k) (ctx : Context) (cert : Refresh p.state ctx) (bs) :
    GeneralNominalVersionedAllocation231.Fresh ctx.state compiled (invocation n k) bs := by
  intro key member used
  have before := cert.support _ used
  rw [p.context_eq] at before
  rw [(lift p ctx cert).seed] at before
  exact (lift p ctx cert).allocated key (GeneralDeferredLadderLedger302.fresh p bs key member before)

theorem list_prepared (p : Phase n k) (hi : k ≤ n) (ctx : Context)
    (cert : Refresh p.state ctx) : Prepared compiled ctx (focus n k) display := by
  let m := GeneralNominalOutputGrowth.finiteModel n
  have valid : Models (refresh p.state ctx) m :=
    (GeneralNominalVersionedMixedObservations233.refresh_models cert).mpr (GeneralDeferredLadderStage302.model p)
  refine ⟨metadata p ctx cert,linked p ctx cert k (by omega),_,argument_exact p ctx cert k (by omega),
    frontier_fresh p ctx cert _,?_,m,?_⟩
  · rw [list_report p ctx cert k hi]
    exact ⟨rfl,rfl,rfl⟩
  · exact (GeneralNominalVersionedCandidates231.headModels_packet_iff (listPlan p ctx cert k hi).packet m).mpr
      (GeneralNominalVersionedPlans231.head_models (list_held p ctx cert k hi m valid))

theorem frontier_frame (p : Phase n k) (hi : k ≤ n) (ctx : Context)
    (cert : Refresh p.state ctx) :
    Frame compiled (refresh p.state ctx).core (focus n k) 1 (listPlan p ctx cert k hi) :=
  ⟨rfl,rfl,rfl,rfl,raw_recorded p ctx k (Nat.le_refl _),center_recorded p ctx k (Nat.le_refl _),
    List.mem_cons_of_mem _ (List.mem_cons_self ..),rfl,argument_exact p ctx cert k (by omega),
    list_prepared p hi ctx cert⟩

theorem frontier_not_int (p : Phase n k) (hi : k ≤ n) (ctx : Context)
    (cert : Refresh p.state ctx) : ¬ Prepared compiled ctx (focus n k) intDisplay := by
  rintro ⟨_,_,bounds,loc,_,report,_⟩
  have boundsEq := Option.some.inj (loc.symm.trans (argument_exact p ctx cert k (by omega)))
  cases boundsEq
  exact wrong_int p ctx cert k hi report.2.1

theorem frontier_unique_frame (p : Phase n k) (hi : k ≤ n) (ctx : Context)
    (cert : Refresh p.state ctx) {q : GeneralNominalCenters.Plan roles} {key : Nat}
    (other : Frame compiled (refresh p.state ctx).core (focus n k) key q) :
    q = listPlan p ctx cert k hi := by
  have decl : q.packet.declaration = display := by
    rcases GeneralRebaseCompiledDisplay277.compiled_members other.visible other.role_eq with wrong|right
    · exact False.elim (frontier_not_int p hi ctx cert (wrong ▸ other.prepared))
    · exact right
  have same_site : q.packet.site = (listPlan p ctx cert k hi).packet.site := by
    change q.packet.site = GeneralNominalDemandMerging.pointSite (focus n k)
    have a := other.raw_recorded
    change q.packet.site ∈ p.state.core.erased.current.sites at a
    exact GeneralDeferredLadderStage302.raw_is p _ a other.occurrence_eq
  have same_input : q.input = (listPlan p ctx cert k hi).input := by
    have a := other.center_recorded
    change q.input ∈ p.state.core.sites at a
    exact GeneralObservedLadderRoute301.unique_row n k k q.input (p.centers_eq ▸ a)
      (q.input_exact.trans other.occurrence_eq)
  exact GeneralRebaseScopedFrame276.same_frame other (frontier_frame p hi ctx cert) decl same_site same_input

end Yulang.GeneralDeferredLadderFrontier303
