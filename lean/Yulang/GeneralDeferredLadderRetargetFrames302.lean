import Yulang.GeneralDeferredLadderRetargetData302
import Yulang.GeneralDeferredLadderTransport302

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29000
set_option maxHeartbeats 9200000
namespace Yulang.GeneralDeferredLadderRetargetFrames302
open GeneralDeferredLadderLedger302 (Phase env)
open GeneralDeferredLadderRetargetData302
open GeneralDeferredLadderAdvance302 (run)
open GeneralDeferredLadderReindexed302 (promotion_metadata)
open GeneralObservedLadderRoute301 (focus invocation site observed sites_exact)
open GeneralObservedLadderEvidence301 (final replay replay_held)
open GeneralObservedLadderLeaf301 (terminalPlan)
open GeneralObservedLadderPlan301 (compiled)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedPlans231 (Holds)
open GeneralNominalVersionedCandidates231 (Prepared inputs)
open GeneralNominalRecursiveCandidates (Metadata report)
open GeneralDeclarationExamples (roles display)
open GeneralNominalExamples (intDisplay)
open GeneralNominalCommonBridge (Assignment)

abbrev endUnseen (n : Nat) := run n (n+1) (Nat.le_refl _)

theorem metadata (p : Phase n k) (ctx : GeneralNominalCandidates.Context) (cert : Refresh p.state ctx) :
    Metadata compiled ctx := by
  obtain ⟨constructors,interp⟩ := promotion_metadata p ctx cert
  exact ⟨constructors.symm,interp.symm ▸ (GeneralObservedLadderSelection301.metadata n).2⟩

theorem linked (p : Phase n k) (ctx : GeneralNominalCandidates.Context) (cert : Refresh p.state ctx)
    (i : Nat) (hi : i ≤ n+1) : GeneralNominalState.Linked ctx.state (inputs (focus n i)).demand := by
  constructor
  · intro index
    have member := GeneralNominalAllocationSupport.slot_source ctx.state (slot p ctx cert i hi)
    rw [id p ctx cert i hi] at member
    exact ⟨member,member⟩
  · intro _ none
    cases none

theorem reference_models (p : Phase n k) (ctx : GeneralNominalCandidates.Context) (cert : Refresh p.state ctx)
    (m : Assignment) (valid : Models (refresh p.state ctx) m) : Models (final n).state m := by
  apply ((final n).models m).mpr
  apply (GeneralDeferredLadderNoAdmin302.same_observed_models p m).mp
  exact (GeneralNominalVersionedMixedObservations233.refresh_models cert).mp valid

theorem list_held (p : Phase n k) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh p.state ctx) (i : Nat) (hi : i ≤ n) (m : Assignment)
    (valid : Models (refresh p.state ctx) m) :
    Holds (listPlan p ctx cert i hi) m :=
  GeneralDeferredLadderTransport302.held_of_reindex (list_same p ctx cert i hi) m
    (replay_held (final n) i hi m (reference_models p ctx cert m valid)) valid.1.1

theorem int_held (p : Phase n k) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh p.state ctx) (known : GeneralNominalState.Known ctx.state (n+1)) (m : Assignment)
    (valid : Models (refresh p.state ctx) m) :
    Holds (intPlan p ctx cert) m :=
  GeneralDeferredLadderTransport302.held_of_reindex (scalar_same p ctx cert known) m
    (GeneralObservedLadderLeaf301.holds (final n) m (reference_models p ctx cert m valid)) valid.1.1

theorem list_fresh (n : Nat) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh (endUnseen n).state ctx) (i : Nat) (hi : i ≤ n) :
    GeneralNominalVersionedAllocation231.Fresh ctx.state compiled (invocation n i)
      (listPlan (endUnseen n) ctx cert i hi).packet.bindings := by
  let p := endUnseen n
  intro key member _
  have eq := (GeneralNominalCenteredHeadMatPlanData.bindings (list_same p ctx cert i hi)).symm.trans
    ((GeneralNominalVersionedTransport231.packet_bindings ..).trans
      (GeneralObservedLadderPlan301.bindings n i (invocation n i) hi))
  rw [eq] at member
  exact (lift p ctx cert).allocated key
    (GeneralDeferredLadderFrames302.keys_installed n (n+1) (Nat.le_refl _) i (by omega) member)

theorem int_fresh (n : Nat) (ctx : GeneralNominalCandidates.Context) (cert : Refresh (endUnseen n).state ctx)
    (bs) : GeneralNominalVersionedAllocation231.Fresh ctx.state compiled (invocation n (n+1)) bs := by
  let p := endUnseen n
  intro key member used
  have before := cert.support _ used
  rw [p.context_eq] at before
  have exact := (lift p ctx cert).seed
  rw [exact] at before
  exact (lift p ctx cert).allocated key (GeneralDeferredLadderLedger302.fresh p bs key member before)

theorem list_prepared (n : Nat) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh (endUnseen n).state ctx) (i : Nat) (hi : i ≤ n) :
    Prepared compiled ctx (focus n i) display := by
  let p := endUnseen n
  let m := GeneralNominalOutputGrowth.finiteModel n
  have valid : Models (refresh p.state ctx) m :=
    (GeneralNominalVersionedMixedObservations233.refresh_models cert).mpr (GeneralDeferredLadderStage302.model p)
  refine ⟨metadata p ctx cert,linked p ctx cert i (by omega),_,argument_exact p ctx cert i (by omega),
    list_fresh n ctx cert i hi,?_,m,?_⟩
  · rw [list_report p ctx cert i hi]
    exact ⟨rfl,rfl,rfl⟩
  · exact (GeneralNominalVersionedCandidates231.headModels_packet_iff (listPlan p ctx cert i hi).packet m).mpr
      (GeneralNominalVersionedPlans231.head_models (list_held p ctx cert i hi m valid))

theorem int_prepared (n : Nat) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh (endUnseen n).state ctx) (known : GeneralNominalState.Known ctx.state (n+1)) :
    Prepared compiled ctx (focus n (n+1)) intDisplay := by
  let p := endUnseen n
  let m := GeneralNominalOutputGrowth.finiteModel n
  have valid : Models (refresh p.state ctx) m :=
    (GeneralNominalVersionedMixedObservations233.refresh_models cert).mpr (GeneralDeferredLadderStage302.model p)
  refine ⟨metadata p ctx cert,linked p ctx cert _ (Nat.le_refl _),_,argument_exact p ctx cert _ (Nat.le_refl _),
    int_fresh n ctx cert _,?_,m,?_⟩
  · rw [scalar_report p ctx cert known]
    exact ⟨rfl,rfl,rfl⟩
  · exact (GeneralNominalVersionedCandidates231.headModels_packet_iff (intPlan p ctx cert).packet m).mpr
      (GeneralNominalVersionedPlans231.head_models (int_held p ctx cert known m valid))

theorem raw_recorded (p : Phase n k) (ctx : GeneralNominalCandidates.Context) (i : Nat) (atPhase : i ≤ k) :
    GeneralNominalDemandMerging.pointSite (focus n i) ∈ (refresh p.state ctx).core.erased.current.sites := by
  change _ ∈ p.state.core.erased.current.sites
  rw [p.raw_eq,← observed n i]
  exact List.mem_map.mpr ⟨site n i,(sites_exact ..).mpr ⟨i,atPhase,rfl⟩,rfl⟩

theorem center_recorded (p : Phase n k) (ctx : GeneralNominalCandidates.Context) (i : Nat) (atPhase : i ≤ k) :
    site n i ∈ (refresh p.state ctx).core.sites := by
  change _ ∈ p.state.core.sites
  rw [p.centers_eq]
  exact (sites_exact ..).mpr ⟨i,atPhase,rfl⟩

theorem list_frame (n : Nat) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh (endUnseen n).state ctx) (i : Nat) (hi : i ≤ n) :
    Frame compiled (refresh (endUnseen n).state ctx).core (focus n i) 1 (listPlan (endUnseen n) ctx cert i hi) :=
  ⟨rfl,rfl,rfl,rfl,raw_recorded (endUnseen n) ctx i (by omega),center_recorded (endUnseen n) ctx i (by omega),
    List.mem_cons_of_mem _ (List.mem_cons_self ..),rfl,argument_exact (endUnseen n) ctx cert i (by omega),
    list_prepared n ctx cert i hi⟩

theorem int_frame (n : Nat) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh (endUnseen n).state ctx) (known : GeneralNominalState.Known ctx.state (n+1)) :
    Frame compiled (refresh (endUnseen n).state ctx).core (focus n (n+1)) 3 (intPlan (endUnseen n) ctx cert) :=
  ⟨rfl,rfl,rfl,rfl,raw_recorded (endUnseen n) ctx _ (Nat.le_refl _),center_recorded (endUnseen n) ctx _ (Nat.le_refl _),
    List.mem_cons_self ..,rfl,argument_exact (endUnseen n) ctx cert _ (Nat.le_refl _),int_prepared n ctx cert known⟩

end Yulang.GeneralDeferredLadderRetargetFrames302
