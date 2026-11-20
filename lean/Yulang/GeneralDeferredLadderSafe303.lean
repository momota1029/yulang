import Yulang.GeneralDeferredLadderFrontier303
import Yulang.GeneralDeferredLadderShape303

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 7500000
namespace Yulang.GeneralDeferredLadderSafe303
open GeneralDeferredLadderLedger302 (Phase)
open GeneralDeferredLadderFrontier303 (list_prepared frontier_not_int)
open GeneralDeferredLadderRetargetData302 (lift listPlan list_same wrong_int argument_exact)
open GeneralObservedLadderRoute301 (focus)
open GeneralObservedLadderPlan301 (compiled)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalRecursiveCandidates (Context)
open GeneralNominalVersionedCandidates231 (inputs Unique Survivor survivor_children_functional)
open GeneralNominalVersionedFrame231 (children)
open GeneralDeclarationExamples (roles display display_checked)
open GeneralNominalExamples (intDisplay)

theorem known (p : Phase n k) (hi : k ≤ n) (ctx : Context) (cert : Refresh p.state ctx) :
    ¬ GeneralNominalState.RootPending ctx.state (inputs (focus n k)).demand := by
  intro pending
  obtain ⟨i,bad⟩ := pending
  apply bad
  have start := GeneralObservedLadderRefreshProgram301.earlier_known n k hi
  exact (lift p ctx cert).known _ start

theorem chosen_children (p : Phase n k) (hi : k ≤ n) (ctx : Context) (cert : Refresh p.state ctx) :
    children (listPlan p ctx cert k hi).packet = [focus n (k+1)] :=
  (GeneralDeferredLadderTransport302.children_eq (list_same p ctx cert k hi)).symm.trans
    (GeneralObservedLadderEvidence301.replay_children (GeneralObservedLadderEvidence301.final n) k hi)

theorem unique (p : Phase n k) (hi : k ≤ n) (ctx : Context) (cert : Refresh p.state ctx) :
    Unique compiled ctx (focus n k) 1 [focus n (k+1)] := by
  have chosen : Survivor compiled ctx (focus n k) 1 [focus n (k+1)] :=
    ⟨known p hi ctx cert,display,List.mem_cons_of_mem _ (List.mem_cons_self ..),display_checked,
      rfl,rfl,_,argument_exact p ctx cert k (by omega),list_prepared p hi ctx cert,
      (chosen_children p hi ctx cert).symm⟩
  refine ⟨chosen,?_⟩
  intro key kids other
  have kept := other
  obtain ⟨_,d,visible,_,eq,role,_,_,ready,_⟩ := other
  rcases GeneralRebaseCompiledDisplay277.compiled_members visible role with rfl|rfl
  · exact False.elim (frontier_not_int p hi ctx cert ready)
  · subst key
    exact ⟨rfl,survivor_children_functional GeneralRebaseCompiledDisplay277.compiled_checked kept chosen⟩

theorem administrative (p : Phase n k) (cap : k ≤ n+1) (ctx : Context) (cert : Refresh p.state ctx) :
    GeneralNominalVersionedDiagnostic232.AdministrativeReady (refresh p.state ctx) (focus n k) := by
  have raw := GeneralDeferredLadderEnabled302.administrative p cap
  have models : Models (refresh p.state ctx) = Models p.state :=
    funext (fun _ => propext (refresh_models cert))
  unfold GeneralNominalVersionedDiagnostic232.AdministrativeReady at raw ⊢
  refine ⟨raw.1,?_⟩
  have forward {a b : Nat} (path : GeneralNominalSaturationState.Alias p.state.core.erased.current a b) :
      GeneralNominalSaturationState.Alias (refresh p.state ctx).core.erased.current a b := by
    induction path with
    | refl => exact .refl _
    | edge seen => exact .edge seen
    | symm _ ih => exact .symm ih
    | trans _ _ first last => exact .trans first last
  intro a first root b last same
  rw [models] at same
  exact forward (raw.2 a first root b last same)

theorem int_failed (p : Phase n k) (hi : k ≤ n) (ctx : Context) (cert : Refresh p.state ctx) :
    GeneralNominalVersionedCandidates231.Failed compiled ctx (focus n k) intDisplay := by
  refine ⟨GeneralDeferredLadderRetargetFrames302.metadata p ctx cert,
    (listPlan p ctx cert k hi).packet.bounds,argument_exact p ctx cert k (by omega),
    GeneralDeferredLadderFrontier303.frontier_fresh p ctx cert _,?_,?_,.inl (wrong_int p ctx cert k hi)⟩
  all_goals
    unfold GeneralNominalRecursiveCandidates.report
    rw [GeneralDeferredLadderReindexed302.query_int ctx
      (GeneralDeferredLadderReindexed302.promotion_metadata p ctx cert).2]
    simp [GeneralNominalRecursiveInspection.inspectMany,GeneralNominalRecursiveInspection.inspect,
      GeneralNominalRecursiveInspection.Report.visit,GeneralNominalRecursiveInspection.Report.append,
      GeneralDeferredLadderRetargetData302.recorded p ctx cert k hi]

theorem safe (p : Phase n k) (hi : k ≤ n) (ctx : Context) (cert : Refresh p.state ctx) :
    B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles)
      compiled (refresh p.state ctx) (focus n k) := by
  have held := (refresh_models cert).mpr (GeneralDeferredLadderStage302.model p)
  have semantic := GeneralObservedLadderSafety301.semantic n held
  have raw : ∀ i, ¬ GeneralNominalCycleK2.RecursAt ctx.state i :=
    GeneralDeferredLadderShape303.raw_acyclic n ctx.state held.1.1
  refine ⟨known p hi ctx cert,?_,?_,?_⟩
  · rintro (rawCycle | (⟨i,cyclic⟩ | ⟨s,_,_,i,cyclic⟩))
    · obtain ⟨_,_,_,slot,_,cyclic⟩ := rawCycle
      exact raw slot cyclic
    · exact semantic _ cyclic
    · exact semantic _ cyclic
  · rintro (rawCycle | ⟨plan,_,entry,_,cyclic⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cyclic⟩ := rawCycle
      exact raw visited.1 cyclic
    · exact semantic _ cyclic
  · rintro (⟨_,d,visible,role,notFailed,notPrepared⟩ | pending)
    · rcases GeneralRebaseCompiledDisplay277.compiled_members visible role with rfl|rfl
      · exact notFailed (int_failed p hi ctx cert)
      · exact notPrepared (list_prepared p hi ctx cert)
    · exact pending (administrative p (by omega) ctx cert)

end Yulang.GeneralDeferredLadderSafe303
