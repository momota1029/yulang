import Yulang.GeneralDeferredLadderReindexed302
import Yulang.GeneralNominalCenteredHeadMatPlanData

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 7500000
namespace Yulang.GeneralDeferredLadderRetargetData302
open GeneralDeferredLadderLedger302 (Phase env)
open GeneralDeferredLadderReport302 (context nominal_at)
open GeneralDeferredLadderReindexed302 (query_list query_int promotion_metadata location)
open GeneralDeferredLadderRefreshHead302 (terminal_has_no_nominal)
open GeneralObservedLadderReport301 (pos point)
open GeneralObservedLadderRoute301 (focus site)
open GeneralObservedLadderEvidence301 (final replay)
open GeneralObservedLadderLeaf301 (terminalPlan terminalPacket)
open GeneralObservedLadderPlan301 (compiled)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalRefinements (Refines renameDescriptor)
open GeneralNominalSaturationState (Packet)
open GeneralNominalCenters (Plan)
open GeneralDeclarationExamples (roles display display_checked)
open GeneralNominalExamples (intDisplay int_display_checked)
open GeneralNominalRecursiveInspection
open GeneralNominalRecursiveCandidates (arguments report Context)
open GeneralNominalReportErasure
open GeneralNominalUnaryCaptureFacts (captured report_exact)

def lift (p : Phase n k) (ctx : Context) (cert : Refresh p.state ctx) : Refines (env p).state ctx.state := by
  have old := cert.refines
  rw [p.context_eq] at old
  exact old

abbrev slot (p : Phase n k) (ctx : Context) (cert : Refresh p.state ctx) (i : Nat) (fit : i ≤ n+1) :=
  (lift p ctx cert).base.embed (pos n i fit)

theorem id (p : Phase n k) (ctx : Context) (cert : Refresh p.state ctx) (i : Nat) (fit : i ≤ n+1) :
    ctx.state.base.source (slot p ctx cert i fit) = i :=
  (lift p ctx cert).base.source (pos n i fit)

theorem recorded (p : Phase n k) (ctx : Context) (cert : Refresh p.state ctx) (i : Nat) (hi : i ≤ n) :
    ctx.state.nominals (slot p ctx cert i (by omega)) =
      some (renameDescriptor (lift p ctx cert).base.embed
        (GeneralNominalOutputGrowthModels.descriptor n (pos n i (by omega)) hi)) :=
  (lift p ctx cert).nominals (pos n i (by omega)) _ (nominal_at n i hi)

theorem argument_exact (p : Phase n k) (ctx : Context) (cert : Refresh p.state ctx) (i : Nat) (fit : i ≤ n+1) :
    arguments ctx (focus n i) = some [(slot p ctx cert i fit,slot p ctx cert i fit)] :=
  location ctx n i _ (id p ctx cert i fit)

abbrev packet (p : Phase n k) (ctx : Context) (cert : Refresh p.state ctx)
    (i : Nat) (fit : i ≤ n+1) (decl : GeneralDeclarations.Declaration)
    (checked : GeneralDeclarations.DeclarationChecked compiled.constructors roles decl) : Packet roles :=
  ⟨compiled,ctx,GeneralNominalDemandMerging.pointSite (focus n i),decl,checked,
    [(slot p ctx cert i fit,slot p ctx cert i fit)]⟩

abbrev listPlan (p : Phase n k) (ctx : Context) (cert : Refresh p.state ctx) (i : Nat) (hi : i ≤ n) : Plan roles :=
  ⟨packet p ctx cert i (by omega) display display_checked,site n i,rfl⟩

abbrev intPlan (p : Phase n k) (ctx : Context) (cert : Refresh p.state ctx) : Plan roles :=
  ⟨packet p ctx cert (n+1) (Nat.le_refl _) intDisplay int_display_checked,site n (n+1),rfl⟩

theorem list_report (p : Phase n k) (ctx : Context) (cert : Refresh p.state ctx)
    (i : Nat) (hi : i ≤ n) :
    report ctx display (listPlan p ctx cert i hi).packet.bounds =
      captured ctx.state (slot p ctx cert i (by omega)) 0 0
        (slot p ctx cert (i+1) (by omega),slot p ctx cert (i+1) (by omega)) :=
  report_exact ctx display _ _ (recorded p ctx cert i hi) 0 _ rfl
    (query_list ctx (promotion_metadata p ctx cert).1 (promotion_metadata p ctx cert).2)

theorem wrong_int (p : Phase n k) (ctx : Context) (cert : Refresh p.state ctx)
    (i : Nat) (hi : i ≤ n) :
    (report ctx intDisplay (listPlan p ctx cert i hi).packet.bounds).conflicts ≠ [] := by
  unfold report
  rw [query_int ctx (promotion_metadata p ctx cert).2]
  simp [inspectMany,inspect,Report.visit,Report.append,recorded p ctx cert i hi]

theorem scalar_report (p : Phase n k) (ctx : Context) (cert : Refresh p.state ctx)
    (known : GeneralNominalState.Known ctx.state (n+1)) :
    report ctx intDisplay (intPlan p ctx cert).packet.bounds =
      { inspected := (intPlan p ctx cert).packet.bounds,
        checked := (intPlan p ctx cert).packet.bounds ++ (intPlan p ctx cert).packet.bounds } := by
  obtain ⟨scalar,noNominal⟩ := terminal_has_no_nominal p ctx cert known _ (id p ctx cert (n+1) (Nat.le_refl _))
  unfold report
  rw [query_int ctx (promotion_metadata p ctx cert).2]
  simp [inspectMany,inspect,Report.visit,Report.append,noNominal,scalar]

theorem wrong_list (p : Phase n k) (ctx : Context) (cert : Refresh p.state ctx)
    (known : GeneralNominalState.Known ctx.state (n+1)) :
    (report ctx display (intPlan p ctx cert).packet.bounds).conflicts ≠ [] := by
  obtain ⟨scalar,noNominal⟩ := terminal_has_no_nominal p ctx cert known _ (id p ctx cert (n+1) (Nat.le_refl _))
  unfold report
  rw [query_list ctx (promotion_metadata p ctx cert).1 (promotion_metadata p ctx cert).2]
  simp [inspectMany,inspect,Report.visit,Report.append,noNominal,scalar]

theorem list_erasure (p : Phase n k) (ctx : Context) (cert : Refresh p.state ctx)
    (i : Nat) (hi : i ≤ n) :
    erase ctx.state (report ctx display (listPlan p ctx cert i hi).packet.bounds) =
      ⟨[⟨0,(i+1,i+1),some (.nominal (.source i) 0 0)⟩],
       [(i,i),(i,i),(i+1,i+1)],[((.nominal (.source i) 0 0),(i+1,i+1))],[]⟩ := by
  rw [list_report p ctx cert i hi]
  simp [erase,captured,interval,id p ctx cert i (by omega),id p ctx cert (i+1) (by omega)]

theorem int_erasure (p : Phase n k) (ctx : Context) (cert : Refresh p.state ctx)
    (known : GeneralNominalState.Known ctx.state (n+1)) :
    erase ctx.state (report ctx intDisplay (intPlan p ctx cert).packet.bounds) =
      ⟨[],[(n+1,n+1),(n+1,n+1)],[],[]⟩ := by
  rw [scalar_report p ctx cert known]
  simp [erase,interval,id p ctx cert (n+1) (Nat.le_refl _)]

theorem list_same (p : Phase n k) (ctx : Context) (cert : Refresh p.state ctx) (i : Nat) (hi : i ≤ n) :
    GeneralNominalCenteredHeadMatPlanData.Same (replay (final n) i hi) (listPlan p ctx cert i hi) := by
  have seed := (lift p ctx cert).seed
  obtain ⟨constructors,interp⟩ := promotion_metadata p ctx cert
  refine ⟨rfl,rfl,rfl,seed.symm,constructors.symm,interp.symm,?_⟩
  change erase (GeneralObservedLadderLedger301.env (final n)).state
    (report (GeneralObservedLadderLedger301.env (final n)) display [point n i (by omega)]) = _
  rw [list_erasure p ctx cert i hi]
  rw [GeneralDictionaryOrdinaryTransport.candidate_report_extended,
    GeneralObservedLadderReport301.display_report n i hi]
  rfl

theorem scalar_same (p : Phase n k) (ctx : Context) (cert : Refresh p.state ctx)
    (known : GeneralNominalState.Known ctx.state (n+1)) :
    GeneralNominalCenteredHeadMatPlanData.Same (terminalPlan (final n)) (intPlan p ctx cert) := by
  have seed := (lift p ctx cert).seed
  obtain ⟨constructors,interp⟩ := promotion_metadata p ctx cert
  refine ⟨rfl,rfl,rfl,seed.symm,constructors.symm,interp.symm,?_⟩
  change _ = erase ctx.state (report ctx intDisplay (intPlan p ctx cert).packet.bounds)
  rw [int_erasure p ctx cert known,GeneralObservedLadderLeaf301.blank_report]
  rfl

end Yulang.GeneralDeferredLadderRetargetData302
