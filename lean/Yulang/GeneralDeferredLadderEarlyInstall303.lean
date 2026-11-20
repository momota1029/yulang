import Yulang.GeneralDeferredLadderSafe303

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 9500000
namespace Yulang.GeneralDeferredLadderEarlyInstall303
open GeneralDeferredLadderLedger302 (Phase)
open GeneralDeferredLadderRetargetData302 (listPlan list_report list_same)
open GeneralDeferredLadderRetargetFrames302 (list_held)
open GeneralDeferredLadderSafe303 (chosen_children)
open GeneralObservedLadderRoute301 (focus invocation site edge_exact)
open GeneralObservedLadderPlan301 (compiled)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalRecursiveCandidates (Context)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedInstall232 (InstallationModels install installCore)
open GeneralNominalVersionedMixedKernel234 (Installable AlternativesSafe Committed)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedFrame231 (children)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalExamples (registry displayRoot)
open GeneralDeclarationExamples (roles display)
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalCommonBridge (Assignment)

theorem current_requests (p : Phase n k) (ctx : Context) (o : Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.requests (refresh p.state ctx).core o = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro _ found
  have old := (GeneralNominalVersionedRefresh232.refresh_requests p.state ctx).mp found
  rw [GeneralDeferredLadderStage302.current_requests] at old
  cases old

def effect (p : Phase n k) (hi : k ≤ n) (ctx : Context) (cert : Refresh p.state ctx) : Effect roles := by
  refine ⟨compiled,(refresh p.state ctx).core,listPlan p ctx cert k hi,
    GeneralDeferredLadderFrontier303.frontier_frame p hi ctx cert,?_,?_⟩
  · change GeneralNominalVersionedCandidates231.Unique compiled ctx (focus n k) 1
      (children (listPlan p ctx cert k hi).packet)
    rw [chosen_children p hi ctx cert]
    exact GeneralDeferredLadderSafe303.unique p hi ctx cert
  · intro output request
    rw [current_requests p ctx] at request
    cases request

theorem positions (p : Phase n k) (hi : k ≤ n) (ctx : Context) (cert : Refresh p.state ctx) :
    GeneralNominalVersionedCycles232.Safe (refresh p.state ctx) (listPlan p ctx cert k hi) := by
  have held := (refresh_models cert).mpr (GeneralDeferredLadderStage302.model p)
  refine ⟨?_, fun entry _ => GeneralObservedLadderSafety301.semantic n held entry.1⟩
  let a := GeneralDeferredLadderRetargetData302.slot p ctx cert k (by omega)
  unfold GeneralNominalCenteredSteps.inspection
  have qs := GeneralDeferredLadderReindexed302.query_list ctx
    (GeneralDeferredLadderReindexed302.promotion_metadata p ctx cert).1
    (GeneralDeferredLadderReindexed302.promotion_metadata p ctx cert).2
  change (GeneralNominalRecursiveInspection.inspectMany ctx.state
      (GeneralNominalInspection.queries ctx.state ctx.interpretation display) [(a,a)]
      (fun i => ((site n k).observed.inputs[i]?).join) 0).inspected.length =
    (GeneralNominalRecursiveInspection.inspectMany ctx.state
      (GeneralNominalInspection.queries ctx.state ctx.interpretation display) [(a,a)]
      (fun i => ((site n k).observed.inputs[i]?).join) 0).tests.length
  rw [qs,GeneralObservedLadderRoute301.inputs]
  simp [GeneralNominalRecursiveInspection.inspectMany,GeneralNominalRecursiveInspection.inspect,
    GeneralNominalRecursiveInspection.typeArguments,GeneralNominalRecursiveInspection.Report.visit,
    GeneralNominalRecursiveInspection.Report.append,a,GeneralDeferredLadderRetargetData302.recorded p ctx cert k hi,
    GeneralNominalRefinements.renameDescriptor,GeneralNominalRefinements.renameParameter,
    GeneralNominalOutputGrowthModels.descriptor]

theorem alternatives (p : Phase n k) (hi : k ≤ n) (ctx : Context) (cert : Refresh p.state ctx) :
    AlternativesSafe compiled (refresh p.state ctx) (listPlan p ctx cert k hi).input := by
  intro possible same framed
  have baseFrame : Frame compiled (refresh p.state ctx).core (focus n k)
      possible.packet.declaration.id possible := framed
  have eq := GeneralDeferredLadderFrontier303.frontier_unique_frame p hi ctx cert baseFrame
  subst possible
  exact positions p hi ctx cert


theorem emitted (p : Phase n k) (hi : k ≤ n) (ctx : Context) (cert : Refresh p.state ctx) :
    GeneralNominalVersionedChildren232.emitted (listPlan p ctx cert k hi) = [site n (k+1)] := by
  let child := GeneralDeclarationExamples.displayChild
  let hchild := GeneralDeclarationExamples.display_checked.signature.2.2.2 child (by simp [child])
  let s := GeneralNominalVersionedFrame231.childSite (listPlan p ctx cert k hi) child hchild
  have one : (GeneralNominalVersionedChildren232.emitted (listPlan p ctx cert k hi)).length = 1 :=
    GeneralNominalVersionedChildren232.emitted_length _
  have occurs : s ∈ GeneralNominalVersionedChildren232.emitted (listPlan p ctx cert k hi) := by
    unfold GeneralNominalVersionedChildren232.emitted
    have member : child ∈ GeneralCanonicalChildOrder.canonicalRequirements
        (listPlan p ctx cert k hi).packet.declaration.requirements :=
      (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mp (List.mem_singleton_self _)
    exact List.mem_map.mpr ⟨⟨_,member⟩,List.mem_attach _ _,rfl⟩
  obtain ⟨oneSite,eq⟩ := List.length_eq_one_iff.mp one
  rw [eq] at occurs ⊢
  rw [← List.mem_singleton.mp occurs]
  have transport := GeneralDeferredLadderTransport302.child_eq (list_same p ctx cert k hi) child hchild
  change _ = s at transport
  rw [← transport]
  exact congrArg (fun x => [x]) ((GeneralNominalVersionedTransport231.childSite_eq ..).trans
    (GeneralObservedLadderRoute301.child_site n k hi))

theorem future_requests (p : Phase n k) (hi : k ≤ n) (ctx : Context) (cert : Refresh p.state ctx)
    (o : Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.requests
      (installCore (refresh p.state ctx).core (listPlan p ctx cert k hi)) o = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output member
  obtain ⟨row,listed,_,present⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  change row ∈ p.state.core.erased.current.sites ++
    GeneralNominalVersionedChildren232.rawSites (listPlan p ctx cert k hi) at listed
  rw [p.raw_eq,GeneralNominalVersionedChildren232.rawSites,emitted p hi ctx cert] at listed
  rcases List.mem_append.mp listed with earlier|new
  · obtain ⟨s,atStage,rfl⟩ := List.mem_map.mp earlier
    obtain ⟨i,_,rfl⟩ := (GeneralObservedLadderRoute301.sites_exact ..).mp atStage
    cases present
  · have atNew : row = (site n (k+1)).observed := List.mem_singleton.mp new
    subst row
    cases present

theorem installation (p : Phase n k) (hi : k ≤ n) (ctx : Context) (cert : Refresh p.state ctx)
    (m : Assignment) (valid : Models (refresh p.state ctx) m) :
    InstallationModels (refresh p.state ctx) (effect p hi ctx cert) m := by
  have held := list_held p ctx cert k hi m valid
  refine ⟨valid,held,⟨GeneralNominalVersionedPlans231.head_models held,
    GeneralRebaseDisplayFrame276.classes_empty (current_requests p ctx (focus n k)) _ m⟩,
    GeneralRebaseDisplayFrame276.classes_empty (future_requests p hi ctx cert (focus n k)) _ m,?_,?_⟩
  · intro e listed
    change e ∈ p.state.legacy.effects at listed
    rw [p.legacy_empty] at listed
    cases listed
  · intro old _
    exact GeneralRebaseDisplayFrame276.classes_empty (future_requests p hi ctx cert _) old.plan m

theorem promoted_reached (p : Phase n k) (ctx : Context) (cert : Refresh p.state ctx)
    (known : GeneralNominalState.Known ctx.state (n+1)) :
    B4TargetV8.Reachable (boundary roles) registry displayRoot (refresh p.state ctx) := by
  obtain ⟨s,init,path⟩ := p.reached
  exact ⟨s,init,.tail path (GeneralDeferredLadderExact302.promotion_legal p _ ⟨ctx,cert,known,rfl⟩)⟩

theorem enabled (p : Phase n k) (hi : k ≤ n) (ctx : Context) (cert : Refresh p.state ctx)
    (known : GeneralNominalState.Known ctx.state (n+1)) :
    Installable compiled (refresh p.state ctx) (effect p hi ctx cert) := by
  refine ⟨rfl,rfl,GeneralDeferredLadderSafe303.safe p hi ctx cert,
    GeneralNominalVersionedMixedEmbedding234.source_cache (promoted_reached p ctx cert known),?_,?_,
    positions p hi ctx cert,alternatives p hi ctx cert,GeneralNominalOutputGrowth.finiteModel n,
    installation p hi ctx cert _ ((refresh_models cert).mpr (GeneralDeferredLadderStage302.model p))⟩
  · change (GeneralNominalVersionedPlans231.emittedSchema (listPlan p ctx cert k hi)).unknown = false
    rw [← GeneralDeferredLadderTransport302.emitted_eq (list_same p ctx cert k hi),
      GeneralNominalVersionedTransport231.emittedSchema_eq,
      GeneralObservedLadderPlan301.emitted_schema n k (invocation n k) hi]
  · intro prior member _
    change prior ∈ p.state.core.erased.current.packets at member
    exact (p.packets_display prior member).symm

theorem not_committed (p : Phase n k) (hi : k ≤ n) (ctx : Context) (cert : Refresh p.state ctx) :
    ¬ Committed (refresh p.state ctx) (listPlan p ctx cert k hi) := by
  intro committed
  have next := committed.2 (focus n (k+1)) ((chosen_children p hi ctx cert).symm ▸ List.mem_singleton_self _)
  change _ ∈ p.state.core.erased.current.edges at next
  rw [p.edges_eq] at next
  obtain ⟨i,before,edge⟩ := (edge_exact ..).mp next
  have same : focus n k = focus n i := (Prod.mk.inj edge).1
  have ineq : k = i := GeneralObservedLadderRoute301.injective n (congrArg (fun o => o.identity) same)
  omega

theorem actual (p : Phase n k) (hi : k ≤ n) (ctx : Context) (cert : Refresh p.state ctx)
    (known : GeneralNominalState.Known ctx.state (n+1)) :
    (boundary roles).Step registry displayRoot (refresh p.state ctx)
      (install (refresh p.state ctx) (effect p hi ctx cert)) :=
  ⟨focus n k,GeneralDeferredLadderAfterVariants302.generated p ctx p.focus_generated,
    .install (effect p hi ctx cert) (enabled p hi ctx cert known) (not_committed p hi ctx cert)⟩

end Yulang.GeneralDeferredLadderEarlyInstall303
