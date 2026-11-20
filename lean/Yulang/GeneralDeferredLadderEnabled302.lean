import Yulang.GeneralDeferredLadderStage302

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 8500000
namespace Yulang.GeneralDeferredLadderEnabled302
open GeneralDeferredLadderPlan302
open GeneralObservedLadderRoute301
open GeneralDeferredLadderLedger302
open GeneralDeferredLadderStage302
open GeneralDeferredLadderReport302 (context snapshot nominal_at)
open GeneralObservedLadderRefresh301 (before)
open GeneralDeclarationExamples (roles display)
open GeneralNominalExamples (registry displayRoot intDisplay)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalOutputGrowth (finiteModel finite_prefix_separates)
open GeneralNominalVersionedJournal232 (Effect Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedMixedKernel234 (Installable AlternativesSafe Committed)
open GeneralNominalVersionedInstall232 (install InstallationModels)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCenters (Site SameInputs)
open GeneralSourceDictionaries (Occurrence)
open CommonNominalFullCarrier (Equivalent)
open GeneralNominalRecursiveInspection

theorem separates (p : Phase n k) {i j : Nat} (left : i ≤ n+1) (right : j ≤ n+1)
    (same : SameInputs (Models p.state) (site n i) (site n j)) : i = j := by
  have aSeen : GeneralNominalDemandMerging.Denotes (finiteModel n) (site n i).observed [(finiteModel n i).1] := by
    unfold GeneralNominalDemandMerging.Denotes
    rw [GeneralObservedLadderRoute301.inputs]
    exact .cons ⟨_,rfl,.source i⟩ .nil
  have bSeen : GeneralNominalDemandMerging.Denotes (finiteModel n) (site n j).observed [(finiteModel n j).1] := by
    unfold GeneralNominalDemandMerging.Denotes
    rw [GeneralObservedLadderRoute301.inputs]
    exact .cons ⟨_,rfl,.source j⟩ .nil
  have paired := GeneralNominalDemandMerging.same_inputs_denote _ _ _ same (finiteModel n) (model p) _ _ aSeen bSeen
  cases paired with
  | cons equal _ =>
    by_cases identical : i = j
    · exact identical
    · exact False.elim (finite_prefix_separates n i j left right identical equal)

theorem administrative (p : Phase n k) (bound : k ≤ n+1) :
    GeneralNominalVersionedDiagnostic232.AdministrativeReady p.state (focus n k) := by
  constructor
  · exact ⟨site n k,center_recorded p,rfl⟩
  · intro a first id b second same
    rw [p.centers_eq] at first second
    rw [unique_row n k k a first id] at same ⊢
    obtain ⟨i,le,rfl⟩ := (sites_exact ..).mp second
    have eq := separates p bound (Nat.le_trans le bound) same
    cases eq
    exact .refl _

theorem safe (p : Phase n k) (hi : k ≤ n) :
    B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) compiled p.state (focus n k) := by
  have held := model p
  have semantic := GeneralObservedLadderSafety301.semantic n held
  have raw : ∀ i, ¬ GeneralNominalCycleK2.RecursAt p.state.core.erased.current.context.state i := by
    have transfer : ∀ i, ¬ GeneralNominalCycleK2.RecursAt (env p).state i := by
      have valid := held.1.1
      rw [p.context_eq] at valid
      exact GeneralObservedLadderSafety301.raw_acyclic n _ rfl valid
    rw [p.context_eq]
    exact transfer
  refine ⟨?_,?_,?_,?_⟩
  · change ¬ GeneralNominalState.RootPending p.state.core.erased.current.context.state (focus n k).demand
    rw [p.context_eq]
    exact known p hi
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
    · rw [p.context_eq] at notFailed notPrepared
      rcases GeneralRebaseCompiledDisplay277.compiled_members visible role with rfl|rfl
      · exact notFailed (wrong_int p hi)
      · exact notPrepared (list_prepared p hi)
    · exact pending (administrative p (by omega))

theorem positions (p : Phase n k) (hi : k ≤ n) :
    GeneralNominalVersionedCycles232.Safe p.state (stagePlan p hi) := by
  refine ⟨?_,fun entry _ => GeneralObservedLadderSafety301.semantic n (model p) entry.1⟩
  unfold GeneralNominalCenteredSteps.inspection
  rw [show GeneralNominalInspection.queries (stagePlan p hi).packet.context.state
      (stagePlan p hi).packet.context.interpretation (stagePlan p hi).packet.declaration = _
    from GeneralDeferredLadderReport302.display_query n]
  have points : (stagePlan p hi).input.observed.inputs = [some (.source k)] :=
    GeneralObservedLadderRoute301.inputs n k
  change (inspectMany (env p).state [.nominal 0 [.variables [0]]] [GeneralObservedLadderReport301.point n k (by omega)]
    (fun i => ((stagePlan p hi).input.observed.inputs[i]?).join) 0).inspected.length =
    (inspectMany (env p).state [.nominal 0 [.variables [0]]] [GeneralObservedLadderReport301.point n k (by omega)]
    (fun i => ((stagePlan p hi).input.observed.inputs[i]?).join) 0).tests.length
  rw [points]
  simp [inspectMany,inspect,typeArguments,Report.visit,Report.append,
    nominal_at n k hi,GeneralNominalOutputGrowthModels.descriptor]

theorem alternatives (p : Phase n k) (hi : k ≤ n) : AlternativesSafe compiled p.state (stagePlan p hi).input := by
  intro possible same framed
  have baseFrame : Frame compiled p.state.core (focus n k) possible.packet.declaration.id possible := framed
  have decl : possible.packet.declaration = display := by
    rcases GeneralRebaseCompiledDisplay277.compiled_members baseFrame.visible baseFrame.role_eq with wrong|right
    · have prep := baseFrame.prepared
      rw [p.context_eq] at prep
      exact False.elim (no_int p hi (wrong ▸ prep))
    · exact right
  have eq := GeneralRebaseScopedFrame276.same_frame baseFrame (frame p hi) decl
    (raw_is p _ baseFrame.raw_recorded baseFrame.occurrence_eq) same
  subst possible
  exact positions p hi

theorem future_requests (p : Phase n k) (hi : k ≤ n) (o : Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.requests
      (GeneralNominalVersionedInstall232.installCore p.state.core (stagePlan p hi)) o = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro output member
  obtain ⟨row,listed,_,present⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  change row ∈ p.state.core.erased.current.sites ++ GeneralNominalVersionedChildren232.rawSites (stagePlan p hi) at listed
  rw [p.raw_eq,GeneralNominalVersionedChildren232.rawSites,stage_emits] at listed
  rcases List.mem_append.mp listed with earlier|new
  · obtain ⟨s,atStage,rfl⟩ := List.mem_map.mp earlier
    obtain ⟨i,_,rfl⟩ := (sites_exact ..).mp atStage
    cases present
  · have atNew : row = (site n (k+1)).observed := List.mem_singleton.mp new
    subst row
    cases present

theorem ready (p : Phase n k) (hi : k ≤ n) :
    GeneralNominalCenteredHeadMatEffects.Ready p.state.core (focus n k) (stagePlan p hi) := by
  intro output seen
  rw [current_requests] at seen
  cases seen

def effect (p : Phase n k) (hi : k ≤ n) : Effect roles := by
  refine ⟨compiled,p.state.core,stagePlan p hi,frame p hi,?_,ready p hi⟩
  rw [p.context_eq,stage_children]
  exact unique p hi

theorem installation (p : Phase n k) (hi : k ≤ n) (m : Assignment) (valid : Models p.state m) :
    InstallationModels p.state (effect p hi) m := by
  have held := stage_held p hi m valid
  refine ⟨valid,held,⟨GeneralNominalVersionedPlans231.head_models held,
    GeneralRebaseDisplayFrame276.classes_empty (current_requests p (focus n k)) (stagePlan p hi) m⟩,
    GeneralRebaseDisplayFrame276.classes_empty (future_requests p hi (focus n k)) (stagePlan p hi) m,?_,?_⟩
  · intro e listed
    rw [p.legacy_empty] at listed
    cases listed
  · intro old _
    exact GeneralRebaseDisplayFrame276.classes_empty
      (future_requests p hi old.plan.packet.site.occurrence) old.plan m

theorem enabled (p : Phase n k) (hi : k ≤ n) : Installable compiled p.state (effect p hi) := by
  refine ⟨rfl,rfl,safe p hi,GeneralNominalVersionedMixedEmbedding234.source_cache p.reached,?_,?_,
    positions p hi,alternatives p hi,finiteModel n,installation p hi _ (model p)⟩
  · change (GeneralNominalVersionedPlans231.emittedSchema (stagePlan p hi)).unknown = false
    rw [GeneralNominalVersionedTransport231.emittedSchema_eq,
      emitted_schema n k (invocation n k) hi]
  · intro prior member _
    exact (p.packets_display prior member).symm

theorem not_committed (p : Phase n k) (hi : k ≤ n) : ¬ Committed p.state (stagePlan p hi) := by
  intro committed
  have next := committed.2 (focus n (k+1)) ((stage_children p hi).symm ▸ List.mem_singleton_self _)
  rw [p.edges_eq] at next
  obtain ⟨i,before,edge⟩ := (edge_exact ..).mp next
  have same : focus n k = focus n i := (Prod.mk.inj edge).1
  have ineq : k = i := injective n (congrArg (fun o => o.identity) same)
  omega

theorem actual (p : Phase n k) (hi : k ≤ n) :
    (boundary roles).Step registry displayRoot p.state (install p.state (effect p hi)) :=
  ⟨focus n k,p.focus_generated,.install (effect p hi) (enabled p hi) (not_committed p hi)⟩

end Yulang.GeneralDeferredLadderEnabled302
