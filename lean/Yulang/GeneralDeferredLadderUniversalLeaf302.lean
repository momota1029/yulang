import Yulang.GeneralDeferredLadderRetargetFrames302

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 9500000
namespace Yulang.GeneralDeferredLadderUniversalLeaf302
open GeneralDeferredLadderRetargetFrames302
open GeneralDeferredLadderRetargetData302
open GeneralDeferredLadderCompiler302 (delayed_compile)
open GeneralDeferredLadderExact302 (RawStep Promotion)
open GeneralDeferredLadderAfterPromotion302 (after_only_install)
open GeneralObservedLadderRoute301
open GeneralObservedLadderEvidence301 (final dictionary replay_children)
open GeneralObservedLadderPlan301 (compiled)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedJournal232 (Models State)
open GeneralNominalVersionedEvidence231 (Frame Instance)
open GeneralNominalVersionedMixedKernel234 (Committed)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedFrame231 (children)
open GeneralDeclarationExamples (roles display)
open GeneralNominalExamples (registry displayRoot intDisplay)
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceDictionaries (Occurrence)
open GeneralObservedLadderJournalCompiler301 (table)

theorem requests (n : Nat) (ctx : GeneralNominalCandidates.Context) (o : Occurrence roles) :
    GeneralNominalCenteredHeadOutputs.requests (refresh (endUnseen n).state ctx).core o = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro _ found
  have old := (GeneralNominalVersionedRefresh232.refresh_requests (endUnseen n).state ctx).mp found
  rw [GeneralDeferredLadderStage302.current_requests] at old
  cases old

theorem list_children (n : Nat) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh (endUnseen n).state ctx) (i : Nat) (hi : i ≤ n) :
    children (listPlan (endUnseen n) ctx cert i hi).packet = [focus n (i+1)] :=
  (GeneralDeferredLadderTransport302.children_eq (list_same (endUnseen n) ctx cert i hi)).symm.trans
    (replay_children (final n) i hi)

theorem int_children (n : Nat) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh (endUnseen n).state ctx) (known : GeneralNominalState.Known ctx.state (n+1)) :
    children (intPlan (endUnseen n) ctx cert).packet = [] :=
  (GeneralDeferredLadderTransport302.children_eq (scalar_same (endUnseen n) ctx cert known)).symm.trans
    (GeneralObservedLadderLeaf301.children_empty (final n))

theorem frame_compare (n : Nat) (ctx : GeneralNominalCandidates.Context)
    (i : Nat) {q target : Plan roles} {key chosen}
    (given : Frame compiled (refresh (endUnseen n).state ctx).core (focus n i) key q)
    (correct : Frame compiled (refresh (endUnseen n).state ctx).core (focus n i) chosen target)
    (decl : q.packet.declaration = target.packet.declaration)
    (siteEq : target.packet.site = GeneralNominalDemandMerging.pointSite (focus n i))
    (inputEq : target.input = site n i) : q = target := by
  apply GeneralRebaseScopedFrame276.same_frame given correct decl
  · exact (GeneralDeferredLadderStage302.raw_is (endUnseen n) _ given.raw_recorded given.occurrence_eq).trans siteEq.symm
  · rw [inputEq]
    exact unique_row n (n+1) i _ ((endUnseen n).centers_eq ▸ given.center_recorded)
      (q.input_exact.trans given.occurrence_eq)

theorem list_only (n : Nat) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh (endUnseen n).state ctx) (i : Nat) (hi : i ≤ n)
    {q : Plan roles} {key}
    (given : Frame compiled (refresh (endUnseen n).state ctx).core (focus n i) key q) :
    q = listPlan (endUnseen n) ctx cert i hi := by
  let p := endUnseen n
  apply frame_compare n ctx i given (list_frame n ctx cert i hi) _ rfl rfl
  rcases GeneralRebaseCompiledDisplay277.compiled_members given.visible given.role_eq with bad|good
  · have found := given.prepared
    rw [bad] at found
    obtain ⟨_,_,bs,loc,_,done,_⟩ := found
    have point := argument_exact p ctx cert i (by omega)
    cases Option.some.inj (loc.symm.trans point)
    exact False.elim (wrong_int p ctx cert i hi done.2.1)
  · exact good

theorem int_only (n : Nat) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh (endUnseen n).state ctx) (known : GeneralNominalState.Known ctx.state (n+1))
    {q : Plan roles} {key}
    (given : Frame compiled (refresh (endUnseen n).state ctx).core (focus n (n+1)) key q) :
    q = intPlan (endUnseen n) ctx cert := by
  let p := endUnseen n
  apply frame_compare n ctx (n+1) given (int_frame n ctx cert known) _ rfl rfl
  rcases GeneralRebaseCompiledDisplay277.compiled_members given.visible given.role_eq with good|bad
  · exact good
  · have found := given.prepared
    rw [bad] at found
    obtain ⟨_,_,bs,loc,_,done,_⟩ := found
    have point := argument_exact p ctx cert (n+1) (Nat.le_refl _)
    cases Option.some.inj (loc.symm.trans point)
    exact False.elim (wrong_list p ctx cert known done.2.1)

theorem committed (n : Nat) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh (endUnseen n).state ctx) (known : GeneralNominalState.Known ctx.state (n+1))
    {q : Plan roles} {key} (o : Occurrence roles)
    (given : Frame compiled (refresh (endUnseen n).state ctx).core o key q) :
    Committed (refresh (endUnseen n).state ctx) q := by
  let p := endUnseen n
  obtain ⟨i,le,atRow⟩ := GeneralDeferredLadderOnlyInstall302.raw_hit p _ given.raw_recorded
  have eq : o = focus n i := given.occurrence_eq.symm.trans atRow
  subst o
  by_cases inner : i ≤ n
  · cases list_only n ctx cert i inner given
    constructor
    · intro m valid
      exact ⟨list_held p ctx cert i inner m valid,GeneralRebaseDisplayFrame276.classes_empty (requests n ctx _) _ m⟩
    · intro next found
      rw [list_children n ctx cert i inner] at found
      cases List.mem_singleton.mp found
      change (_,_) ∈ p.state.core.erased.current.edges
      rw [p.edges_eq]
      exact (edge_exact ..).mpr ⟨i,by omega,rfl⟩
  · have last : i = n+1 := by omega
    subst i
    cases int_only n ctx cert known given
    constructor
    · intro m valid
      exact ⟨int_held p ctx cert known m valid,GeneralRebaseDisplayFrame276.classes_empty (requests n ctx _) _ m⟩
    · intro next found
      rw [int_children n ctx cert known] at found
      cases found

theorem halted (n : Nat) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh (endUnseen n).state ctx) (known : GeneralNominalState.Known ctx.state (n+1))
    (s : State roles) : ¬ RawStep (refresh (endUnseen n).state ctx) s := by
  intro raw
  obtain ⟨e,enabled,fresh,_⟩ := after_only_install (endUnseen n) (Nat.le_refl _) _ _ ⟨ctx,cert,known,rfl⟩ raw
  have f := e.frame
  rw [enabled.registry_eq,enabled.snapshot_eq] at f
  exact fresh (committed n ctx cert known _ f)

theorem list_instance (n : Nat) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh (endUnseen n).state ctx) (i : Nat) (hi : i ≤ n) (m : Assignment)
    (valid : Models (refresh (endUnseen n).state ctx) m) :
    Instance compiled (refresh (endUnseen n).state ctx).core m (focus n i) 1 [focus n (i+1)] := by
  refine ⟨_,GeneralNominalVersionedEvidence231.certificate_of_semantics
    (list_frame n ctx cert i hi) (list_children n ctx cert i hi).symm
    (list_held (endUnseen n) ctx cert i hi m valid) ?_ ?_⟩
  · intro _ output
    rw [requests] at output
    cases output
  · exact GeneralRebaseDisplayFrame276.classes_empty (requests n ctx _) _ m

theorem int_instance (n : Nat) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh (endUnseen n).state ctx) (known : GeneralNominalState.Known ctx.state (n+1))
    (m : Assignment) (valid : Models (refresh (endUnseen n).state ctx) m) :
    Instance compiled (refresh (endUnseen n).state ctx).core m (focus n (n+1)) 3 [] := by
  refine ⟨_,GeneralNominalVersionedEvidence231.certificate_of_semantics
    (int_frame n ctx cert known) (int_children n ctx cert known).symm
    (int_held (endUnseen n) ctx cert known m valid) ?_ ?_⟩
  · intro _ output
    rw [requests] at output
    cases output
  · exact GeneralRebaseDisplayFrame276.classes_empty (requests n ctx _) _ m

theorem evidence (n : Nat) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh (endUnseen n).state ctx) (known : GeneralNominalState.Known ctx.state (n+1))
    (depth : Nat) (cap : depth ≤ n+1) (m : Assignment) (valid : Models (refresh (endUnseen n).state ctx) m) :
    (boundary roles).Evidence registry (refresh (endUnseen n).state ctx) m
      (focus n (n+1-depth)) (dictionary depth) := by
  induction depth with
  | zero => exact GeneralNominalVersionedEvidence231.evidence_leaf (int_instance n ctx cert known m valid)
  | succ depth ih =>
    have projected : n+1-(depth+1)+1 = n+1-depth := by omega
    have child := ih (by omega)
    rw [← projected] at child
    exact GeneralNominalVersionedEvidence231.evidence_node
      (list_instance n ctx cert (n+1-(depth+1)) (by omega) m valid) (.cons child .nil)

theorem every_delayed_promotion_completes (n : Nat) (s : State roles) (promoted : Promotion n (endUnseen n).state s) :
    (∀ next, ¬ RawStep s next) ∧
    GeneralGeneratedDictionaryRun299.run (table s) (n+2) 0 = some (dictionary (n+1)) ∧
    ∀ m, Models s m → (boundary roles).Evidence registry s m displayRoot (dictionary (n+1)) := by
  obtain ⟨ctx,cert,known,rfl⟩ := promoted
  refine ⟨halted n ctx cert known,?_ ,?_⟩
  · rw [delayed_compile (endUnseen n) ctx cert known]
    exact ite_eq_left (by omega)
  · intro m valid
    change (boundary roles).Evidence registry (refresh (endUnseen n).state ctx) m (focus n 0) (dictionary (n+1))
    simpa only [Nat.sub_self] using evidence n ctx cert known (n+1) (Nat.le_refl _) m valid

end Yulang.GeneralDeferredLadderUniversalLeaf302
