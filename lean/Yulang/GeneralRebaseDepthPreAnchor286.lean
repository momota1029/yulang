import Yulang.GeneralRebaseDepthPathComplete285

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 13000000
namespace Yulang.GeneralRebaseDepthPreAnchor286
open GeneralDictionaryOutputDepth252 (snapshot plan root registry roles S F model)
open GeneralDictionaryOutputDepthInstall252 (smallModel small_source)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalState (Known sources)
open GeneralRebaseDepthGroundModels285 (InitialTypeCheck source_inputs)
open GeneralNominalReobservationSteps (PointClosed)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Subtype Equivalent subtype_refl subtype_trans)
open GeneralRebaseDepthPathAnchor285 renaming snapshot → raw

abbrev initial := GeneralDictionaryOutputDepth252.initial

theorem initial_models (m : Assignment) : Models initial m ↔ InitialTypeCheck m := by
  rw [GeneralNominalVersionedJournal232.initial_models]
  exact ⟨fun valid => (source_inputs m).mp valid.1,fun checked =>
    ⟨(source_inputs m).mpr checked,GeneralNominalCenters.point_root_holds _ _ (fun _ => rfl) _⟩⟩

structure Anchor (s : State roles) : Prop where
  models : ∀ m, Models s m ↔ InitialTypeCheck m
  rawModels : ∀ m, GeneralNominalState.Models (raw s) m ↔ InitialTypeCheck m
  nominalTwo : ∃ slot, (raw s).base.source slot = 2 ∧
    ∃ d, (raw s).nominals slot = some d
  point : PointClosed (raw s)
  sites : s.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root]
  centers : s.core.sites = [plan.input]
  edges : s.core.erased.current.edges = []
  aliases : s.core.erased.current.aliases = []
  plans : s.plans = []
  effects : s.effects = []
  legacy : s.legacy.effects = []

theorem start : Anchor initial :=
  ⟨initial_models,source_inputs,⟨(2 : Fin 4),rfl,_,rfl⟩,GeneralRebaseDepthTerminalFrame285.point_closed,
    rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def altered (n : Nat) (t : Ty) : Assignment := fun i =>
  ((if i = n then t else (smallModel i).1),(smallModel i).2)

theorem altered_source (n : Nat) (large : 2 < n) (t : Ty) :
    InitialTypeCheck (altered n t) := by
  have original := (source_inputs smallModel).mp small_source
  have zero : (0 : Nat) ≠ n := by omega
  have one : (1 : Nat) ≠ n := by omega
  have two : (2 : Nat) ≠ n := by omega
  simpa only [InitialTypeCheck,altered,ite_eq_right zero,ite_eq_right one,ite_eq_right two] using original

theorem not_top_small (n : Nat) : ¬ Equivalent .top (smallModel n).1 := by
  by_cases h : n = 2
  · change ¬ Equivalent .top (if n = 2 then F else S)
    rw [ite_eq_left h]
    exact fun eq => GeneralNominalTopObservation.top_not_nominal 0 _ eq.1
  · change ¬ Equivalent .top (if n = 2 then F else S)
    rw [ite_eq_right h]
    exact fun eq => GeneralNominalTopObservation.top_not_scalar .int eq.1

theorem forbidden_large {s : State roles} (a : Anchor s) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh s ctx) (n : Nat) (large : 2 < n) : ¬ Known ctx.state n := by
  intro recognized
  obtain ⟨test,observation,head⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head recognized
  have valid : Models s (altered n .top) := (a.models _).mpr (altered_source n large _)
  have seen := GeneralNominalVersionedMixedObservations233.cache_sound cert.cache
    (GeneralNominalSupport.head_recorded head) valid
  have tested := GeneralDictionaryGroundCopy218Refresh.head_holds head seen
  simp only [altered,ite_true] at tested
  exact GeneralDictionaryGroundCopy218Refresh.top_no_head test tested

theorem novel_position {s : State roles} (a : Anchor s) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh s ctx) (n : Nat) (novel : ¬ Known (raw s) n) (learned : Known ctx.state n) :
    n = 0 ∨ n = 1 := by
  have split : n = 0 ∨ n = 1 ∨ n = 2 ∨ 2 < n := by omega
  rcases split with rfl|rfl|rfl|large
  · exact Or.inl rfl
  · exact Or.inr rfl
  · obtain ⟨slot,identity,desc,seen⟩ := a.nominalTwo
    exact (novel ⟨slot,identity,Or.inr ⟨desc,seen⟩⟩).elim
  · exact (forbidden_large a ctx cert n large learned).elim

theorem only_named {s : State roles} (meaning : ∀ m, Models s m ↔ InitialTypeCheck m)
    (slot : Fin (raw s).base.slots) (d : GeneralNominalState.Descriptor (raw s).base.slots)
    (seen : (raw s).nominals slot = some d) : (raw s).base.source slot = 2 := by
  let n := (raw s).base.source slot
  have casesID : n = 2 ∨ (n ≠ 2 ∧ n ≤ 2) ∨ 2 < n := by omega
  rcases casesID with same | ⟨apart,_small⟩ | large
  · exact same
  · have valid := (meaning smallModel).mpr ((source_inputs _).mp small_source)
    obtain ⟨args,_,edge⟩ := valid.1.1.2.1 slot d seen
    change Equivalent (if n = 2 then F else S) _ at edge
    rw [ite_eq_right apart] at edge
    exact nomatch (GeneralDictionaryInspectionHeads215.tag_subtype
      (GeneralDictionaryInspectionHeads215.tagged_scalar .int)
      (GeneralDictionaryInspectionHeads215.tagged_nominal _ args) edge.1)
  · have valid := (meaning (altered n .top)).mpr (altered_source n large .top)
    obtain ⟨args,_,edge⟩ := valid.1.1.2.1 slot d seen
    change Equivalent ((altered n .top) n).1 _ at edge
    simp only [altered,ite_true] at edge
    exact (GeneralNominalTopObservation.top_not_nominal _ _ edge.1).elim

theorem point_from_retained {s : State roles} (a : Anchor s) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh s ctx) (nextModels : ∀ m, Models (refresh s ctx) m ↔ InitialTypeCheck m) :
    PointClosed ctx.state := by
  obtain ⟨sourceSlot,sourceEq,d,recorded⟩ := a.nominalTwo
  intro slot desc appeared
  let moved := cert.refines.base.embed sourceSlot
  have found := cert.refines.nominals sourceSlot d recorded
  have atTwo : ctx.state.base.source slot = 2 := only_named (s := refresh s ctx) nextModels slot desc appeared
  have eq : moved = slot := ctx.state.base.source_injective
    ((cert.refines.base.source sourceSlot).trans (sourceEq.trans atTwo.symm))
  change ctx.state.nominals moved = _ at found
  rw [eq,appeared] at found
  cases Option.some.inj found
  exact GeneralRebaseRefreshClosure275.rename_point _ d (a.point sourceSlot d recorded)

theorem advance {s : State roles} (a : Anchor s) (ctx : GeneralNominalCandidates.Context)
    (cert : Refresh s ctx) : Anchor (refresh s ctx) := by
  have nextModels : ∀ m, Models (refresh s ctx) m ↔ InitialTypeCheck m :=
    fun m => (refresh_models cert).trans (a.models m)
  refine ⟨nextModels,?_,?_,point_from_retained a ctx cert nextModels,
    a.sites,a.centers,a.edges,a.aliases,a.plans,a.effects,a.legacy⟩
  · intro m
    exact ⟨fun valid => (a.rawModels m).mp (GeneralNominalRefinements.models cert.refines m valid),
      fun checked => ((nextModels m).mpr checked).1.1⟩
  · obtain ⟨slot,source,d,seen⟩ := a.nominalTwo
    exact ⟨cert.refines.base.embed slot,(cert.refines.base.source slot).trans source,
      _,cert.refines.nominals slot d seen⟩

theorem equality_closed {s : State roles} (a : Anchor s) :
    GeneralNominalVersionedMixedTerminalStable234.EqualityClosed s := by
  intro first last _ _ equality m valid
  exact equality m ((a.models m).mpr ((a.rawModels m).mp valid))

end Yulang.GeneralRebaseDepthPreAnchor286
