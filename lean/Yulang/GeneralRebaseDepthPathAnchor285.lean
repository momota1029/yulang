import Yulang.GeneralRebaseDepthHaltSelection285
import Yulang.GeneralNominalVersionedMixedRefreshEquality234

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27500
set_option maxHeartbeats 12500000
namespace Yulang.GeneralRebaseDepthPathAnchor285
open GeneralDictionaryOutputDepth252 (registry root plan roles model P S F)
open GeneralDictionaryOutputDepthInstall252 (installed installed_model)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalState (Known sources)
open GeneralNominalReobservationSteps (PointClosed PointDescriptor)
open GeneralRebaseDepthScalar285 (old target refreshed fixed_models)
open GeneralRebaseDepthTerminalFrame285 (putTop high_model not_top)
open GeneralDictionaryInspectionHeads215 (tag_subtype tagged_nominal tagged_scalar)
open CommonNominalFullCarrier (Equivalent Subtype)

abbrev snapshot (s : State roles) := s.core.erased.current.context.state
abbrev PublicModels (s : State roles) := ∀ m : Assignment, Models s m ↔ Models installed m

structure Anchor (s : State roles) : Prop where
  models : PublicModels s
  nominal_two : ∃ slot, (snapshot s).base.source slot = 2 ∧
    ∃ d, (snapshot s).nominals slot = some d
  points : PointClosed (snapshot s)
  equality : GeneralNominalVersionedMixedTerminalStable234.EqualityClosed s
  sites : s.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root]
  centers : s.core.sites = [plan.input]
  edges : s.core.erased.current.edges = []

theorem initial_equality : GeneralNominalVersionedMixedTerminalStable234.EqualityClosed installed := by
  intro a b hasA hasB same
  have full : GeneralNominalVersionedMixedKernel234.Equal refreshed a b :=
    fun m valid => same m ((fixed_models m).mp valid)
  exact GeneralRebaseDepthTerminalFrame285.equality_closed a b hasA hasB full

theorem initial : Anchor installed :=
  ⟨fun _ => Iff.rfl,⟨(2 : Fin 4),rfl,_,rfl⟩,GeneralRebaseDepthTerminalFrame285.point_closed,
    initial_equality,GeneralRebaseDepthCommit285.raw_sites,
    GeneralRebaseDepthCommit285.center_sites,GeneralRebaseDepthCommit285.no_edges⟩

theorem valid_model {s : State roles} (same : PublicModels s) : Models s model :=
  (same model).mpr installed_model

theorem valid_high {s : State roles} (same : PublicModels s) (n : Nat) (high : 3 < n) :
    Models s (putTop n) :=
  (same _).mpr ((fixed_models _).mp (high_model n high))

theorem forbidden_high {s : State roles} (same : PublicModels s)
    (ctx : GeneralNominalCandidates.Context) (cert : Refresh s ctx) (n : Nat) (high : 3 < n) :
    ¬ Known ctx.state n := by
  intro known
  obtain ⟨test,observation,head⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head known
  have fact := GeneralNominalVersionedMixedObservations233.cache_sound cert.cache
    (GeneralNominalSupport.head_recorded head) (valid_high same n high)
  have tested := GeneralDictionaryGroundCopy218Refresh.head_holds head fact
  simp only [putTop,ite_true] at tested
  exact GeneralDictionaryGroundCopy218Refresh.top_no_head test tested

theorem forbidden_output {s : State roles} (same : PublicModels s)
    (ctx : GeneralNominalCandidates.Context) (cert : Refresh s ctx) :
    ¬ Known ctx.state 3 :=
  GeneralRebaseDepthRefresh285.no_certified_deep_head_of_model s (valid_model same) ctx.state cert.cache rfl

theorem fresh_position {s : State roles} (a : Anchor s)
    (ctx : GeneralNominalCandidates.Context) (cert : Refresh s ctx) (n : Nat)
    (unknown : ¬ Known (snapshot s) n) (known : Known ctx.state n) : n = 0 ∨ n = 1 := by
  by_cases high : 3 < n
  · exact (forbidden_high a.models ctx cert n high known).elim
  have candidates : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
  rcases candidates with rfl|rfl|rfl|rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · obtain ⟨slot,source,d,seen⟩ := a.nominal_two
    exact (unknown ⟨slot,source,Or.inr ⟨d,seen⟩⟩).elim
  · exact (forbidden_output a.models ctx cert known).elim

theorem only_nominal {s : State roles} (a : PublicModels s)
    (slot : Fin (snapshot s).base.slots) (d : GeneralNominalState.Descriptor (snapshot s).base.slots)
    (seen : (snapshot s).nominals slot = some d) : (snapshot s).base.source slot = 2 := by
 let n := (snapshot s).base.source slot
 by_cases high : 3 < n
 · have valid := (valid_high a n high).1.1.2.1 slot d seen
   obtain ⟨args,_,same⟩ := valid
   change Equivalent (putTop n n).1 _ at same
   simp only [putTop,ite_true] at same
   exact (GeneralNominalTopObservation.top_not_nominal _ _ same.1).elim
 have slots : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega
 have denoted := (valid_model a).1.1.2.1 slot d seen
 rcases slots with e|e|e|e
 · obtain ⟨args,_,same⟩ := denoted
   change Equivalent (model n).1 _ at same
   rw [e] at same
   exact nomatch (tag_subtype (tagged_scalar .int) (tagged_nominal _ args) same.1)
 · obtain ⟨args,_,same⟩ := denoted
   change Equivalent (model n).1 _ at same
   rw [e] at same
   exact nomatch (tag_subtype (tagged_scalar .int) (tagged_nominal _ args) same.1)
 · exact e
 · apply False.elim
   exact GeneralRebaseDepthRefresh285.nominal_unrepresentable (snapshot s) slot d
     (by change (model n).1 = P; rw [e]; rfl) denoted

theorem next {s : State roles} (a : Anchor s)
    (ctx : GeneralNominalCandidates.Context) (cert : Refresh s ctx) : Anchor (refresh s ctx) := by
 have modelEq : PublicModels (refresh s ctx) := fun m => (refresh_models cert).trans (a.models m)
 obtain ⟨old_slot,old_named,old_desc,old_find⟩ := a.nominal_two
 let new_slot := cert.refines.base.embed old_slot
 have new_name : ctx.state.base.source new_slot = 2 :=
   (cert.refines.base.source old_slot).trans old_named
 have new_desc := cert.refines.nominals old_slot old_desc old_find
 refine ⟨modelEq,⟨new_slot,new_name,_,new_desc⟩,?_,
    GeneralNominalVersionedMixedRefreshEquality234.equality_closed cert a.equality,
    a.sites,a.centers,a.edges⟩
 intro slot desc observed
 have slotName := only_nominal modelEq slot desc observed
 have sameSlot : new_slot = slot := ctx.state.base.source_injective (new_name.trans slotName.symm)
 change ctx.state.nominals new_slot = _ at new_desc
 change ctx.state.nominals slot = some desc at observed
 rw [sameSlot,observed] at new_desc
 cases Option.some.inj new_desc
 exact GeneralRebaseRefreshClosure275.rename_point _ old_desc (a.points _ _ old_find)

end Yulang.GeneralRebaseDepthPathAnchor285
