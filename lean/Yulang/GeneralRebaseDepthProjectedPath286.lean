import Yulang.GeneralRebaseDepthNonunique286

/-! The already implemented 271 successor tracks exactly the one visible
installation on every actual raw 286 path. Scalar refreshes are silent before
as well as after it. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseDepthProjectedPath286
open GeneralDictionaryOutputDepth252 (roles root registry initial plan)
open GeneralRebaseOutputDepthSuccessor271 (owner output support)
open GeneralRebaseOutputDepthTrace271 (observe)
open GeneralRebaseStep258 (done)
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralRebaseDepthPathRank285 (ActualPath)
open GeneralRebaseDepthPhase286 (Hop InstallHop)
open GeneralRebaseDepthFullTrace286 (RefreshTrace Crosses)
open GeneralRebaseLiveProjection264 (liveFacts)
open GeneralRebaseMultiSelection263 (ofPlan proposal requests)
open GeneralRebaseOneOutputFacts270 (pairKey)

theorem to_steps {s t : State roles} {n : Nat} (path : ActualPath s t n) :
    B4Target.Steps (Step registry root) s t := by
  induction path with
  | empty => exact .refl
  | more _ next ih => exact .tail ih next

theorem silent {s t : State roles} (go : Hop s t) : observe t = observe s := by
  cases go with
  | refresh ctx _ _ _ _ _ =>
    exact (GeneralRebaseSourceProjection264.refresh_stutters [owner] [output] s ctx).symm

theorem silent_trace {s t : State roles} {n : Nat} (walk : RefreshTrace s t n) :
    observe t = observe s := by
  induction walk with
  | empty => rfl
  | more _ next ih => exact (silent next).trans ih

theorem install_writes_pair {s t : State roles} {n : Nat}
    (path : RefreshTrace initial s n) (hit : InstallHop s t) :
    pairKey owner output ∈ liveFacts t := by
  have linked := GeneralRebaseDepthFullTrace286.linked_after path
  have pre := GeneralRebaseDepthEnableShape286.as_pre linked
  cases hit with
  | take e allowed same _ =>
    have certified := GeneralRebaseDepthPreInstall286.installed_uses_certified
      pre.anchor pre.plan allowed same
    have after := GeneralRebaseDepthCrossAnchor286.anchored pre.anchor pre.plan allowed same
    change pairKey owner output ∈ GeneralRebaseLiveProjection264.facts _ _
    apply (GeneralRebaseLiveProjection264.member ..).mpr
    refine ⟨e.plan,List.mem_cons_self,?_⟩
    have select : (ofPlan e.plan).owner = owner := by
      unfold ofPlan owner
      rw [same,certified.frame.key_eq]
    have present : output ∈ requests (GeneralNominalVersionedInstall232.install s e).core (ofPlan e.plan) := by
      unfold requests
      rw [show (ofPlan e.plan).root = root from same]
      apply (GeneralRebaseExecutableRequests262.mem_iff ..).mpr
      refine ⟨GeneralNominalDemandMerging.pointSite root,?_,.refl _,?_⟩
      · rw [after.sites]
        exact List.mem_singleton_self _
      · exact List.mem_singleton_self _
    exact (GeneralRebaseOneOutputFacts270.pair_proposal ..).mpr ⟨select,present⟩

theorem installed_observe {s t : State roles} {n : Nat}
    (path : RefreshTrace initial s n) (hit : InstallHop s t) : observe t = done support := by
  have pairPresent := install_writes_pair path hit
  have actual : ActualPath initial t (n+1) :=
    .more (GeneralRebaseDepthFullTrace286.real_refresh_trace path) (GeneralRebaseDepthPhase286.as_step hit)
  have view := GeneralRebaseOutputDepthSuccessor271.dichotomy t (to_steps actual)
  have basisPair : pairKey owner output ∈ support := by
    change pairKey owner output ∈ GeneralRebaseCompression266.Basis [owner] [output]
    rw [GeneralRebaseOneOutputProjection270.basis_two]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have notRemaining : pairKey owner output ∉ (observe t).remaining := by
    change pairKey owner output ∉ support.filter (fun f => !(liveFacts t).contains f)
    intro h
    have inFilter := (List.mem_filter.mp h).2
    have included : (liveFacts t).contains (pairKey owner output) = true :=
      List.contains_iff_mem.mpr pairPresent
    rw [included] at inFilter
    cases inFilter
  rcases view with empty|full
  · exact GeneralRebaseStep258.state_ext _ _ empty
  · exact False.elim (notRemaining (full.symm ▸ basisPair))

theorem crossed_observe {s : State roles} {n : Nat} (path : Crosses s n) :
    observe s = done support := by
  obtain ⟨before,middle,first,last,early,hit,after,_⟩ := path.trace
  exact (silent_trace after).trans (installed_observe early hit)

theorem observed_phase {s : State roles} {n : Nat} (path : ActualPath initial s n) :
    (observe s = done support ↔ GeneralRebaseDepthPhase286.Post s) ∧
    (observe s = GeneralRebaseStep258.initial support ↔ GeneralRebaseDepthPhase286.Pre s) := by
  have unequal : GeneralRebaseStep258.initial support ≠ done support := by
    intro eq
    have impossible : support = [] := congrArg GeneralRebaseStep258.State.remaining eq
    exact (by decide +kernel : support ≠ []) impossible
  rcases GeneralRebaseDepthFullTrace286.decomposes path with early|crossed
  · have eq : observe s = GeneralRebaseStep258.initial support :=
      (silent_trace early).trans GeneralRebaseOutputDepthSuccessor271.initial_view
    have phase := GeneralRebaseDepthEnableShape286.as_pre (GeneralRebaseDepthFullTrace286.linked_after early)
    constructor
    · exact ⟨fun h => (unequal (eq.symm.trans h)).elim,
        fun p => (GeneralRebaseDepthPhase286.exclusive phase p).elim⟩
    · exact ⟨fun _ => phase,fun _ => eq⟩
  · have eq := crossed_observe crossed
    have phase := GeneralRebaseDepthFullTrace286.crosses_post crossed
    constructor
    · exact ⟨fun _ => phase,fun _ => eq⟩
    · exact ⟨fun h => (unequal (h.symm.trans eq)).elim,
        fun p => (GeneralRebaseDepthPhase286.exclusive p phase).elim⟩

end Yulang.GeneralRebaseDepthProjectedPath286
