import Yulang.GeneralRebasePrivateTrace282

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebasePrivateObserved282
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State)
open GeneralRebaseMixedOwnedTrace277 (raw)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable split)
open GeneralNominalVersionedMixedGrowth234 (steps steps_source)
open GeneralRebasePrivateKey282 (port)
open GeneralRebasePrivateSchema282 (SiteSafe)
open GeneralRebasePrivateTrace282 (sites_safe)
open GeneralRebaseAggregateTags281 (Tag fixedOrigin)
open GeneralNominalCenteredEmptyFrame179 (rawSiteSources)

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
  {after : State roles}

theorem root_observed (ctx : GeneralNominalCandidates.Context)
    (point : ∀ idx, (root.demand.arguments idx).1 = (root.demand.arguments idx).2) :
    GeneralNominalDemandMerging.pointSite root = (rootSite ctx.state.seed root).observed := by
  unfold GeneralNominalDemandMerging.pointSite Site.observed
  congr 1
  apply congrArg List.ofFn
  funext idx
  rw [GeneralNominalCenters.point_center _ _ _ (point idx)]
  exact ite_eq_left (point idx)

theorem observations (path : Reachable registry root after) :
    after.core.erased.current.sites = after.core.sites.map Site.observed := by
  obtain ⟨start,formed,path⟩ := path
  induction path with
  | refl =>
    obtain ⟨legacy,⟨ctx,labels,base,point,ground,coverage,rfl⟩,rfl⟩ := formed
    change [GeneralNominalDemandMerging.pointSite root] = [(rootSite ctx.state.seed root).observed]
    rw [root_observed ctx point]
  | @tail prior current path movement ih =>
    rcases split (show Reachable registry root prior from ⟨start,formed,path⟩) movement with
      update | ⟨e,_,_,rfl⟩
    · cases update <;> exact ih
    · change prior.core.erased.current.sites ++ (GeneralNominalVersionedChildren232.emitted e.plan).map Site.observed =
        (prior.core.sites ++ GeneralNominalVersionedChildren232.emitted e.plan).map Site.observed
      rw [List.map_append,ih]

theorem observed_private {site : Site roles} (safe : SiteSafe site target) :
    target ∉ rawSiteSources site.observed := by
  intro seen
  rcases List.mem_append.mp seen with endpoints | origins
  · obtain ⟨row,used,member⟩ := List.mem_flatten.mp endpoints
    obtain ⟨idx,rfl⟩ := List.mem_ofFn.mp used
    rcases List.mem_cons.mp member with lo|hi
    · exact (safe idx).1 lo
    · exact (safe idx).2.1 (List.mem_singleton.mp hi)
  · obtain ⟨o,used,eq⟩ := List.mem_map.mp origins
    obtain ⟨i,found,equal⟩ := List.mem_filterMap.mp used
    obtain ⟨idx,rfl⟩ := List.mem_ofFn.mp found
    have same : GeneralNominalRecursiveInspection.Origin.source (site.center idx) = o := Option.some.inj equal
    subst o
    exact (safe idx).2.2 eq.symm

theorem source_private (reached : Reachable registry root after) (owner decl : Nat) (tag : Tag) :
    port (raw after).seed owner decl tag ∉ GeneralNominalState.sources after.core.erased.source.state := by
  obtain ⟨start,formed,path⟩ := reached
  have source := steps_source path
  have seed := (steps path).seed
  rw [source,seed]
  obtain ⟨legacy,⟨ctx,labels,base,point,ground,coverage,rfl⟩,rfl⟩ := formed
  intro member
  exact Nat.not_lt_of_ge (base.below_seed _ member) (GeneralNominalIdentities.source_above_seed _ _)

end Yulang.GeneralRebasePrivateObserved282
