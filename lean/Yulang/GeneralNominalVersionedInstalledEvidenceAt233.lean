import Yulang.GeneralNominalVersionedInstalledEvidence233
import Yulang.GeneralNominalVersionedBoundary232
import Yulang.GeneralNominalVersionedSourceBoundary232
import Yulang.B4SkeletonV8
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalVersionedInstalledEvidenceAt233
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedInstall232
variable {roles : Roles.RoleDecls} {state : State roles} {effect : Effect roles}

 theorem generated_only {core : GeneralNominalSaturationState.State roles}
    (edges : core.edges = [])
    (sites : ∀ site ∈ core.sites, site.occurrence = root)
    (given : GeneralNominalSaturationState.Generated core root focus) : focus = root := by
  induction given with
  | root => rfl
  | child _ edge _ => rw [edges] at edge; cases edge
  | alias _ _ last _ _ => exact sites _ last

theorem installed_generated_only
    (terminal : GeneralNominalVersionedFrame231.children effect.plan.packet = [])
    (edges : state.core.erased.current.edges = [])
    (sites : ∀ site ∈ state.core.erased.current.sites, site.occurrence = effect.plan.packet.site.occurrence)
    (given : GeneralNominalSaturationState.Generated (install state effect).core.erased.current
      effect.plan.packet.site.occurrence focus) : focus = effect.plan.packet.site.occurrence := by
  apply generated_only (core := (install state effect).core.erased.current) (given := given)
  · change state.core.erased.current.edges ++ GeneralNominalVersionedChildren232.edges effect.plan = []
    unfold GeneralNominalVersionedChildren232.edges
    rw [edges,terminal]
    rfl
  · change ∀ site ∈ (installCore state.core effect.plan).erased.current.sites, _
    rw [GeneralNominalVersionedTerminal232.raw_eq terminal]
    exact sites

theorem evidenceAt (snapshot : effect.snapshot = state.core)
    (terminal : GeneralNominalVersionedFrame231.children effect.plan.packet = [])
    (edges : state.core.erased.current.edges = [])
    (sites : ∀ site ∈ state.core.erased.current.sites, site.occurrence = effect.plan.packet.site.occurrence)
    (selected : GeneralNominalVersionedBoundary232.Local effect.registry (install state effect)
      effect.plan.packet.site.occurrence (.selected effect.plan.packet.declaration.id [])) :
    B4SkeletonV8.EvidenceAt (GeneralNominalVersionedBoundary232.boundary roles) effect.registry
      (install state effect) effect.plan.packet.site.occurrence := by
  intro model valid demand key children dictionaries reached _stable _childStable chosen childEvidence
  have same : demand = effect.plan.packet.site.occurrence :=
    reached.elim id (installed_generated_only terminal edges sites)
  subst demand
  have same := GeneralNominalVersionedBoundary232.local_functional selected chosen
  cases same
  cases childEvidence
  exact GeneralNominalVersionedInstalledEvidence233.evidence snapshot terminal valid

theorem source_evidenceAt {registry : Registry} (encoded : effect.registry = GeneralNominalCenteredHeadAllocEncoding.registry registry)
    (snapshot : effect.snapshot = state.core)
    (terminal : GeneralNominalVersionedFrame231.children effect.plan.packet = [])
    (edges : state.core.erased.current.edges = [])
    (sites : ∀ site ∈ state.core.erased.current.sites, site.occurrence = effect.plan.packet.site.occurrence)
    (selected : GeneralNominalVersionedSourceBoundary232.Local registry (install state effect)
      effect.plan.packet.site.occurrence (.selected effect.plan.packet.declaration.id [])) :
    B4SkeletonV8.EvidenceAt (GeneralNominalVersionedSourceBoundary232.boundary roles) registry
      (install state effect) effect.plan.packet.site.occurrence := by
  apply GeneralNominalVersionedSourceBoundary232.evidenceAt_iff.mpr
  rw [← encoded]
  apply evidenceAt snapshot terminal edges sites
  rw [encoded]
  exact GeneralNominalVersionedSourceBoundary232.local_iff.mp selected

end Yulang.GeneralNominalVersionedInstalledEvidenceAt233
