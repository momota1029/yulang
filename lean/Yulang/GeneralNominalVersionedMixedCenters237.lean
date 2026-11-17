import Yulang.GeneralNominalVersionedInvocationPool237
/-! Every actual trace has a source-determined finite identity frontier.
No final-state model-existence premise is needed: installation common supplies
one at each growth event; all other steps retain the same center list.
This bounds identities, not observation-dependent occurrence arguments. -/
namespace Yulang.GeneralNominalVersionedMixedCenters237
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234 GeneralNominalVersionedInstall232
open GeneralNominalVersionedMixedAncestry237
open GeneralNominalInvocationAncestry (frontier)
open GeneralNominalPatersonLineage (mass)
variable {roles : Roles.RoleDecls} {root : Occurrence roles} {state : State roles}

theorem centers_bounded
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ site ∈ state.core.sites, site.occurrence.identity ∈
      frontier registry context.state.seed root.identity (mass rootLabels) := by
  induction path with
  | refl =>
    intro site member
    cases List.mem_singleton.mp member
    exact GeneralNominalInvocationAncestry.bounded_enumerated .root (Nat.zero_le _)
  | @tail before after path action ih =>
    have entire := B4Target.Steps.tail path action
    obtain ⟨focus,generated,action⟩ := action
    cases action with
    | administrative action =>
      cases action with
      | enqueue linked absent =>
        obtain ⟨site,member,same⟩ := GeneralNominalVersionedMixedTrace235.generated_registered
          (GeneralNominalVersionedMixedTrace235.steps (GeneralNominalVersionedMixedTrace235.initial context) path).1 generated
        exact False.elim (absent site member same)
      | refresh | reobserve | equate => exact ih
    | refresh | merge => exact ih
    | install effect enabled novel =>
      obtain ⟨model,common⟩ := enabled.common
      have valid := (install_models enabled.snapshot_eq).mpr common
      intro site member
      obtain ⟨depth,labels,ancestry,_,bound⟩ := sites_bounded source point ground coverage entire model valid site member
      exact GeneralNominalInvocationAncestry.bounded_enumerated ancestry (by omega)

/-- The finite center-ID cover is an actual producer from source formation,
not a cover assumed for all future installations. -/
theorem identity_cover
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation) :
    ∃ identities : List Nat, ∀ state,
      B4Target.Steps (Step registry root) (initial context root) state →
      ∀ site ∈ state.core.sites, site.occurrence.identity ∈ identities :=
  ⟨frontier registry context.state.seed root.identity (mass rootLabels),
    fun _ path => centers_bounded source point ground coverage path⟩
end Yulang.GeneralNominalVersionedMixedCenters237
