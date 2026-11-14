import Yulang.GeneralNominalCenteredHeadMatStepEnumeration
import Yulang.GeneralNominalCenteredHeadMatEmissionCodes

/-! A concrete finite fact cover from a bound on installation ancestry. All
administrative support and total packet semantics are discharged here. -/
namespace Yulang.GeneralNominalCenteredHeadMatGroundCover
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralNominalCenteredHeadMatStepKernel
open GeneralNominalCenteredHeadMatStepTrace GeneralNominalCenteredHeadMatStepDepthSupport
open GeneralNominalCenteredHeadMatStepEnumeration
open GeneralNominalCenteredHeadMatSemanticCodes
open GeneralNominalCenteredHeadMatStepFiniteProgress (FiniteCover GroundCover)
open GeneralNominalOccurrenceEnumeration (basis)
open GeneralNominalActualTraceSupport (pool)
variable {roles : Roles.RoleDecls} {root : Occurrence roles} {state : State roles}

noncomputable def centers (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles)) (limit : Nat) : List (Site roles) :=
  rootSite context.state.seed root ::
    GeneralNominalCenteredHeadMatEmissionCodes.pool context registry (basis checked source limit) (pool registry context root limit)

theorem centers_enumerated (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    state.core.sites ⊆ centers checked source limit := by
  induction path with
  | refl =>
      intro site member
      cases List.mem_singleton.mp member
      exact List.mem_cons_self
  | @tail before after path step ih =>
      obtain ⟨focus,generated,action⟩ := step
      cases action with
      | administrative action => cases action <;> exact ih
      | refresh | merge => exact ih
      | install effect enabled novel =>
          intro site member
          rcases List.mem_append.mp member with prior | emitted
          · exact ih prior
          · have frame := frame enabled
            have parent : effect.plan.packet.site.occurrence ∈ basis checked source limit :=
              sites_enumerated checked source bound path effect.plan.packet.site frame.raw_recorded
            apply List.mem_cons_of_mem
            apply GeneralNominalCenteredHeadMatEmissionCodes.emitted_mem (plan_config path enabled)
              frame.registry_eq parent frame.visible frame.located _ emitted
            rw [frame.context_eq]
            exact slot_pool source bound path

noncomputable def cover (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit) : FiniteCover registry root (initial context root) where
  signatures := (codes context registry (centers checked source limit) (pool registry context root limit)).map (signature context)
  sources := pool registry context root limit
  occurrences := (centers checked source limit).map Site.occurrence
  installs := by
    intro state path effect generated enabled novel
    have frame := frame enabled
    have configured := plan_config path enabled
    have member := encode_mem configured frame.registry_eq
      (centers_enumerated checked source bound path frame.center_recorded) frame.visible frame.located
      (by rw [frame.context_eq]; exact slot_pool source bound path)
    exact ⟨_,List.mem_map.mpr ⟨_,member,rfl⟩,encode_represents configured⟩
  source_mem := fun _ path => (source_pool source bound path).1
  slot_mem := fun _ path => slot_pool source bound path
  center_mem := fun _ path site member =>
    List.mem_map.mpr ⟨site,centers_enumerated checked source bound path member,rfl⟩

theorem accessible_of_depth_bound (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit) :
    Acc (fun next current => Step registry root current next) (initial context root) :=
  GeneralNominalCenteredHeadMatStepFiniteProgress.accessible_of_cover (cover checked source bound)

def GroundDepthBound (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, Checked registry → ∀ context (root : Occurrence roles) labels,
    GeneralNominalSourceFormation.InitialSource registry context root →
    (∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2) →
    GeneralNominalGroundAccessibility.GroundRoots context root labels →
    GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation →
    ∃ limit, InstalledDepthBound registry context root limit

theorem ground_cover (depth : GroundDepthBound roles) : GroundCover roles := by
  intro registry checked context root labels source point ground coverage
  obtain ⟨limit,bound⟩ := depth registry checked context root labels source point ground coverage
  exact ⟨cover checked source bound⟩

theorem progress (depth : GroundDepthBound roles) : GeneralNominalCenteredHeadMatStepExecutor.Progress roles :=
  GeneralNominalCenteredHeadMatStepFiniteProgress.progress (ground_cover depth)

end Yulang.GeneralNominalCenteredHeadMatGroundCover
