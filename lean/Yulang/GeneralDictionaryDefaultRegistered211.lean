import Yulang.GeneralDictionaryDefaultTrace208
import Yulang.GeneralDictionaryDefaultBoundary208

set_option backward.isDefEq.respectTransparency false

/-! Whole reachable-graph provenance for the corrected default-aware kernel.
No syntax, interval, model-inhabitance, or selected-demand restriction is used. -/
namespace Yulang.GeneralDictionaryDefaultRegistered211
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultKernel208
open GeneralNominalSaturationState (Generated Alias)
variable {roles : Roles.RoleDecls} {state before after : State roles}

theorem generated_growth (growth : GeneralNominalCenteredHeadMatStepTrustedGrowth.Growth before after)
    (edges : before.core.erased.current.edges ⊆ after.core.erased.current.edges)
    (path : Generated before.core.erased.current root focus) :
    Generated after.core.erased.current root focus := by
  induction path with
  | root => exact .root
  | child prior edge ih => exact .child ih (edges edge)
  | alias prior one two same ih =>
      exact .alias ih (growth.rawSites one) (growth.rawSites two) (GeneralNominalCenteredHeadMatStepTrustedGrowth.aliases growth same)

theorem at_edges (action : At registry before focus after) :
    before.core.erased.current.edges ⊆ after.core.erased.current.edges := by
  cases action with
  | administrative action => cases action <;> exact fun _ h => h
  | refresh | merge => exact fun _ h => h
  | install => exact fun _ h => List.mem_append_left _ h

theorem raw_registered_generated
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ site ∈ state.core.erased.current.sites,
      Generated state.core.erased.current root site.occurrence := by
  induction path with
  | refl =>
      intro site member
      cases List.mem_singleton.mp member
      exact .root
  | @tail before after path step ih =>
      have growth := GeneralDictionaryDefaultGrowth208.step step
      have edges := at_edges step.choose_spec.2
      obtain ⟨focus,generated,action⟩ := step
      cases action with
      | administrative action =>
          cases action with
          | enqueue linked absent =>
              obtain ⟨site,present,same⟩ := GeneralDictionaryDefaultTrace208.generated_registered
                (GeneralDictionaryDefaultTrace208.registered_trace path) generated
              exact False.elim (absent site present same)
          | refresh | equate | reobserve =>
              intro site member
              exact generated_growth growth edges (ih site member)
      | refresh | merge =>
          intro site member
          exact generated_growth growth edges (ih site member)
      | install effect enabled novel =>
          intro site member
          change site ∈ before.core.erased.current.sites ++ effect.plan.emitted.map Site.observed at member
          rcases List.mem_append.mp member with old | added
          · exact generated_growth growth edges (ih site old)
          · obtain ⟨center,present,rfl⟩ := List.mem_map.mp added
            obtain ⟨clause,_,rfl⟩ := List.mem_map.mp present
            have parent := generated_growth growth edges generated
            apply Generated.child parent
            apply List.mem_append_right
            apply List.mem_map.mpr
            refine ⟨_,?_,rfl⟩
            exact GeneralNominalCenteredTrace.clauseChild_mem effect.plan.packet clause.val clause.property
              (effect.plan.packet.checked.signature.2.2.2 clause.val clause.property)

theorem registered_iff_generated
    (reachable : B4TargetV7.Reachable (GeneralDictionaryDefaultBoundary208.boundary roles) value root state) :
    (∃ site ∈ state.core.erased.current.sites, site.occurrence = focus) ↔
      Generated state.core.erased.current root focus := by
  obtain ⟨start,initial,path⟩ := reachable
  obtain ⟨context,labels,source,point,ground,coverage,rfl⟩ :=
    GeneralNominalCenteredHeadAllocBoundary.initial_compiled initial
  constructor
  · rintro ⟨site,member,rfl⟩
    exact raw_registered_generated path site member
  · exact GeneralDictionaryDefaultTrace208.generated_registered
      (GeneralDictionaryDefaultTrace208.registered_trace path)

end Yulang.GeneralDictionaryDefaultRegistered211
