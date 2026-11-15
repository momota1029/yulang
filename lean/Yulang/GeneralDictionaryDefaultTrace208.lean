import Yulang.GeneralDictionaryDefaultGrowth208
import Yulang.GeneralNominalCenteredHeadMatStepTrace

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryDefaultTrace208
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultKernel208
open GeneralNominalCenteredHeadMatStepHistory (Built)
variable {roles : Roles.RoleDecls} {before after state : State roles}

def Registered (state : State roles) (root : Occurrence roles) : Prop :=
  (∃ site ∈ state.core.erased.current.sites, site.occurrence = root) ∧
    ∀ edge ∈ state.core.erased.current.edges, ∃ site ∈ state.core.erased.current.sites, site.occurrence = edge.2

theorem generated_registered (recorded : Registered state root)
    (generated : GeneralNominalSaturationState.Generated state.core.erased.current root focus) :
    ∃ site ∈ state.core.erased.current.sites, site.occurrence = focus := by
  induction generated with
  | root => exact recorded.1
  | child path member ih => exact recorded.2 _ member
  | alias path one two same ih => exact ⟨_,two,rfl⟩

theorem at_registered (recorded : Registered before root) (action : At registry before focus after) : Registered after root := by
  have growth := GeneralDictionaryDefaultGrowth208.at_growth action
  have rootRecorded : ∃ site ∈ after.core.erased.current.sites, site.occurrence = root := by
    obtain ⟨site,member,same⟩ := recorded.1
    exact ⟨site,growth.rawSites member,same⟩
  refine ⟨rootRecorded,?_⟩
  cases action with
  | administrative action =>
      cases action <;> intro edge member
      all_goals
        obtain ⟨site,present,same⟩ := recorded.2 edge member
        exact ⟨site,growth.rawSites present,same⟩
  | refresh | merge =>
      intro edge member
      obtain ⟨site,present,same⟩ := recorded.2 edge member
      exact ⟨site,growth.rawSites present,same⟩
  | install effect enabled novel =>
      intro edge member
      rcases List.mem_append.mp member with old | added
      · obtain ⟨site,present,same⟩ := recorded.2 edge old
        exact ⟨site,growth.rawSites present,same⟩
      · have mapped : edge ∈ effect.plan.packet.children.map (fun child => (effect.plan.packet.site.occurrence,child)) := added
        obtain ⟨child,childMember,equal⟩ := List.mem_map.mp mapped
        subst edge
        obtain ⟨clause,present,signature,rfl⟩ := GeneralNominalPatersonLineage.emitted_clause effect.plan.packet child childMember
        refine ⟨(effect.plan.childSite clause signature).observed,List.mem_append_right _ ?_,rfl⟩
        apply List.mem_map.mpr
        refine ⟨effect.plan.childSite clause signature,?_,rfl⟩
        exact List.mem_map.mpr ⟨⟨clause,present⟩,List.mem_attach _ _,rfl⟩

theorem registered_trace (path : B4Target.Steps (Step registry root) (initial context root) state) : Registered state root := by
  induction path with
  | refl => exact ⟨⟨_,List.mem_singleton_self _,rfl⟩,by intro edge member; cases member⟩
  | tail _ step ih => exact at_registered ih step.choose_spec.2

theorem centered_registered (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ center ∈ state.core.sites, ∃ raw ∈ state.core.erased.current.sites, raw.occurrence = center.occurrence := by
  induction path with
  | refl =>
      intro center member
      cases List.mem_singleton.mp member
      exact ⟨_,List.mem_singleton_self _,rfl⟩
  | tail path step ih =>
      have growth := GeneralDictionaryDefaultGrowth208.step step
      obtain ⟨focus,generated,action⟩ := step
      cases action with
      | administrative action =>
          cases action <;> intro center member
          all_goals
            obtain ⟨raw,present,equal⟩ := ih center member
            exact ⟨raw,growth.rawSites present,equal⟩
      | refresh | merge =>
          intro center member
          obtain ⟨raw,present,equal⟩ := ih center member
          exact ⟨raw,growth.rawSites present,equal⟩
      | install effect enabled novel =>
          intro center member
          rcases List.mem_append.mp member with prior | emitted
          · obtain ⟨raw,present,equal⟩ := ih center prior
            exact ⟨raw,growth.rawSites present,equal⟩
          · exact ⟨center.observed,List.mem_append_right _ (List.mem_map.mpr ⟨center,emitted,rfl⟩),rfl⟩

theorem built_trace (path : B4Target.Steps (Step registry root) (initial context root) state) : Built registry context root state := by
  induction path with
  | refl => exact .initial
  | @tail before after path step ih =>
      obtain ⟨focus,generated,action⟩ := step
      cases action with
      | administrative action =>
          cases action with
          | enqueue linked absent =>
              obtain ⟨site,member,same⟩ := generated_registered (registered_trace path) generated
              exact False.elim (absent site member same)
          | refresh next certificate source member unknown known =>
              exact .context ih next certificate.refines.seed certificate.interpretation
          | equate first last one two equal novel => exact .context ih _ rfl rfl
          | reobserve revision certificate improved => exact .context ih _ rfl rfl
      | refresh focus next certificate source member unknown known =>
          exact .context ih next certificate.refines.seed certificate.interpretation
      | install effect enabled novel => exact .install ih effect enabled.snapshot_eq enabled.registry_eq
      | merge first last one two same novel => exact .merge ih one two same.1

end Yulang.GeneralDictionaryDefaultTrace208
