import Yulang.GeneralNominalVersionedMixedStableLaws235
import Yulang.GeneralNominalVersionedMixedGrowth234
set_option backward.isDefEq.respectTransparency false
/-! Full mixed-kernel reachable occurrence registration. Administrative enqueue
cannot occur on a source trace, because every generated occurrence is recorded. -/
namespace Yulang.GeneralNominalVersionedMixedTrace235
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
open GeneralNominalSaturationState (Generated)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
  {before after state : State roles}

def Registered (state : State roles) (root : Occurrence roles) : Prop :=
  (∃ site ∈ state.core.erased.current.sites, site.occurrence = root) ∧
    ∀ edge ∈ state.core.erased.current.edges,
      ∃ site ∈ state.core.erased.current.sites, site.occurrence = edge.2

def Centered (state : State roles) : Prop :=
  ∀ center ∈ state.core.sites,
    ∃ raw ∈ state.core.erased.current.sites, raw.occurrence = center.occurrence

def Covered (state : State roles) : Prop :=
  ∀ raw ∈ state.core.erased.current.sites,
    ∃ center ∈ state.core.sites, center.occurrence = raw.occurrence

theorem generated_registered (recorded : Registered state root)
    (generated : Generated state.core.erased.current root focus) :
    ∃ site ∈ state.core.erased.current.sites, site.occurrence = focus := by
  induction generated with
  | root => exact recorded.1
  | child _ member _ => exact recorded.2 _ member
  | alias _ _ member _ _ => exact ⟨_,member,rfl⟩

theorem at_registered (recorded : Registered before root) (action : At registry before focus after) :
    Registered after root := by
  have growth := GeneralNominalVersionedMixedGrowth234.at_growth action
  refine ⟨?_,?_⟩
  · obtain ⟨site,member,same⟩ := recorded.1
    exact ⟨site,growth.legacy.rawSites member,same⟩
  · cases action with
    | administrative action =>
      cases action <;> intro edge member
      all_goals
        obtain ⟨site,present,same⟩ := recorded.2 edge member
        exact ⟨site,growth.legacy.rawSites present,same⟩
    | refresh | merge =>
      intro edge member
      obtain ⟨site,present,same⟩ := recorded.2 edge member
      exact ⟨site,growth.legacy.rawSites present,same⟩
    | install effect enabled novel =>
      intro edge member
      rcases List.mem_append.mp member with old | added
      · obtain ⟨site,present,same⟩ := recorded.2 edge old
        exact ⟨site,growth.legacy.rawSites present,same⟩
      · obtain ⟨child,present,same⟩ := GeneralNominalVersionedChildren232.edge_iff.mp added
        subst edge
        obtain ⟨site,present,same⟩ := GeneralNominalVersionedChildren232.child_raw_site present
        exact ⟨site,List.mem_append_right _ present,same⟩

theorem at_centered (recorded : Centered before) (action : At registry before focus after) : Centered after := by
  have growth := GeneralNominalVersionedMixedGrowth234.at_growth action
  cases action with
  | administrative action =>
    cases action <;> intro center member
    all_goals
      obtain ⟨raw,present,same⟩ := recorded center member
      exact ⟨raw,growth.legacy.rawSites present,same⟩
  | refresh | merge =>
    intro center member
    obtain ⟨raw,present,same⟩ := recorded center member
    exact ⟨raw,growth.legacy.rawSites present,same⟩
  | install effect enabled novel =>
    intro center member
    rcases List.mem_append.mp member with old | added
    · obtain ⟨raw,present,same⟩ := recorded center old
      exact ⟨raw,growth.legacy.rawSites present,same⟩
    · exact ⟨center.observed,List.mem_append_right _ (List.mem_map.mpr ⟨center,added,rfl⟩),rfl⟩

theorem step_covered (registered : Registered before root) (covered : Covered before)
    (action : Step registry root before after) : Covered after := by
  obtain ⟨focus,generated,action⟩ := action
  cases action with
  | administrative action =>
    cases action with
    | enqueue linked absent =>
      obtain ⟨site,present,same⟩ := generated_registered registered generated
      exact False.elim (absent site present same)
    | refresh | equate | reobserve => exact covered
  | refresh | merge => exact covered
  | install effect enabled novel =>
    intro raw member
    rcases List.mem_append.mp member with old | added
    · obtain ⟨center,present,same⟩ := covered raw old
      exact ⟨center,List.mem_append_left _ present,same⟩
    · obtain ⟨center,present,same⟩ := List.mem_map.mp added
      subst raw
      exact ⟨center,List.mem_append_right _ present,rfl⟩

def Invariant (state : State roles) (root : Occurrence roles) : Prop :=
  Registered state root ∧ Centered state ∧ Covered state

theorem initial (context : GeneralNominalCandidates.Context) :
    Invariant (GeneralNominalVersionedJournal232.initial context root) root := by
  refine ⟨⟨⟨_,List.mem_singleton_self _,rfl⟩,?_⟩,?_,?_⟩
  · intro edge member; cases member
  · intro center member; cases List.mem_singleton.mp member; exact ⟨_,List.mem_singleton_self _,rfl⟩
  · intro raw member; cases List.mem_singleton.mp member; exact ⟨_,List.mem_singleton_self _,rfl⟩

theorem step (invariant : Invariant before root) (action : Step registry root before after) : Invariant after root :=
  ⟨at_registered invariant.1 action.choose_spec.2,at_centered invariant.2.1 action.choose_spec.2,
    step_covered invariant.1 invariant.2.2 action⟩

theorem steps (invariant : Invariant before root) (path : B4Target.Steps (Step registry root) before after) :
    Invariant after root := by
  induction path with
  | refl => exact invariant
  | tail _ action ih => exact step ih action

theorem reachable
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state) :
    Invariant state root := by
  obtain ⟨first,⟨legacy,⟨context,labels,source,point,ground,coverage,sameLegacy⟩,same⟩,path⟩ := path
  subst first
  subst legacy
  exact steps (initial context) path

theorem centered_registered
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (member : center ∈ state.core.sites) :
    ∃ raw ∈ state.core.erased.current.sites, raw.occurrence = center.occurrence :=
  (reachable path).2.1 center member

theorem generated_center
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (generated : Generated state.core.erased.current root focus) :
    ∃ center ∈ state.core.sites, center.occurrence = focus := by
  obtain ⟨raw,present,same⟩ := generated_registered (reachable path).1 generated
  obtain ⟨center,present,equal⟩ := (reachable path).2.2 raw present
  exact ⟨center,present,equal.trans same⟩

theorem administrative_ready
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (stable : Stable (GeneralNominalCenteredHeadAllocEncoding.registry registry) state root)
    (generated : Generated state.core.erased.current root focus) :
    GeneralNominalVersionedDiagnostic232.AdministrativeReady state focus := by
  refine ⟨generated_center path generated,?_⟩
  intro first one same last two equal
  exact GeneralNominalVersionedMixedStableLaws235.same_inputs_alias stable
    (same.symm ▸ generated) one two equal

end Yulang.GeneralNominalVersionedMixedTrace235
