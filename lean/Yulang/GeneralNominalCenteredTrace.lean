import Yulang.GeneralNominalCenteredInspection
import Yulang.GeneralNominalFiniteProgress

/-! Journal growth and reachable registration for the unrestricted centered
relation. Model restriction is separate from equality of model sets. -/
namespace Yulang.GeneralNominalCenteredTrace
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps GeneralNominalCenters
open GeneralNominalSaturationState (Generated)

variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem at_extends (action : At registry before focus after) :
    GeneralNominalFeedbackProgress.Extends before.erased.current after.erased.current := by
  cases action with
  | administrative focus after action =>
    exact GeneralNominalReobservationSteps.at_extends
      (GeneralNominalSupportSteps.administrative_old action)
  | refresh focus context certificate source member unknown known =>
    exact ⟨⟨fun _ valid => ⟨GeneralNominalRefinements.models certificate.refines _ valid.1,valid.2⟩,
      fun _ member => member,fun _ member => member,fun _ member => member,certificate.refines.known⟩,
      GeneralNominalRefinements.models certificate.refines⟩
  | install plan support enabled novel guard =>
    have refinement := GeneralNominalRefinements.installed plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.bounds
    refine ⟨⟨fun model valid => ((GeneralNominalSharedSteps.install_models (support := support) enabled.1.2.1 model).mp valid).1,
      fun _ member => List.mem_append_left _ member,fun _ member => List.mem_append_left _ member,
      fun _ member => member,?_⟩,?_⟩
    · intro source known
      apply refinement.known source
      simpa only [enabled.1.2.1] using known
    · intro model valid
      rw [← enabled.1.2.1]
      exact GeneralNominalRefinements.models refinement model valid
  | merge first last support one two same novel guard =>
    exact ⟨⟨fun model valid => ((GeneralNominalSaturationState.merge_models ..).mp valid).1,
      fun _ member => member,fun _ member => member,fun _ member => List.mem_cons_of_mem _ member,
      fun _ known => known⟩,fun model valid => ((GeneralNominalState.extend_models ..).mp valid).1⟩

theorem point_at (action : At registry before focus after)
    (point : GeneralNominalReobservationOrder.Point before.erased.current source) :
    GeneralNominalReobservationOrder.Point after.erased.current source := by
  cases action with
  | administrative focus after action =>
    exact GeneralNominalReobservationOrder.point_at
      (GeneralNominalSupportSteps.administrative_old action) point
  | refresh focus context certificate source member unknown known =>
      exact GeneralNominalReobservationOrder.point_refines certificate.refines point
  | merge => exact point
  | install plan support enabled novel guard =>
    have refinement := GeneralNominalRefinements.installed plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.bounds
    conv at refinement => lhs; rw [enabled.1.2.1]
    exact GeneralNominalReobservationOrder.point_refines refinement point

def Recorded (state : State roles) (root : Occurrence roles) : Prop :=
  (∃ site ∈ state.erased.current.sites, site.occurrence = root) ∧
    ∀ parent child, (parent,child) ∈ state.erased.current.edges →
      ∃ site ∈ state.erased.current.sites, site.occurrence = child

theorem recorded_at (recorded : Recorded before root) (action : At registry before focus after) :
    Recorded after root := by
  cases action with
  | administrative focus after action =>
    have sites := (GeneralNominalReobservationSteps.at_extends
      (GeneralNominalSupportSteps.administrative_old action)).journal.sites
    have edges : after.edges = before.erased.current.edges := by cases action <;> rfl
    obtain ⟨site,member,same⟩ := recorded.1
    refine ⟨⟨site,sites site member,same⟩,?_⟩
    intro parent child member
    change (parent, child) ∈ after.edges at member
    rw [edges] at member
    obtain ⟨site,present,same⟩ := recorded.2 parent child member
    exact ⟨site,sites site present,same⟩
  | refresh | merge => exact recorded
  | install plan support enabled novel guard =>
    obtain ⟨site,member,same⟩ := recorded.1
    refine ⟨⟨site,List.mem_append_left _ member,same⟩,?_⟩
    intro parent child member
    rcases List.mem_append.mp member with old | added
    · obtain ⟨site,present,same⟩ := recorded.2 parent child old
      exact ⟨site,List.mem_append_left _ present,same⟩
    · obtain ⟨actual,present,equal⟩ := List.mem_map.mp added
      cases equal
      exact ⟨GeneralNominalSharedEmission.childSite plan.packet child,
        List.mem_append_right _ (List.mem_map.mpr ⟨child,present,rfl⟩),rfl⟩

theorem recorded_trace (path : B4Target.Steps (Step registry root) (initial context root) state) :
    Recorded state root := by
  induction path with
  | refl => exact ⟨⟨_,List.mem_singleton_self _,rfl⟩,by intro _ _ impossible; cases impossible⟩
  | tail path step ih => exact recorded_at ih step.choose_spec.2

theorem generated_registered (path : B4Target.Steps (Step registry root) (initial context root) state)
    (generated : Generated state.erased.current root focus) :
    ∃ site ∈ state.erased.current.sites, site.occurrence = focus := by
  have recorded := recorded_trace path
  cases generated with
  | root => exact recorded.1
  | child _ member => exact recorded.2 _ _ member
  | alias _ _ member _ => exact ⟨_,member,rfl⟩

theorem configuration_step (step : Step registry root before after) :
    after.erased.current.context.state.seed = before.erased.current.context.state.seed ∧
    after.erased.current.context.state.constructors = before.erased.current.context.state.constructors ∧
    after.erased.current.context.interpretation = before.erased.current.context.interpretation := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | administrative focus after action =>
    cases action with
    | refresh _ certificate _ _ _ _ => exact ⟨certificate.refines.seed,certificate.refines.constructors,certificate.interpretation⟩
    | enqueue | equate | reobserve => exact ⟨rfl,rfl,rfl⟩
  | refresh focus context certificate source member unknown known =>
    exact ⟨certificate.refines.seed,certificate.refines.constructors,certificate.interpretation⟩
  | merge => exact ⟨rfl,rfl,rfl⟩
  | install plan support enabled novel guard =>
    change plan.packet.context.state.seed = before.erased.current.context.state.seed ∧
      plan.packet.context.state.constructors = before.erased.current.context.state.constructors ∧
      plan.packet.context.interpretation = before.erased.current.context.interpretation
    rw [enabled.1.2.1]
    exact ⟨rfl,rfl,rfl⟩

theorem configuration_trace (path : B4Target.Steps (Step registry root) before after) :
    after.erased.current.context.state.seed = before.erased.current.context.state.seed ∧
    after.erased.current.context.state.constructors = before.erased.current.context.state.constructors ∧
    after.erased.current.context.interpretation = before.erased.current.context.interpretation := by
  induction path with
  | refl => exact ⟨rfl,rfl,rfl⟩
  | tail path step ih =>
    have next := configuration_step step
    exact ⟨next.1.trans ih.1,next.2.1.trans ih.2.1,next.2.2.trans ih.2.2⟩

theorem clauseChild_mem (packet : GeneralNominalSaturationState.Packet roles)
    (clause : Clause) (present : clause ∈ packet.declaration.requirements)
    (signature : clause.Signature roles) :
    GeneralNominalFeedbackSites.clauseChild packet clause signature ∈ packet.children := by
  unfold GeneralNominalSaturationState.Packet.children GeneralNominalAllocation.children
    GeneralDictionaryEmissionPlans.children
  apply List.mem_map.mpr
  refine ⟨_,?_,rfl⟩
  apply (GeneralCanonicalChildOrder.canonicalEmit_perm packet.site.occurrence.identity
    packet.declaration packet.checked _ _).mem_iff.mp
  exact List.mem_map.mpr ⟨⟨clause,present⟩,List.mem_attach ..,rfl⟩

theorem centered_site_registered
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ site ∈ state.sites, ∃ raw ∈ state.erased.current.sites, raw.occurrence = site.occurrence := by
  induction path with
  | refl =>
    intro site member
    cases List.mem_singleton.mp member
    exact ⟨_,List.mem_singleton_self _,rfl⟩
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action =>
      intro site member
      obtain ⟨raw,registered,same⟩ := ih site member
      exact ⟨raw,(GeneralNominalReobservationSteps.at_extends
        (GeneralNominalSupportSteps.administrative_old action)).journal.sites raw registered,same⟩
    | refresh | merge => exact ih
    | install plan support enabled novel guard =>
      intro site member
      rcases List.mem_append.mp member with old | added
      · obtain ⟨raw,registered,same⟩ := ih site old
        exact ⟨raw,List.mem_append_left _ registered,same⟩
      · obtain ⟨clause,_,rfl⟩ := List.mem_map.mp added
        refine ⟨GeneralNominalSharedEmission.childSite plan.packet _,List.mem_append_right _ ?_,rfl⟩
        apply List.mem_map.mpr
        refine ⟨_,?_,rfl⟩
        exact clauseChild_mem plan.packet clause.val clause.property _

theorem raw_site_centered
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ raw ∈ state.erased.current.sites, ∃ site ∈ state.sites, site.occurrence = raw.occurrence := by
  induction path with
  | refl =>
    intro raw member
    cases List.mem_singleton.mp member
    exact ⟨_,List.mem_singleton_self _,rfl⟩
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action =>
      cases action with
      | enqueue linked absent =>
        obtain ⟨raw,member,same⟩ := generated_registered path generated
        exact False.elim (absent raw member same)
      | refresh | equate | reobserve => exact ih
    | refresh | merge => exact ih
    | install plan support enabled novel guard =>
      intro raw member
      rcases List.mem_append.mp member with old | added
      · obtain ⟨site,present,same⟩ := ih raw old
        exact ⟨site,List.mem_append_left _ present,same⟩
      · obtain ⟨child,present,rfl⟩ := List.mem_map.mp added
        obtain ⟨clause,clausePresent,signature,rfl⟩ := GeneralNominalPatersonLineage.emitted_clause plan.packet child present
        exact ⟨plan.childSite clause signature,List.mem_append_right _
          (List.mem_map.mpr ⟨⟨clause,clausePresent⟩,List.mem_attach ..,rfl⟩),rfl⟩

theorem generated_centered
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (generated : Generated state.erased.current root focus) :
    ∃ site ∈ state.sites, site.occurrence = focus := by
  obtain ⟨raw,member,same⟩ := generated_registered path generated
  obtain ⟨site,present,exact⟩ := raw_site_centered path raw member
  exact ⟨site,present,exact.trans same⟩

end Yulang.GeneralNominalCenteredTrace
