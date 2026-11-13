import Yulang.GeneralNominalAllocationSupport

/-! The actual repaired trace preserves its interpretation and seed. A bound
on installing ancestors supplies a fixed pool for every listed source ID. -/
namespace Yulang.GeneralNominalActualTraceSupport
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualInspectionSteps
open GeneralNominalInvocationAncestry GeneralNominalAllocationSupport

theorem configuration_step (step : Step registry root before after) :
    after.current.context.state.seed = before.current.context.state.seed ∧
    after.current.context.state.constructors = before.current.context.state.constructors ∧
    after.current.context.interpretation = before.current.context.interpretation := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | administrative focus after action =>
    cases action with
    | refresh _ certificate _ _ _ _ => exact ⟨certificate.refines.seed,certificate.refines.constructors,certificate.interpretation⟩
    | enqueue | equate | reobserve => exact ⟨rfl,rfl,rfl⟩
  | merge => exact ⟨rfl,rfl,rfl⟩
  | install packet support enabled novel guard =>
    change packet.context.state.seed = before.current.context.state.seed ∧
      packet.context.state.constructors = before.current.context.state.constructors ∧
      packet.context.interpretation = before.current.context.interpretation
    rw [enabled.1.2.1]
    exact ⟨rfl,rfl,rfl⟩

theorem configuration_trace (path : B4Target.Steps (Step registry root) before after) :
    after.current.context.state.seed = before.current.context.state.seed ∧
    after.current.context.state.constructors = before.current.context.state.constructors ∧
    after.current.context.interpretation = before.current.context.interpretation := by
  induction path with
  | refl => exact ⟨rfl,rfl,rfl⟩
  | tail path step ih =>
    have next := configuration_step step
    exact ⟨next.1.trans ih.1,next.2.1.trans ih.2.1,next.2.2.trans ih.2.2⟩

def pool (registry : Registry) (context : GeneralNominalCandidates.Context) (root : Occurrence roles) (limit : Nat) : List Nat :=
  GeneralNominalState.sources context.state ++
    allocationPool registry context.state.seed (frontier registry context.state.seed root.identity limit)

def Supported (state : State roles) (sources : List Nat) : Prop :=
  GeneralNominalState.sources state.context.state ⊆ sources ∧
    ∀ site ∈ state.sites, ∀ output ∈ site.occurrence.demand.outputs, output.target ∈ sources

theorem administrative_support (before : State roles) (supported : Supported before sources) :
    GeneralNominalAdministrativeProgress.support before ⊆ sources := by
  intro identity member
  rcases List.mem_append.mp member with old | output
  · exact supported.1 old
  · obtain ⟨site,present,member⟩ := List.mem_flatMap.mp output
    obtain ⟨request,requested,rfl⟩ := List.mem_map.mp member
    exact supported.2 site present request requested

theorem formed_trace (formed : SourceFormed registry root before)
    (path : B4Target.Steps (Step registry root) before after) : SourceFormed registry root after := by
  induction path with
  | refl => exact formed
  | tail path step ih => exact .update ih step

theorem source_pool (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    Supported state.current (pool registry context root limit) := by
  induction path with
  | refl =>
    refine ⟨fun _ member => List.mem_append_left _ member,?_⟩
    intro site member output requested
    cases List.mem_singleton.mp member
    exact List.mem_append_left _ (source.linked.2 output requested)
  | @tail before after path step ih =>
    have formed := formed_trace (.initial context source) path
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action =>
      cases action with
      | enqueue linked absent =>
        obtain ⟨site,member,same⟩ := GeneralNominalSharedSteps.generated_registered (formed_shared formed) generated
        exact False.elim (absent site member same)
      | refresh after certificate identity member unknown known =>
        exact ⟨fun _ member => ih.1 (certificate.support _ member),ih.2⟩
      | equate first last one two equal novel =>
        exact ⟨fun _ member => administrative_support before.current ih
          (GeneralNominalFeedbackAdministrative.sources_bounded (registry := registry) (.equate focus first last one two equal novel) member),ih.2⟩
      | reobserve => exact ih
    | merge first last support one two same novel guard =>
        exact ⟨fun _ member => administrative_support before.current ih
          (GeneralNominalFeedbackAdministrative.sources_bounded (registry := registry) (.merge first last one two same novel) member),ih.2⟩
    | install packet support enabled novel guard =>
      have reservations := reservations_finite bound path generated enabled novel guard
      have listed : GeneralNominalAllocation.reserved packet.context.state packet.registry packet.site.occurrence.identity ⊆
          pool registry context root limit := fun _ member => List.mem_append_right _ (reservations member)
      have visible : packet.declaration ∈ packet.registry.declarations := by
        simpa only [enabled.1.1] using enabled.1.2.2.2.1
      refine ⟨private_sources packet visible (by simpa only [enabled.1.2.1] using ih.1) listed,?_⟩
      intro site member output requested
      change site ∈ before.current.sites ++ packet.children.map (GeneralNominalSharedEmission.childSite packet) at member
      rcases List.mem_append.mp member with old | new
      · exact ih.2 site old output requested
      · obtain ⟨child,childMember,rfl⟩ := List.mem_map.mp new
        exact listed (child_output_reserved packet visible child childMember output requested)

theorem slot_pool (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (slot : Fin state.current.context.state.base.slots) :
    state.current.context.state.base.source slot ∈ pool registry context root limit :=
  (source_pool source bound path).1 (slot_source state.current.context.state slot)

end Yulang.GeneralNominalActualTraceSupport
