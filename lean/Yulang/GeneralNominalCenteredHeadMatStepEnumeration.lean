import Yulang.GeneralNominalCenteredHeadMatStepDepthSupport

/-! The successor relation retains the finite source and occurrence cover
from its retrospective installation-depth bound. -/
namespace Yulang.GeneralNominalCenteredHeadMatStepEnumeration
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralNominalCenteredHeadMatStepKernel
open GeneralNominalCenteredHeadMatStepTrace GeneralNominalCenteredHeadMatStepDepthSupport
open GeneralNominalCenteredEnumeration (merge_sources)
open GeneralNominalActualTraceSupport (pool Supported administrative_support)
open GeneralNominalAllocationSupport
open GeneralNominalInvocationAncestry (frontier)
open GeneralNominalOccurrenceEnumeration (basis checkedFor child_enumerated)
open GeneralNominalSaturationState (Packet)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
theorem equate_sources {before : GeneralNominalSaturationState.State roles}
    (one : first ∈ GeneralNominalState.sources before.context.state)
    (two : last ∈ GeneralNominalState.sources before.context.state) :
    GeneralNominalState.sources (GeneralNominalFeedbackSteps.equate before first last).context.state ⊆
      GeneralNominalState.sources before.context.state := by
  intro source member
  change source ∈ GeneralNominalState.sources (GeneralNominalState.extend before.context.state [] _) at member
  simp only [GeneralNominalState.sources,GeneralNominalState.extend,List.append_nil,List.flatMap_append] at member
  have split : source ∈ GeneralNominalState.sources before.context.state ∨ source = first ∨ source = last := by
    simpa [GeneralNominalState.sources,List.mem_append,or_assoc,GeneralNominalAllocation.equations,
      GeneralNominalState.atomSources,GeneralNominalState.typeSources,or_comm,or_left_comm] using member
  rcases split with old | rfl | rfl
  · exact old
  · exact one
  · exact two

theorem source_pool (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    Supported state.core.erased.current (pool registry context root limit) := by
  induction path with
  | refl =>
    refine ⟨fun _ member => List.mem_append_left _ member,?_⟩
    intro site member output requested
    cases List.mem_singleton.mp member
    exact List.mem_append_left _ (source.linked.2 output requested)
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative action =>
      cases action with
      | enqueue linked absent =>
        obtain ⟨site,member,same⟩ := generated_registered (registered_trace path) generated
        exact False.elim (absent site member same)
      | refresh after certificate identity member unknown known =>
        exact ⟨fun _ member => ih.1 (certificate.support _ member),ih.2⟩
      | equate first last one two equal novel =>
        exact ⟨fun _ member => ih.1 (equate_sources one two member),ih.2⟩
      | reobserve => exact ih
    | refresh focus context certificate identity member unknown known =>
        exact ⟨fun _ member => ih.1 (certificate.support _ member),ih.2⟩
    | merge first last one two same novel =>
      obtain ⟨a,ha,ea⟩ := centered_registered path first one
      obtain ⟨b,hb,eb⟩ := centered_registered path last two
      refine ⟨merge_sources ih.1 ?_ ?_,ih.2⟩
      · intro output member
        apply ih.2 a ha output
        simpa only [ea,Site.observed] using member
      · intro output member
        apply ih.2 b hb output
        simpa only [eb,Site.observed] using member
    | install effect enabled novel =>
      let plan := effect.plan
      have enabledFrame := frame enabled
      have reservations := reservations_finite bound path generated enabled novel
      have listed : GeneralNominalAllocation.reserved plan.packet.context.state plan.packet.registry plan.packet.site.occurrence.identity ⊆
          pool registry context root limit := fun _ member => List.mem_append_right _ (reservations member)
      have visible : plan.packet.declaration ∈ plan.packet.registry.declarations := by
        simpa only [plan,enabledFrame.registry_eq] using enabledFrame.visible
      refine ⟨private_sources plan.packet visible (by simpa only [plan,enabledFrame.context_eq] using ih.1) listed,?_⟩
      intro site member output requested
      change site ∈ before.core.erased.current.sites ++ plan.emitted.map Site.observed at member
      rcases List.mem_append.mp member with old | new
      · exact ih.2 site old output requested
      · obtain ⟨center,centerMember,rfl⟩ := List.mem_map.mp new
        obtain ⟨clause,_,rfl⟩ := List.mem_map.mp centerMember
        exact listed (child_output_reserved plan.packet visible _
          (GeneralNominalCenteredTrace.clauseChild_mem plan.packet clause.val clause.property _) output requested)

theorem slot_pool (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (slot : Fin state.core.erased.current.context.state.base.slots) :
    state.core.erased.current.context.state.base.source slot ∈ pool registry context root limit :=
  (source_pool source bound path).1 (slot_source state.core.erased.current.context.state slot)

theorem sites_enumerated (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ site ∈ state.core.erased.current.sites, site.occurrence ∈ basis checked source limit := by
  induction path with
  | refl =>
    intro site member
    cases List.mem_singleton.mp member
    exact List.mem_cons_self
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative action =>
      cases action with
      | enqueue linked absent =>
        obtain ⟨site,member,same⟩ := generated_registered (registered_trace path) generated
        exact False.elim (absent site member same)
      | refresh | equate | reobserve => exact ih
    | refresh | merge => exact ih
    | install effect enabled novel =>
      let plan := effect.plan
      have enabledFrame := frame enabled
      have parent := installed_parents_finite bound path generated enabled novel
      have config := configuration_trace path
      rw [← enabledFrame.context_eq] at config
      have listed : ∀ slot, plan.packet.context.state.base.source slot ∈ pool registry context root limit := by
        rw [enabledFrame.context_eq]
        exact slot_pool source bound path
      have registrySame := enabledFrame.registry_eq
      have visible : plan.packet.declaration ∈ plan.packet.registry.declarations := by
        simpa only [plan,registrySame] using enabledFrame.visible
      have packetChecked : ∀ declaration ∈ plan.packet.registry.declarations,
          DeclarationChecked plan.packet.registry.constructors roles declaration := by
        rw [registrySame]; exact checkedFor checked source
      intro site member
      change site ∈ before.core.erased.current.sites ++ plan.emitted.map Site.observed at member
      rcases List.mem_append.mp member with old | added
      · exact ih site old
      · obtain ⟨center,centerMember,rfl⟩ := List.mem_map.mp added
        obtain ⟨clause,_,rfl⟩ := List.mem_map.mp centerMember
        have present := GeneralNominalCenteredTrace.clauseChild_mem plan.packet clause.val clause.property
          (plan.packet.checked.signature.2.2.2 clause.val clause.property)
        have result := child_enumerated context plan.packet packetChecked root parent visible
          enabledFrame.role_eq enabledFrame.located listed config.1.symm config.2.1.symm config.2.2.symm _ present
        simpa only [basis,plan,registrySame,Site.observed,Plan.childSite] using result

end Yulang.GeneralNominalCenteredHeadMatStepEnumeration
