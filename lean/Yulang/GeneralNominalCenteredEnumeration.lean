import Yulang.GeneralNominalCenteredAncestry

/-! Finite raw source support along centered traces. Center-equivalent merges
may have different site records; only their occurrence outputs enter support. -/
namespace Yulang.GeneralNominalCenteredEnumeration
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredTrace GeneralNominalCenteredAncestry
open GeneralNominalActualTraceSupport (pool Supported administrative_support)
open GeneralNominalAllocationSupport
open GeneralNominalInvocationAncestry (frontier)
open GeneralNominalOccurrenceEnumeration (basis checkedFor child_enumerated)
open GeneralNominalSaturationState (Packet)

variable {sources : List Nat}
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem output_atoms_supported (first last : GeneralNominalDemandMerging.Site roles)
    (one : ∀ output ∈ first.occurrence.demand.outputs, output.target ∈ sources)
    (two : ∀ output ∈ last.occurrence.demand.outputs, output.target ∈ sources) (atom : PresenceNormalForm.Atom Nat)
    (member : atom ∈ GeneralNominalDemandMerging.outputAtoms first last) :
    ∀ source ∈ GeneralNominalState.atomSources atom, source ∈ sources := by
  obtain ⟨a,ha,rest⟩ := List.mem_flatMap.mp member
  obtain ⟨b,hb,member⟩ := List.mem_flatMap.mp rest
  split at member
  · simp only [GeneralNominalAllocation.equations,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;>
      simp only [GeneralNominalState.atomSources,GeneralNominalState.typeSources,List.mem_append,
        List.mem_singleton] <;> intro source h
    · rcases h with rfl | rfl
      · exact one a ha
      · exact two b hb
    · rcases h with rfl | rfl
      · exact two b hb
      · exact one a ha
  · cases member

theorem merge_sources {before : GeneralNominalSaturationState.State roles}
    {first last : GeneralNominalDemandMerging.Site roles}
    (prior : GeneralNominalState.sources before.context.state ⊆ sources)
    (one : ∀ output ∈ first.occurrence.demand.outputs, output.target ∈ sources)
    (two : ∀ output ∈ last.occurrence.demand.outputs, output.target ∈ sources) :
    GeneralNominalState.sources (GeneralNominalSaturationState.merge before first last).context.state ⊆ sources := by
  intro source member
  change source ∈ GeneralNominalState.sources (GeneralNominalState.extend before.context.state [] _) at member
  simp only [GeneralNominalState.sources,GeneralNominalState.extend,List.append_nil,List.flatMap_append] at member
  have split : source ∈ GeneralNominalState.sources before.context.state ∨
      source ∈ (GeneralNominalDemandMerging.outputAtoms first last).flatMap GeneralNominalState.atomSources := by
    simpa only [GeneralNominalState.sources,List.mem_append,or_assoc] using member
  rcases split with old | added
  · exact prior old
  · obtain ⟨atom,member,within⟩ := List.mem_flatMap.mp added
    exact output_atoms_supported first last one two atom member source within

theorem source_pool (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    Supported state.erased.current (pool registry context root limit) := by
  induction path with
  | refl =>
    refine ⟨fun _ member => List.mem_append_left _ member,?_⟩
    intro site member output requested
    cases List.mem_singleton.mp member
    exact List.mem_append_left _ (source.linked.2 output requested)
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action =>
      cases action with
      | enqueue linked absent =>
        obtain ⟨site,member,same⟩ := generated_registered path generated
        exact False.elim (absent site member same)
      | refresh after certificate identity member unknown known =>
        exact ⟨fun _ member => ih.1 (certificate.support _ member),ih.2⟩
      | equate first last one two equal novel =>
        exact ⟨fun _ member => administrative_support before.erased.current ih
          (GeneralNominalFeedbackAdministrative.sources_bounded (registry := registry) (.equate focus first last one two equal novel) member),ih.2⟩
      | reobserve => exact ih
    | refresh focus context certificate identity member unknown known =>
        exact ⟨fun _ member => ih.1 (certificate.support _ member),ih.2⟩
    | merge first last support one two same novel guard =>
      obtain ⟨a,ha,ea⟩ := centered_site_registered path first one
      obtain ⟨b,hb,eb⟩ := centered_site_registered path last two
      refine ⟨merge_sources ih.1 ?_ ?_,ih.2⟩
      · intro output member
        apply ih.2 a ha output
        simpa only [ea,Site.observed] using member
      · intro output member
        apply ih.2 b hb output
        simpa only [eb,Site.observed] using member
    | install plan support enabled novel guard =>
      have reservations := reservations_finite bound path generated enabled novel guard
      have listed : GeneralNominalAllocation.reserved plan.packet.context.state plan.packet.registry plan.packet.site.occurrence.identity ⊆
          pool registry context root limit := fun _ member => List.mem_append_right _ (reservations member)
      have visible : plan.packet.declaration ∈ plan.packet.registry.declarations := by
        simpa only [enabled.1.1] using enabled.1.2.2.2.1
      refine ⟨private_sources plan.packet visible (by simpa only [enabled.1.2.1] using ih.1) listed,?_⟩
      intro site member output requested
      change site ∈ before.erased.current.sites ++ plan.packet.children.map (GeneralNominalSharedEmission.childSite plan.packet) at member
      rcases List.mem_append.mp member with old | new
      · exact ih.2 site old output requested
      · obtain ⟨child,childMember,rfl⟩ := List.mem_map.mp new
        exact listed (child_output_reserved plan.packet visible child childMember output requested)

theorem slot_pool (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (slot : Fin state.erased.current.context.state.base.slots) :
    state.erased.current.context.state.base.source slot ∈ pool registry context root limit :=
  (source_pool source bound path).1 (slot_source state.erased.current.context.state slot)

theorem sites_enumerated (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (bound : InstalledDepthBound registry context root limit)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ site ∈ state.erased.current.sites, site.occurrence ∈ basis checked source limit := by
  induction path with
  | refl =>
    intro site member
    cases List.mem_singleton.mp member
    exact List.mem_cons_self
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action =>
      cases action with
      | enqueue linked absent =>
        obtain ⟨site,member,same⟩ := generated_registered path generated
        exact False.elim (absent site member same)
      | refresh | equate | reobserve => exact ih
    | refresh | merge => exact ih
    | install plan support enabled novel guard =>
      have parent := installed_parents_finite bound path generated enabled novel guard
      have config := configuration_trace path
      rw [← enabled.1.2.1] at config
      have listed : ∀ slot, plan.packet.context.state.base.source slot ∈ pool registry context root limit := by
        rw [enabled.1.2.1]
        exact slot_pool source bound path
      have registrySame := enabled.1.1
      have visible : plan.packet.declaration ∈ plan.packet.registry.declarations := by
        simpa only [registrySame] using enabled.1.2.2.2.1
      have packetChecked : ∀ declaration ∈ plan.packet.registry.declarations,
          DeclarationChecked plan.packet.registry.constructors roles declaration := by
        rw [registrySame]; exact checkedFor checked source
      intro site member
      change site ∈ before.erased.current.sites ++ plan.packet.children.map (GeneralNominalSharedEmission.childSite plan.packet) at member
      rcases List.mem_append.mp member with old | added
      · exact ih site old
      · obtain ⟨child,present,rfl⟩ := List.mem_map.mp added
        have result := child_enumerated context plan.packet packetChecked root parent visible
          enabled.1.2.2.2.2.1 enabled.1.2.2.2.2.2.1 listed config.1.symm config.2.1.symm config.2.2.symm child present
        simpa only [basis,registrySame,GeneralNominalSharedEmission.childSite] using result

end Yulang.GeneralNominalCenteredEnumeration
