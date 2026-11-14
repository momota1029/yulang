import Yulang.GeneralNominalCenteredProgress

/-! A finite signature cover for each bounded full centered journal. -/
namespace Yulang.GeneralNominalCenteredSnapshot
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalCenters GeneralNominalCenteredSteps GeneralNominalCenteredTrace
open GeneralNominalInvocationAncestry GeneralNominalAllocationSupport GeneralNominalOccurrenceEnumeration
open GeneralNominalSharedBudget (Signature Represents)
open GeneralNominalSnapshotCover (Parents signatures)
open GeneralNominalActualTraceSupport (Supported pool administrative_support)

theorem snapshot (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (parents : Parents registry context root limit state.erased) :
    Supported state.erased.current (pool registry context root limit) ∧
      ∀ site ∈ state.erased.current.sites, site.occurrence ∈ basis checked source limit := by
  induction path with
  | refl =>
    refine ⟨⟨fun _ member => List.mem_append_left _ member,?_⟩,?_⟩
    · intro site member output requested
      cases List.mem_singleton.mp member
      exact List.mem_append_left _ (source.linked.2 output requested)
    · intro site member
      cases List.mem_singleton.mp member
      exact List.mem_cons_self
  | @tail before after path step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action =>
      cases action with
      | enqueue linked absent =>
        obtain ⟨site,member,same⟩ := GeneralNominalCenteredTrace.generated_registered path generated
        exact False.elim (absent site member same)
      | refresh after certificate identity member unknown known =>
        have old := ih parents
        exact ⟨⟨fun _ member => old.1.1 (certificate.support _ member),old.1.2⟩,old.2⟩
      | equate first last one two equal novel =>
        have old := ih parents
        exact ⟨⟨fun _ member => administrative_support before.erased.current old.1
          (GeneralNominalFeedbackAdministrative.sources_bounded (registry := registry) (.equate focus first last one two equal novel) member),old.1.2⟩,old.2⟩
      | reobserve => exact ih parents
    | refresh focus context certificate source member unknown known =>
      have old := ih parents
      exact ⟨⟨fun _ member => old.1.1 (certificate.support _ member),old.1.2⟩,old.2⟩
    | merge first last support one two same novel guard =>
      have old := ih parents
      exact ⟨⟨fun _ member => administrative_support before.erased.current old.1
        (GeneralNominalCenteredProgress.merge_sources_bounded before.erased.current first.observed last.observed
          (GeneralNominalCenteredProgress.sites_correspond path first one)
          (GeneralNominalCenteredProgress.sites_correspond path last two) member),old.1.2⟩,old.2⟩
    | install plan support enabled novel guard =>
      have old := ih (fun prior member => parents prior (List.mem_cons_of_mem _ member))
      have parent := parents plan.packet (List.mem_cons_self ..)
      have config := configuration_trace path
      rw [← enabled.1.2.1] at config
      have listed : ∀ slot, plan.packet.context.state.base.source slot ∈ pool registry context root limit := by
        rw [enabled.1.2.1]
        exact fun slot => old.1.1 (slot_source before.erased.current.context.state slot)
      have registrySame := enabled.1.1
      have visible : plan.packet.declaration ∈ plan.packet.registry.declarations := by
        simpa only [registrySame] using enabled.1.2.2.2.1
      have packetChecked : ∀ declaration ∈ plan.packet.registry.declarations,
          DeclarationChecked plan.packet.registry.constructors roles declaration := by
        rw [registrySame]; exact checkedFor checked source
      have reserved : GeneralNominalAllocation.reserved plan.packet.context.state plan.packet.registry plan.packet.site.occurrence.identity ⊆
          pool registry context root limit := by
        intro identity member
        obtain ⟨key,present,rfl⟩ := List.mem_map.mp member
        apply List.mem_append_right
        simpa only [GeneralNominalAllocation.source,config.1,registrySame,
          GeneralNominalCenteredSteps.initial,GeneralNominalCenteredSteps.initialAt,
          GeneralNominalSupport.initial,GeneralNominalSaturationState.initial] using
          allocation_member (seed := context.state.seed) _ parent key (registrySame ▸ present)
      refine ⟨⟨private_sources plan.packet visible (by simpa only [enabled.1.2.1] using old.1.1) reserved,?_⟩,?_⟩
      · intro site member output requested
        change site ∈ before.erased.current.sites ++ plan.packet.children.map (GeneralNominalSharedEmission.childSite plan.packet) at member
        rcases List.mem_append.mp member with member | member
        · exact old.1.2 site member output requested
        · obtain ⟨child,childMember,rfl⟩ := List.mem_map.mp member
          exact reserved (child_output_reserved plan.packet visible child childMember output requested)
      · intro site member
        change site ∈ before.erased.current.sites ++ plan.packet.children.map (GeneralNominalSharedEmission.childSite plan.packet) at member
        rcases List.mem_append.mp member with member | member
        · exact old.2 site member
        · obtain ⟨child,present,rfl⟩ := List.mem_map.mp member
          have result := child_enumerated context plan.packet packetChecked root parent visible
            enabled.1.2.2.2.2.1 enabled.1.2.2.2.2.2.1 listed config.1.symm config.2.1.symm config.2.2.symm child present
          simpa only [basis,registrySame,GeneralNominalSharedEmission.childSite] using result

theorem covers (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (parents : Parents registry context root limit state.erased)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.erased.current packet) :
    ∃ signature ∈ signatures checked source limit, Represents signature packet := by
  have facts := snapshot checked source path parents
  have config := configuration_trace path
  rw [← enabled.1.2.1] at config
  have listed : ∀ slot, packet.context.state.base.source slot ∈ pool registry context root limit := by
    rw [enabled.1.2.1]
    exact fun slot => facts.1.1 (slot_source state.erased.current.context.state slot)
  have same := enabled.1.1
  have visible : packet.declaration ∈ packet.registry.declarations := by
    simpa only [same] using enabled.1.2.2.2.1
  have packetChecked : ∀ declaration ∈ packet.registry.declarations,
      DeclarationChecked packet.registry.constructors roles declaration := by
    rw [same]; exact checkedFor checked source
  have member := GeneralNominalPacketCodes.encoded_member context packet packetChecked
    (facts.2 packet.site enabled.1.2.2.1) visible enabled.1.2.2.2.2.2.1 listed config.2.1.symm config.2.2.symm
  have represented := GeneralNominalPacketCodes.encode_represents context packet config.1.symm config.2.1.symm config.2.2.symm
  refine ⟨_,?_,represented⟩
  have mapped := (List.mem_map (f := GeneralNominalPacketCodes.signature context)).mpr ⟨_,member,rfl⟩
  subst registry
  exact mapped


theorem journal_parents
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (journal : GeneralNominalCanonicalHoleJournal.Journal context root state.erased inventory) :
    Parents registry context root (GeneralNominalCanonicalHoleJournal.inventoryMass inventory) state.erased := by
  intro packet member
  obtain ⟨depth,lineage⟩ := packets_lineage path packet member
  have descent := GeneralNominalCanonicalHoleJournal.history_descent journal.history lineage
  have bounded := GeneralNominalCanonicalHoleJournal.journal_bound journal
  exact GeneralNominalInvocationAncestry.bounded_enumerated
    (GeneralNominalPatersonLineage.lineage_ancestry lineage) (by omega)

end Yulang.GeneralNominalCenteredSnapshot
