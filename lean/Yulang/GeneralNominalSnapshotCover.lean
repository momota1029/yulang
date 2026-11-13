import Yulang.GeneralNominalActualBudget

/-! Finite literal reports from one bounded journal. No bound on other traces
is required; the finite list may change when a source hole is eliminated. -/
namespace Yulang.GeneralNominalSnapshotCover
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualInspectionSteps
open GeneralNominalInvocationAncestry GeneralNominalActualTraceSupport
open GeneralNominalAllocationSupport GeneralNominalOccurrenceEnumeration
open GeneralNominalSharedBudget (Signature Represents)

def Parents (registry : Registry) (context : GeneralNominalCandidates.Context) (root : Occurrence roles)
    (limit : Nat) (state : Tracked roles) : Prop :=
  ∀ packet ∈ state.current.packets,
    packet.site.occurrence.identity ∈ frontier registry context.state.seed root.identity limit

theorem snapshot (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (parents : Parents registry context root limit state) :
    Supported state.current (pool registry context root limit) ∧
      ∀ site ∈ state.current.sites, site.occurrence ∈ basis checked source limit := by
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
    have formed := formed_trace (.initial context source) path
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action =>
      cases action with
      | enqueue linked absent =>
        obtain ⟨site,member,same⟩ := GeneralNominalSharedSteps.generated_registered (formed_shared formed) generated
        exact False.elim (absent site member same)
      | refresh after certificate identity member unknown known =>
        have old := ih parents
        exact ⟨⟨fun _ member => old.1.1 (certificate.support _ member),old.1.2⟩,old.2⟩
      | equate first last one two equal novel =>
        have old := ih parents
        exact ⟨⟨fun _ member => administrative_support before.current old.1
          (GeneralNominalFeedbackAdministrative.sources_bounded (registry := registry) (.equate focus first last one two equal novel) member),old.1.2⟩,old.2⟩
      | reobserve => exact ih parents
    | merge first last support one two same novel guard =>
      have old := ih parents
      exact ⟨⟨fun _ member => administrative_support before.current old.1
        (GeneralNominalFeedbackAdministrative.sources_bounded (registry := registry) (.merge first last one two same novel) member),old.1.2⟩,old.2⟩
    | install packet support enabled novel guard =>
      have old := ih (fun prior member => parents prior (List.mem_cons_of_mem _ member))
      have parent := parents packet (List.mem_cons_self ..)
      have config := configuration_trace path
      rw [← enabled.1.2.1] at config
      have listed : ∀ slot, packet.context.state.base.source slot ∈ pool registry context root limit := by
        rw [enabled.1.2.1]
        exact fun slot => old.1.1 (slot_source before.current.context.state slot)
      have registrySame := enabled.1.1
      have visible : packet.declaration ∈ packet.registry.declarations := by
        simpa only [registrySame] using enabled.1.2.2.2.1
      have packetChecked : ∀ declaration ∈ packet.registry.declarations,
          DeclarationChecked packet.registry.constructors roles declaration := by
        rw [registrySame]; exact checkedFor checked source
      have reserved : GeneralNominalAllocation.reserved packet.context.state packet.registry packet.site.occurrence.identity ⊆
          pool registry context root limit := by
        intro identity member
        obtain ⟨key,present,rfl⟩ := List.mem_map.mp member
        apply List.mem_append_right
        simpa only [GeneralNominalAllocation.source,config.1,registrySame,
          GeneralNominalSupport.initial,GeneralNominalSaturationState.initial] using
          allocation_member (seed := context.state.seed) _ parent key (registrySame ▸ present)
      refine ⟨⟨private_sources packet visible (by simpa only [enabled.1.2.1] using old.1.1) reserved,?_⟩,?_⟩
      · intro site member output requested
        change site ∈ before.current.sites ++ packet.children.map (GeneralNominalSharedEmission.childSite packet) at member
        rcases List.mem_append.mp member with member | member
        · exact old.1.2 site member output requested
        · obtain ⟨child,childMember,rfl⟩ := List.mem_map.mp member
          exact reserved (child_output_reserved packet visible child childMember output requested)
      · intro site member
        change site ∈ before.current.sites ++ packet.children.map (GeneralNominalSharedEmission.childSite packet) at member
        rcases List.mem_append.mp member with member | member
        · exact old.2 site member
        · obtain ⟨child,present,rfl⟩ := List.mem_map.mp member
          have result := child_enumerated context packet packetChecked root parent visible
            enabled.1.2.2.2.2.1 enabled.1.2.2.2.2.2.1 listed config.1.symm config.2.1.symm config.2.2.symm child present
          simpa only [basis,registrySame,GeneralNominalSharedEmission.childSite] using result

def signatures (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles)) (limit : Nat) : List (Signature roles) :=
  (GeneralNominalPacketCodes.codes context registry (checkedFor checked source)
    (basis checked source limit) (pool registry context root limit)).map (GeneralNominalPacketCodes.signature context)

theorem covers (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (parents : Parents registry context root limit state)
    (enabled : GeneralNominalFeedbackSteps.Installable registry state.current packet) :
    ∃ signature ∈ signatures checked source limit, Represents signature packet := by
  have facts := snapshot checked source path parents
  have config := configuration_trace path
  rw [← enabled.1.2.1] at config
  have listed : ∀ slot, packet.context.state.base.source slot ∈ pool registry context root limit := by
    rw [enabled.1.2.1]
    exact fun slot => facts.1.1 (slot_source state.current.context.state slot)
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

end Yulang.GeneralNominalSnapshotCover
