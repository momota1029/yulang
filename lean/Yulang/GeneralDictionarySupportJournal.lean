import Yulang.GeneralNominalSupportBoundary

/-! Historical dictionary semantics survive actual support-aware transitions.
This intentionally retains packet.context, not the current observation context. -/
namespace Yulang.GeneralDictionarySupportJournal
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps
variable {roles : Roles.RoleDecls}

/-- Actual support-aware source formation preserves historical packet instances
and their generated child edges, even across certified reobservation. -/
theorem recorded_instances (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state) :
    ∀ packet ∈ state.current.packets,
      (∀ model, Models state.current model → GeneralDictionaryRecursiveEvidence.Instance
        packet.registry packet.context model packet.site.occurrence packet.declaration.id packet.children) ∧
      ∀ child ∈ packet.children, Generated state.current packet.site.occurrence child := by
  induction formed with
  | initial context source => intro packet member; cases member
  | @update before after formed update ih =>
    obtain ⟨focus,generated,action⟩ := update
    have retain : ∀ packet ∈ before.current.packets,
        (∀ model, Models after.current model → GeneralDictionaryRecursiveEvidence.Instance
          packet.registry packet.context model packet.site.occurrence packet.declaration.id packet.children) ∧
        ∀ child ∈ packet.children, Generated after.current packet.site.occurrence child := by
      intro packet member
      have old := ih packet member
      exact ⟨fun model valid => old.1 model
          (GeneralNominalReobservationSteps.at_models (at_old action) model valid),
        fun child present => GeneralNominalSaturationSteps.generated_monotone
          (GeneralNominalReobservationSteps.at_extends (at_old action)).journal (old.2 child present)⟩
    intro packet member
    cases action with
    | administrative _ _ admin =>
      cases admin <;> exact retain packet member
    | merge => exact retain packet member
    | install installed support enabled novel guard =>
      rcases List.mem_cons.mp member with rfl | old
      · exact GeneralDictionaryFeedbackEvidence.installed_trace_instance registry root before.current _ packet enabled .refl
      · exact retain packet old

/-- Every packet in the guarded journal was installed from the source registry. -/
theorem packet_registry (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state) :
    ∀ packet ∈ state.current.packets, packet.registry = registry := by
  induction formed with
  | initial context source => intro packet member; cases member
  | update formed update ih =>
    intro packet member
    obtain ⟨focus,generated,action⟩ := update
    cases action with
    | administrative _ _ admin => cases admin <;> exact ih packet member
    | merge => exact ih packet member
    | install installed support enabled novel guard =>
      rcases List.mem_cons.mp member with rfl | old
      · exact enabled.1.1
      · exact ih packet old

/-- Child evidence at one packet's stored context completes that recorded node.
No claim is made that contexts of different packets agree. -/
theorem recorded_evidence (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state)
    (packet : Packet roles) (recorded : packet ∈ state.current.packets)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry packet.context model) packet.children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry packet.context model packet.site.occurrence
      (.node packet.declaration.id dictionaries) := by
  have instanceRule := (recorded_instances registry root state formed packet recorded).1 model valid
  rw [packet_registry registry root state formed packet recorded] at instanceRule
  exact GeneralDictionaryRecursiveEvidence.evidence_node registry packet.context model packet.site.occurrence
    packet.declaration.id packet.children dictionaries instanceRule given

end Yulang.GeneralDictionarySupportJournal
