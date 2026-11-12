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

/-- Every stored declaration was actually visible in the source registry.
This provenance statement survives administrative point replacement. -/
theorem packet_visible (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state) :
    ∀ packet ∈ state.current.packets, packet.declaration ∈ registry.declarations := by
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
      · exact enabled.1.2.2.2.1
      · exact ih packet old

/-- For a singleton declaration registry, the journal-key half of Joint follows
from actual provenance, with no Current or alias-equality assumption. -/
theorem singleton_choices (registry : Registry) (root : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state)
    (declaration : Declaration) (singleton : registry.declarations = [declaration]) :
    ∀ packet ∈ state.current.packets, packet.declaration.id = declaration.id := by
  intro packet member
  have visible := packet_visible registry root state formed packet member
  rw [singleton] at visible
  exact congrArg Declaration.id (List.mem_singleton.mp visible)

/-- In the singleton-registry reachable case, ONLY the simultaneous semantic
witness remains for Joint. It is not silently inferred from local selection. -/
theorem singleton_joint (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root state)
    (declaration : Declaration) (singleton : registry.declarations = [declaration])
    (simultaneous : ∃ model, Models state.current model ∧
      GeneralNominalJointCandidates.BranchAt registry state.current focus declaration.id model ∧
      ∀ site, GeneralNominalJointCandidates.Related state.current focus site →
        GeneralNominalJointCandidates.BranchAt registry state.current site.occurrence declaration.id model) :
    GeneralNominalJointCandidates.Joint registry state.current focus declaration.id := by
  refine ⟨?_,simultaneous⟩
  intro packet member _
  exact singleton_choices registry root state
    (GeneralNominalSupportBoundary.reachable_formed registry state root reachable)
    declaration singleton packet member

end Yulang.GeneralDictionarySupportJournal
