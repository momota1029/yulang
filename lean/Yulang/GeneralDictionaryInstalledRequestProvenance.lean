import Yulang.GeneralDictionaryRequestProvenanceTrace

/-! An actual installation extends request provenance with its emitted batch.
The targets may be newly allocated or absent from the initial carrier. The
only materialization restriction here is variable-free syntax, not semantic
validity. Previous provenance survives the actual transition. -/
namespace Yulang.GeneralDictionaryInstalledRequestProvenance
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalMaterialization
open GeneralDictionaryRequestProvenance
variable {roles : Roles.RoleDecls}

theorem singleton_variables (state : GeneralNominalState.State)
    (interpretation : GeneralNominalInspection.Interpretation) (batch : List Request)
    (closed : (generated state interpretation batch).variables = [])
    (request : Request) (member : request ∈ batch) :
    (generated state interpretation [request]).variables = [] := by
  induction batch with
  | nil => cases member
  | cons first rest ih =>
    rw [GeneralDictionaryRecordedBatchModels.generated_cons] at closed
    have both : (generated state interpretation [first]).variables = [] ∧
        (generated state interpretation rest).variables = [] := List.append_eq_nil_iff.mp closed
    rcases List.mem_cons.mp member with rfl | present
    · exact both.1
    · exact ih both.2 present

theorem packet_covered (state : State roles) (packet : Packet roles)
    (recorded : packet ∈ state.packets) (batch : List Request)
    (included : ∀ request ∈ batch, request ∈ requests packet.context.state packet.registry
      packet.site.occurrence packet.declaration packet.checked packet.bindings)
    (closed : (generated packet.context.state packet.context.interpretation batch).variables = []) :
    GeneralDictionaryRecordedBatchModels.Covered state batch := by
  intro request member
  exact ⟨packet,recorded,included request member,singleton_variables _ _ batch closed request member⟩

theorem installed_supported (registry : Registry) (root : Occurrence roles)
    (before : Tracked roles) (packet : Packet roles) (support : List (Occurrence roles))
    (closed : (GeneralNominalPacketSupport.namedSchema packet).variables = []) :
    Supported registry root (GeneralNominalValueSteps.install before packet support)
      (requests packet.context.state packet.registry packet.site.occurrence
        packet.declaration packet.checked packet.bindings) := by
  apply supported_of_recorded
  apply packet_covered _ packet List.mem_cons_self _ (fun _ member => member)
  exact closed

/-- Incremental construction from the real update, with no final-batch coverage
assumption. Repeating this theorem collects output requests from many packets. -/
theorem supported_install_append (registry : Registry) (root : Occurrence roles)
    (before : Tracked roles) (packet : Packet roles) (support : List (Occurrence roles))
    (step : GeneralNominalValueSteps.Step registry root before
      (GeneralNominalValueSteps.install before packet support))
    (batch : List Request) (prior : Supported registry root before batch)
    (closed : (GeneralNominalPacketSupport.namedSchema packet).variables = []) :
    Supported registry root (GeneralNominalValueSteps.install before packet support)
      (batch ++ requests packet.context.state packet.registry packet.site.occurrence
        packet.declaration packet.checked packet.bindings) :=
  (supported_append registry root _ _ _).mpr
    ⟨GeneralDictionaryRequestProvenanceTrace.supported_step registry root before _ step batch prior,
      installed_supported registry root before packet support closed⟩
end Yulang.GeneralDictionaryInstalledRequestProvenance
