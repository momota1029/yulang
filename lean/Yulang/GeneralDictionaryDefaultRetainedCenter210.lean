import Yulang.GeneralDictionaryDefaultSemanticReplay209

set_option backward.isDefEq.respectTransparency false

/-! Existential certificates may reuse a historical input center. Arbitrary
intervals are retained; this is not independence of all frame representatives. -/
namespace Yulang.GeneralDictionaryDefaultRetainedCenter210
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionaryDefaultBoundary208 (boundary)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralDictionaryDefaultSemanticReplay209 (recenter)
variable {roles : Roles.RoleDecls} {state : State roles} {current historical : Plan roles}

 theorem stored_input_built
    (built : GeneralNominalCenteredHeadMatStepHistory.Built value context root state)
    (member : historical ∈ state.core.plans) : historical.input ∈ state.core.sites := by
  induction built with
  | initial => cases member
  | install prior effect snapshot registryEq ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact List.mem_append_left _ (snapshot ▸ effect.frame.center_recorded)
      · exact List.mem_append_left _ (ih member)
  | merge _ _ _ _ ih => exact ih member
  | context _ _ _ _ ih => exact ih member

 theorem stored_input (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (member : historical ∈ state.core.plans) : historical.input ∈ state.core.sites := by
  obtain ⟨start,initial,path⟩ := reachable
  obtain ⟨context,labels,source,point,ground,coverage,rfl⟩ :=
    GeneralNominalCenteredHeadAllocBoundary.initial_compiled initial
  exact stored_input_built (GeneralDictionaryDefaultTrace208.built_trace path) member

 theorem recenter_frame
    (frame : GeneralNominalCenteredHeadOutputs.Frame reg core focus key current)
    (site : Site roles) (recorded : site ∈ core.sites)
    (same : site.occurrence = current.packet.site.occurrence) :
    GeneralNominalCenteredHeadOutputs.Frame reg core focus key (recenter current site same) := by
  exact { frame with center_recorded := recorded }

 theorem certificate
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key current)
    (member : historical ∈ state.core.plans)
    (keyEq : historical.packet.declaration.id = key)
    (occurrence : historical.packet.site.occurrence = focus)
    (report : GeneralNominalReportErasure.erase current.packet.context.state
        (GeneralNominalPacketSupport.report current.packet) =
      GeneralNominalReportErasure.erase historical.packet.context.state
        (GeneralNominalPacketSupport.report historical.packet))
    (valid : Models state model) :
    ∃ witness, GeneralDictionaryTotalEvidence206.Certificate (registry value) state.core model
      focus key current.packet.children witness ∧ witness.input = historical.input := by
  have same := historical.input_exact.trans (occurrence.trans frame.occurrence_eq.symm)
  let witness := recenter current historical.input same
  have currentFrame := recenter_frame frame historical.input (stored_input reachable member) same
  have declaration := GeneralDictionaryDefaultOutputBridge209.declaration_of_key checked reachable frame member keyEq
  have data := GeneralDictionaryDefaultConfiguration209.reinspection_data reachable currentFrame member declaration rfl report
  exact ⟨witness,GeneralDictionaryDefaultReinspection209.certificate checked reachable currentFrame member data valid,rfl⟩

 theorem evidence_instance
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key current)
    (member : historical ∈ state.core.plans)
    (keyEq : historical.packet.declaration.id = key)
    (occurrence : historical.packet.site.occurrence = focus)
    (report : GeneralNominalReportErasure.erase current.packet.context.state
        (GeneralNominalPacketSupport.report current.packet) =
      GeneralNominalReportErasure.erase historical.packet.context.state
        (GeneralNominalPacketSupport.report historical.packet))
    (valid : Models state model) :
    GeneralDictionaryTotalEvidence206.Instance (registry value) state.core model focus key current.packet.children := by
  obtain ⟨witness,certificate,_⟩ := certificate checked reachable frame member keyEq occurrence report valid
  exact ⟨witness,certificate⟩

end Yulang.GeneralDictionaryDefaultRetainedCenter210
