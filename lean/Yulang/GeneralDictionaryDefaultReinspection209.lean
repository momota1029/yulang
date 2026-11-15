import Yulang.GeneralDictionaryDefaultBodyTransport209
import Yulang.GeneralNominalCenteredHeadMatPlanData

set_option backward.isDefEq.respectTransparency false

/-! A genuine stored-parent replay fragment. Same is the explicit persistent
report-data condition, NOT a consequence of arbitrary improving reobservation.
The current plan need not be an element of the historical plan ledger. -/
namespace Yulang.GeneralDictionaryDefaultReinspection209
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadMatPlanData (Same)
open GeneralNominalCenteredHeadMatEffects
open GeneralDictionaryDefaultBoundary208 (boundary)
open GeneralNominalCenteredHeadAllocEncoding (registry)
variable {roles : Roles.RoleDecls} {state : State roles} {current historical : Plan roles}
variable {model : GeneralNominalCommonBridge.Assignment}

 theorem body_same (same : Same current historical) :
    BodyHolds current target model body ↔ BodyHolds historical target model body := by
  apply GeneralDictionaryDefaultBodyTransport209.body_transport
  · exact congrArg GeneralDeclarations.Registry.constructors same.registry
  · exact same.interpretation
  · intro name
    rw [GeneralNominalCenteredHeadMatPlanData.binder same name]
    exact GeneralDictionaryDefaultExpression209.equivalent_refl _
  · intro index
    rw [same.input]
    exact GeneralDictionaryDefaultExpression209.equivalent_refl _

 theorem effects_same (same : Same current historical) :
    ClassEffects core focus current model ↔ ClassEffects core focus historical model := by
  simp only [ClassEffects,same.declaration,body_same same]

 theorem packet_reinspect (same : Same current historical)
    (frame : GeneralNominalCenteredHeadOutputs.Frame value state.core focus key current)
    (valid : Models state model)
    (old : GeneralNominalCenteredHeadMatStepPackets.Holds historical model) :
    GeneralNominalCenteredHeadMatStepPackets.Holds current model :=
  ⟨frame.context_eq.symm ▸ valid.1,(GeneralNominalCenteredHeadMatPlanData.delta same model).mpr old.2⟩

 theorem certificate (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key current)
    (present : historical ∈ state.core.plans) (same : Same current historical)
    (valid : Models state model) :
    GeneralDictionaryTotalEvidence206.Certificate (registry value) state.core model focus key current.packet.children current := by
  apply GeneralDictionaryTotalEvidence206.certificate_of_semantics frame rfl
  · exact packet_reinspect same frame valid (valid.2.2.2.2.1 historical present)
  · exact GeneralDictionaryDefaultAvailability208.ready checked reachable frame
  · have output := GeneralDictionaryDefaultRecorded208.current_class reachable present valid
    have focusEq : historical.packet.site.occurrence = focus :=
      (GeneralNominalCenteredHeadMatPlanData.occurrence same).symm.trans frame.occurrence_eq
    exact (effects_same same).mpr (focusEq ▸ output)

 theorem evidence_node (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key current)
    (present : historical ∈ state.core.plans) (same : Same current historical)
    (valid : Models state model)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryTotalEvidence206.Evidence (registry value) state.core model)
      current.packet.children dictionaries) :
    GeneralDictionaryTotalEvidence206.Evidence (registry value) state.core model focus (.node key dictionaries) :=
  GeneralDictionaryTotalEvidence206.evidence_node ⟨current,certificate checked reachable frame present same valid⟩ given

 theorem generated_children (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key current)
    (present : historical ∈ state.core.plans) (same : Same current historical)
    (reached : focus = root ∨ (boundary roles).Generated value state root focus)
    (member : child ∈ current.packet.children) : (boundary roles).Generated value state root child := by
  have done := GeneralDictionaryDefaultRecorded208.committed reachable present
  have childMember := GeneralNominalCenteredHeadMatPlanData.children same ▸ member
  have parent : GeneralNominalSaturationState.Generated state.core.erased.current root focus :=
    reached.elim (fun same => same.symm ▸ GeneralNominalSaturationState.Generated.root) id
  have focusEq : historical.packet.site.occurrence = focus :=
    (GeneralNominalCenteredHeadMatPlanData.occurrence same).symm.trans frame.occurrence_eq
  exact .child parent (focusEq ▸ done.1.2 child childMember)

end Yulang.GeneralDictionaryDefaultReinspection209
