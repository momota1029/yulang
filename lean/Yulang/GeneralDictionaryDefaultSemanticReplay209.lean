import Yulang.GeneralDictionaryDefaultHeadTransport209
import Yulang.GeneralDictionaryDefaultOutputBridge209
import Yulang.GeneralDictionaryDefaultObserved209

set_option backward.isDefEq.respectTransparency false

/-! Historical packet replay need not retain the input-center names. Point
arguments transport actual schemas semantically; persistent report data is
still an explicit condition and arbitrary reobservation is not covered. -/
namespace Yulang.GeneralDictionaryDefaultSemanticReplay209
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalCenteredHeadMatEffects
open GeneralDictionaryDefaultBoundary208 (boundary)
open GeneralNominalCenteredHeadAllocEncoding (registry)
variable {roles : Roles.RoleDecls} {current historical : Plan roles}
variable {model : GeneralNominalCommonBridge.Assignment}

def recenter (plan : Plan roles) (site : Site roles)
    (same : site.occurrence = plan.packet.site.occurrence) : Plan roles := ⟨plan.packet,site,same⟩

 theorem recenter_holds (site : Site roles)
    (same : site.occurrence = historical.packet.site.occurrence)
    (point : ∀ index, (historical.input.occurrence.demand.arguments index).1 =
      (historical.input.occurrence.demand.arguments index).2)
    (center : site.Holds model)
    (old : GeneralNominalCenteredHeadMatStepPackets.Holds historical model) :
    GeneralNominalCenteredHeadMatStepPackets.Holds (recenter historical site same) model := by
  obtain ⟨head,input,binders,schema,equations,children⟩ := GeneralNominalCenteredHeadMatStepPackets.models_iff.mpr old
  apply GeneralNominalCenteredHeadMatStepPackets.models_iff.mp
  refine ⟨head,center,binders,?_,equations,children⟩
  apply GeneralDictionaryDefaultHeadTransport209.point_head_schema_transport
    (first := historical) (last := recenter historical site same) rfl rfl rfl
    (historical.input_exact.trans same.symm) point input center _ schema
  intro name
  exact GeneralDictionaryDefaultExpression209.equivalent_refl _

 theorem recenter_class (site : Site roles)
    (same : site.occurrence = historical.packet.site.occurrence)
    (point : ∀ index, (historical.input.occurrence.demand.arguments index).1 =
      (historical.input.occurrence.demand.arguments index).2)
    (center : site.Holds model) (input : historical.input.Holds model) :
    ClassEffects core focus historical model ↔ ClassEffects core focus (recenter historical site same) model := by
  have bodies : ∀ target body, BodyHolds historical target model body ↔
      BodyHolds (recenter historical site same) target model body := by
    intro target body
    apply GeneralDictionaryDefaultBodyTransport209.body_transport (first := historical)
      (last := recenter historical site same) rfl rfl
    · intro name; exact GeneralDictionaryDefaultExpression209.equivalent_refl _
    · exact GeneralDictionaryDefaultPointTransport209.centers_equivalent _ _
        (historical.input_exact.trans same.symm) point input center
  simp only [ClassEffects,bodies]
  rfl

 theorem recentered_data {state : State roles}
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key current)
    (member : historical ∈ state.core.plans)
    (declaration : current.packet.declaration = historical.packet.declaration)
    (same : current.input.occurrence = historical.packet.site.occurrence)
    (report : GeneralNominalReportErasure.erase current.packet.context.state
        (GeneralNominalPacketSupport.report current.packet) =
      GeneralNominalReportErasure.erase historical.packet.context.state
        (GeneralNominalPacketSupport.report historical.packet)) :
    GeneralNominalCenteredHeadMatPlanData.Same current (recenter historical current.input same) := by
  obtain ⟨start,initial,path⟩ := reachable
  have compiled := GeneralNominalCenteredHeadAllocBoundary.initial_compiled initial
  obtain ⟨context,labels,source,point,ground,coverage,rfl⟩ := compiled
  have built := GeneralDictionaryDefaultTrace208.built_trace path
  have old := GeneralDictionaryDefaultConfiguration209.stored built member
  exact ⟨frame.registry_eq.trans old.1.symm,declaration,rfl,
    ((congrArg (fun context : GeneralNominalCandidates.Context => context.state.seed) frame.context_eq).trans
      (GeneralDictionaryDefaultConfiguration209.seed built)).trans old.2.1.symm,
    (GeneralDictionaryDefaultConfiguration209.frame_constructors frame).trans old.2.2.2.symm,
    ((congrArg GeneralNominalCandidates.Context.interpretation frame.context_eq).trans
      (GeneralNominalCenteredHeadMatStepHistory.interpretation built)).trans old.2.2.1.symm,report⟩

 theorem certificate {state : State roles}
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key current)
    (member : historical ∈ state.core.plans)
    (keyEq : historical.packet.declaration.id = key)
    (occurrence : historical.packet.site.occurrence = focus)
    (point : ∀ index, (focus.demand.arguments index).1 = (focus.demand.arguments index).2)
    (report : GeneralNominalReportErasure.erase current.packet.context.state
        (GeneralNominalPacketSupport.report current.packet) =
      GeneralNominalReportErasure.erase historical.packet.context.state
        (GeneralNominalPacketSupport.report historical.packet))
    (valid : Models state model) :
    GeneralDictionaryTotalEvidence206.Certificate (registry value) state.core model focus key current.packet.children current := by
  have same := current.input_exact.trans (frame.occurrence_eq.trans occurrence.symm)
  have data := recentered_data reachable frame member
    (GeneralDictionaryDefaultOutputBridge209.declaration_of_key checked reachable frame member keyEq) same report
  have old := valid.2.2.2.2.1 historical member
  have center := valid.2.2.2.1 current.input frame.center_recorded
  have oldPoint := (historical.input_exact.trans occurrence).symm ▸ point
  have packet := recenter_holds current.input same oldPoint center old
  apply GeneralDictionaryTotalEvidence206.certificate_of_semantics frame rfl
  · exact GeneralDictionaryDefaultReinspection209.packet_reinspect data frame valid packet
  · exact GeneralDictionaryDefaultAvailability208.ready checked reachable frame
  · apply (GeneralDictionaryDefaultReinspection209.effects_same data).mpr
    exact (recenter_class current.input same oldPoint center
      (GeneralNominalCenteredHeadMatStepPackets.head_equations old).1).mp
      (occurrence ▸ GeneralDictionaryDefaultRecorded208.current_class reachable member valid)

 theorem nominal_report {state : State roles}
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key current)
    (member : historical ∈ state.core.plans)
    (keyEq : historical.packet.declaration.id = key)
    (occurrence : historical.packet.site.occurrence = focus)
    (refinement : GeneralNominalRefinements.Refines historical.packet.context.state current.packet.context.state)
    (shape : ∀ query ∈ GeneralNominalInspection.queries historical.packet.context.state
      historical.packet.context.interpretation historical.packet.declaration,
      GeneralNominalFinishedObservation197.Syntax query) :
    GeneralNominalReportErasure.erase current.packet.context.state
        (GeneralNominalPacketSupport.report current.packet) =
      GeneralNominalReportErasure.erase historical.packet.context.state
        (GeneralNominalPacketSupport.report historical.packet) := by
  have interpretation : current.packet.context.interpretation = historical.packet.context.interpretation := by
    obtain ⟨start,initial,path⟩ := reachable
    have compiled := GeneralNominalCenteredHeadAllocBoundary.initial_compiled initial
    obtain ⟨context,labels,source,point,ground,coverage,rfl⟩ := compiled
    have built := GeneralDictionaryDefaultTrace208.built_trace path
    have old := GeneralDictionaryDefaultConfiguration209.stored built member
    exact ((congrArg GeneralNominalCandidates.Context.interpretation frame.context_eq).trans
      (GeneralNominalCenteredHeadMatStepHistory.interpretation built)).trans old.2.2.1.symm
  exact GeneralDictionaryDefaultObserved209.report_equal refinement interpretation
    (GeneralDictionaryDefaultOutputBridge209.declaration_of_key checked reachable frame member keyEq)
    (frame.occurrence_eq.trans occurrence.symm)
    (GeneralDictionaryDefaultObserved209.located_stored reachable member)
    (frame.occurrence_eq.symm ▸ frame.located)
    (GeneralDictionaryDefaultObserved209.observed_stored reachable member shape)

/-- Nominal/variable heads under descriptor-preserving refinement now need
neither equal input-center names nor an assumed report equality. -/
 theorem nominal_certificate {state : State roles}
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key current)
    (member : historical ∈ state.core.plans)
    (keyEq : historical.packet.declaration.id = key)
    (occurrence : historical.packet.site.occurrence = focus)
    (point : ∀ index, (focus.demand.arguments index).1 = (focus.demand.arguments index).2)
    (refinement : GeneralNominalRefinements.Refines historical.packet.context.state current.packet.context.state)
    (shape : ∀ query ∈ GeneralNominalInspection.queries historical.packet.context.state
      historical.packet.context.interpretation historical.packet.declaration,
      GeneralNominalFinishedObservation197.Syntax query)
    (valid : Models state model) :
    GeneralDictionaryTotalEvidence206.Certificate (registry value) state.core model focus key current.packet.children current :=
  certificate checked reachable frame member keyEq occurrence point
    (nominal_report checked reachable frame member keyEq occurrence refinement shape) valid

 theorem nominal_evidence_node {state : State roles}
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key current)
    (member : historical ∈ state.core.plans)
    (keyEq : historical.packet.declaration.id = key)
    (occurrence : historical.packet.site.occurrence = focus)
    (point : ∀ index, (focus.demand.arguments index).1 = (focus.demand.arguments index).2)
    (refinement : GeneralNominalRefinements.Refines historical.packet.context.state current.packet.context.state)
    (shape : ∀ query ∈ GeneralNominalInspection.queries historical.packet.context.state
      historical.packet.context.interpretation historical.packet.declaration,
      GeneralNominalFinishedObservation197.Syntax query)
    (valid : Models state model)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryTotalEvidence206.Evidence (registry value) state.core model)
      current.packet.children dictionaries) :
    GeneralDictionaryTotalEvidence206.Evidence (registry value) state.core model focus (.node key dictionaries) :=
  GeneralDictionaryTotalEvidence206.evidence_node
    ⟨current,nominal_certificate checked reachable frame member keyEq occurrence point refinement shape valid⟩ given

 theorem generated_children {state : State roles}
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
    (reached : focus = root ∨ (boundary roles).Generated value state root focus)
    (childMember : child ∈ current.packet.children) : (boundary roles).Generated value state root child := by
  have same := current.input_exact.trans (frame.occurrence_eq.trans occurrence.symm)
  have data := recentered_data reachable frame member
    (GeneralDictionaryDefaultOutputBridge209.declaration_of_key checked reachable frame member keyEq) same report
  have children := GeneralNominalCenteredHeadMatPlanData.children data
  have done := GeneralDictionaryDefaultRecorded208.committed reachable member
  have parent : GeneralNominalSaturationState.Generated state.core.erased.current root focus :=
    reached.elim (fun same => same.symm ▸ GeneralNominalSaturationState.Generated.root) id
  exact .child parent (occurrence ▸ done.1.2 child (children ▸ childMember))

 theorem nominal_generated_children {state : State roles}
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key current)
    (member : historical ∈ state.core.plans)
    (keyEq : historical.packet.declaration.id = key)
    (occurrence : historical.packet.site.occurrence = focus)
    (refinement : GeneralNominalRefinements.Refines historical.packet.context.state current.packet.context.state)
    (shape : ∀ query ∈ GeneralNominalInspection.queries historical.packet.context.state
      historical.packet.context.interpretation historical.packet.declaration,
      GeneralNominalFinishedObservation197.Syntax query)
    (reached : focus = root ∨ (boundary roles).Generated value state root focus)
    (childMember : child ∈ current.packet.children) : (boundary roles).Generated value state root child :=
  generated_children checked reachable frame member keyEq occurrence
    (nominal_report checked reachable frame member keyEq occurrence refinement shape) reached childMember

end Yulang.GeneralDictionaryDefaultSemanticReplay209
