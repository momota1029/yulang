import Yulang.GeneralDictionaryDefaultConfiguration209
import Yulang.GeneralNominalSlotTransport198

set_option backward.isDefEq.respectTransparency false

/-! Descriptor-preserving nominal-head reinspection. The old observed input
trace is concrete; total output expressions and role defaults are unrestricted.
Arbitrary improving reobservation is deliberately not included. -/
namespace Yulang.GeneralDictionaryDefaultObserved209
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
open GeneralNominalRefinements (Refines)
open GeneralNominalReportErasure (erase)
open GeneralDictionaryDefaultBoundary208 (boundary)
open GeneralNominalCenteredHeadAllocEncoding (registry)
variable {roles : Roles.RoleDecls} {state : State roles} {current historical : Plan roles}

 theorem erase_report (refinement : Refines before after)
    (report : GeneralNominalRecursiveInspection.Report before) :
    erase after (GeneralNominalSlotReport198.report refinement.base.embed report) = erase before report := by
  simp [GeneralNominalReportErasure.erase,GeneralNominalSlotReport198.report,GeneralNominalSlotReport198.capture,
    GeneralNominalReportErasure.interval,GeneralNominalSlotObservation198.bounds,
    List.map_map,refinement.base.source]

 theorem located_stored (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (member : historical ∈ state.core.plans) :
    GeneralNominalRecursiveCandidates.arguments historical.packet.context
      (GeneralNominalCenteredHeadCandidates.inputs historical.packet.site.occurrence) = some historical.packet.bounds := by
  obtain ⟨effect,present,same⟩ := (GeneralDictionaryDefaultRecorded208.recorded reachable).2 historical member
  exact same ▸ effect.frame.located

 theorem report_equal
    (refinement : Refines historical.packet.context.state current.packet.context.state)
    (interpretation : current.packet.context.interpretation = historical.packet.context.interpretation)
    (declaration : current.packet.declaration = historical.packet.declaration)
    (occurrence : current.packet.site.occurrence = historical.packet.site.occurrence)
    (oldLocated : GeneralNominalRecursiveCandidates.arguments historical.packet.context
      (GeneralNominalCenteredHeadCandidates.inputs historical.packet.site.occurrence) = some historical.packet.bounds)
    (currentLocated : GeneralNominalRecursiveCandidates.arguments current.packet.context
      (GeneralNominalCenteredHeadCandidates.inputs current.packet.site.occurrence) = some current.packet.bounds)
    (observed : GeneralNominalRefinementTrace197.ObservedMany historical.packet.context.state
      (GeneralNominalInspection.queries historical.packet.context.state historical.packet.context.interpretation
        historical.packet.declaration) historical.packet.bounds) :
    erase current.packet.context.state (GeneralNominalPacketSupport.report current.packet) =
      erase historical.packet.context.state (GeneralNominalPacketSupport.report historical.packet) := by
  have located := GeneralDictionaryRefinedLocations.arguments _ _ refinement _ _ oldLocated
  rw [← occurrence] at located
  have equal : current.packet.bounds = historical.packet.bounds.map
      (GeneralNominalSlotObservation198.bounds refinement.base.embed) :=
    Option.some.inj (currentLocated.symm.trans located)
  unfold GeneralNominalPacketSupport.report
  rw [declaration,equal,GeneralNominalSlotFacts198.candidate_report refinement interpretation observed]
  exact erase_report refinement _

 theorem reinspection_data
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key current)
    (member : historical ∈ state.core.plans)
    (declaration : current.packet.declaration = historical.packet.declaration)
    (input : current.input = historical.input)
    (refinement : Refines historical.packet.context.state current.packet.context.state)
    (observed : GeneralNominalRefinementTrace197.ObservedMany historical.packet.context.state
      (GeneralNominalInspection.queries historical.packet.context.state historical.packet.context.interpretation
        historical.packet.declaration) historical.packet.bounds) :
    GeneralNominalCenteredHeadMatPlanData.Same current historical := by
  have occurrence := current.input_exact.symm.trans ((congrArg Site.occurrence input).trans historical.input_exact)
  have metadata : current.packet.context.interpretation = historical.packet.context.interpretation := by
    obtain ⟨start,initial,path⟩ := reachable
    have compiled := GeneralNominalCenteredHeadAllocBoundary.initial_compiled initial
    obtain ⟨context,labels,source,point,ground,coverage,rfl⟩ := compiled
    have built := GeneralDictionaryDefaultTrace208.built_trace path
    have old := GeneralDictionaryDefaultConfiguration209.stored built member
    exact ((congrArg GeneralNominalCandidates.Context.interpretation frame.context_eq).trans
      (GeneralNominalCenteredHeadMatStepHistory.interpretation built)).trans old.2.2.1.symm
  apply GeneralDictionaryDefaultConfiguration209.reinspection_data reachable frame member declaration input
  exact report_equal refinement metadata declaration occurrence (located_stored reachable member)
    (frame.occurrence_eq.symm ▸ frame.located) observed

 theorem observed_stored
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (member : historical ∈ state.core.plans)
    (shape : ∀ query ∈ GeneralNominalInspection.queries historical.packet.context.state
      historical.packet.context.interpretation historical.packet.declaration,
      GeneralNominalFinishedObservation197.Syntax query) :
    GeneralNominalRefinementTrace197.ObservedMany historical.packet.context.state
      (GeneralNominalInspection.queries historical.packet.context.state historical.packet.context.interpretation
        historical.packet.declaration) historical.packet.bounds := by
  obtain ⟨effect,present,same⟩ := (GeneralDictionaryDefaultRecorded208.recorded reachable).2 historical member
  subst historical
  apply GeneralNominalFinishedObservation197.many_observed_of_finished (origins := fun _ => none) (index := 0) shape
  have prepared := effect.frame.prepared
  rw [← effect.frame.context_eq] at prepared
  obtain ⟨_,_,_,bounds,located,finished,_⟩ := prepared
  have equal := Option.some.inj (located.symm.trans effect.frame.located)
  subst bounds
  exact finished

/-- Restricted-head replay, with no old or new certificate supplied. Default
and explicit output expressions remain total and may contain unions/records. -/
 theorem nominal_certificate
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key current)
    (member : historical ∈ state.core.plans)
    (declaration : current.packet.declaration = historical.packet.declaration)
    (input : current.input = historical.input)
    (refinement : Refines historical.packet.context.state current.packet.context.state)
    (shape : ∀ query ∈ GeneralNominalInspection.queries historical.packet.context.state
      historical.packet.context.interpretation historical.packet.declaration,
      GeneralNominalFinishedObservation197.Syntax query)
    (valid : Models state model) :
    GeneralDictionaryTotalEvidence206.Certificate (registry value) state.core model focus key current.packet.children current :=
  GeneralDictionaryDefaultReinspection209.certificate checked reachable frame member
    (reinspection_data reachable frame member declaration input refinement (observed_stored reachable member shape)) valid

 theorem nominal_evidence_node
    (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key current)
    (member : historical ∈ state.core.plans)
    (declaration : current.packet.declaration = historical.packet.declaration)
    (input : current.input = historical.input)
    (refinement : Refines historical.packet.context.state current.packet.context.state)
    (shape : ∀ query ∈ GeneralNominalInspection.queries historical.packet.context.state
      historical.packet.context.interpretation historical.packet.declaration,
      GeneralNominalFinishedObservation197.Syntax query)
    (valid : Models state model)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryTotalEvidence206.Evidence (registry value) state.core model)
      current.packet.children dictionaries) :
    GeneralDictionaryTotalEvidence206.Evidence (registry value) state.core model focus (.node key dictionaries) :=
  GeneralDictionaryTotalEvidence206.evidence_node
    ⟨current,nominal_certificate checked reachable frame member declaration input refinement shape valid⟩ given

 theorem nominal_generated_children
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (frame : GeneralNominalCenteredHeadOutputs.Frame (registry value) state.core focus key current)
    (member : historical ∈ state.core.plans)
    (declaration : current.packet.declaration = historical.packet.declaration)
    (input : current.input = historical.input)
    (refinement : Refines historical.packet.context.state current.packet.context.state)
    (shape : ∀ query ∈ GeneralNominalInspection.queries historical.packet.context.state
      historical.packet.context.interpretation historical.packet.declaration,
      GeneralNominalFinishedObservation197.Syntax query)
    (reached : focus = root ∨ (boundary roles).Generated value state root focus)
    (childMember : child ∈ current.packet.children) : (boundary roles).Generated value state root child :=
  GeneralDictionaryDefaultReinspection209.generated_children reachable frame member
    (reinspection_data reachable frame member declaration input refinement (observed_stored reachable member shape))
    reached childMember

end Yulang.GeneralDictionaryDefaultObserved209
