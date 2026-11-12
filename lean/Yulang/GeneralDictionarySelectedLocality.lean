import Yulang.GeneralDictionaryRefreshDescriptors
import Yulang.GeneralDictionaryInspectionLocality

/-! Only the payload's selected declaration key must retain its inspection
footprint. No report-preservation premise is imposed on other candidates of the same role. Occupancy of
that finite footprint and actual refinement suffice; no report equality,
selection stability, Joint or final evidence is assumed. -/
namespace Yulang.GeneralDictionarySelectedLocality
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveCandidates (Context arguments report RequestReady)
open GeneralDictionaryInspectionTransport GeneralDictionaryInspectionLocality

def FootprintFor (registry : Registry) (context : Context) (next : Observation context.state)
    (root : Occurrence roles) (key : Nat) : Prop :=
  ∀ declaration ∈ registry.declarations, declaration.id = key → declaration.role = root.demand.role →
    ∀ bounds, arguments context root = some bounds →
      ∀ slot ∈ footprints context.state
        (GeneralNominalInspection.queries context.state context.interpretation declaration) bounds,
        next.nominals slot = context.state.nominals slot

def OccupiedFor (registry : Registry) (context : Context) (root : Occurrence roles) (key : Nat) : Prop :=
  ∀ declaration ∈ registry.declarations, declaration.id = key → declaration.role = root.demand.role →
    ∀ bounds, arguments context root = some bounds →
      ∀ slot ∈ footprints context.state
        (GeneralNominalInspection.queries context.state context.interpretation declaration) bounds,
        ∃ descriptor, context.state.nominals slot = some descriptor

theorem footprint_of_occupied (registry : Registry) (context : Context)
    (next : Observation context.state) (root : Occurrence roles) (key : Nat)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (occupied : OccupiedFor registry context root key) : FootprintFor registry context next root key := by
  intro declaration visible identity role bounds located slot member
  obtain ⟨descriptor,recorded⟩ := occupied declaration visible identity role bounds located slot member
  exact (GeneralDictionaryRefreshDescriptors.descriptor_preserved context next refinement slot descriptor recorded).trans recorded.symm

theorem instance_of_footprint (registry : Registry) (context : Context)
    (next : Observation context.state) (view : next.view = context.state.view)
    (model : Assignment) (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (same : FootprintFor registry context next root key)
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (old : GeneralDictionaryRecursiveEvidence.Instance registry context model root key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry (reobserve context next) model root key children := by
  obtain ⟨declaration,visible,checked,identity,role,bounds,located,finished,ready,emitted,metadata,branch⟩ := old
  have reports := report_local context next view declaration bounds (same declaration visible identity role bounds located)
  refine ⟨declaration,visible,checked,identity,role,bounds,located,?_,?_,?_,metadata,
    branch_of_report registry context next root declaration checked bounds model reports valid branch⟩
  · rw [reports,transferred_finished]
    exact finished
  · unfold RequestReady at ready ⊢
    rw [generated_eq registry context next root declaration checked bounds reports]
    exact ready
  · rw [reports,transferred_bindings]
    exact emitted

theorem instance_of_occupied (registry : Registry) (context : Context)
    (next : Observation context.state) (view : next.view = context.state.view)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (model : Assignment) (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (occupied : OccupiedFor registry context root key)
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (old : GeneralDictionaryRecursiveEvidence.Instance registry context model root key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry (reobserve context next) model root key children :=
  instance_of_footprint registry context next view model root key children
    (footprint_of_occupied registry context next root key refinement occupied) valid old

/-- Only the recorded packet's key needs a populated footprint. The actual
refresh pulls the final model back to SourceFormed's journal facts. -/
theorem recorded_instance (registry : Registry) (root : Occurrence roles)
    (before : State roles) (formed : GeneralNominalFeedbackSteps.SourceFormed registry root before)
    (packet : Packet roles) (recorded : packet ∈ before.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context before.context)
    (next : Observation before.context.state) (view : next.view = before.context.state.view)
    (refresh : GeneralNominalCycleSteps.Refresh before (reobserve before.context next))
    (occupied : OccupiedFor registry before.context packet.site.occurrence packet.declaration.id)
    (model : Assignment) (valid : Models (regenerate before (reobserve before.context next)) model) :
    GeneralDictionaryRecursiveEvidence.Instance registry (reobserve before.context next) model
      packet.site.occurrence packet.declaration.id packet.children := by
  have earlier := (GeneralNominalCycleSteps.refresh_models refresh model).mp valid
  have old := (GeneralDictionaryFeedbackEvidence.sourceFormed_recorded_instances registry root before
    formed packet recorded).1 model earlier
  rw [GeneralDictionaryFeedbackEvidence.sourceFormed_packet_registry registry root before formed packet recorded] at old
  apply instance_of_occupied registry before.context next view refresh.refines model
    packet.site.occurrence packet.declaration.id packet.children occupied valid.1
  exact GeneralDictionaryOrdinaryTrace.instance_extension registry packet.context before.context growth
    model earlier.1 _ _ _ old

end Yulang.GeneralDictionarySelectedLocality
