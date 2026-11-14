import Yulang.GeneralDictionaryAgreedEvidence174
import Yulang.GeneralDictionaryFinishedEvidence

/-! Same-model current source evidence after one actual fixed-carrier,
fixed-view refresh following an ordinary actual trace. Historical ordinary
extension is required only BEFORE refresh. No extension is asserted afterwards.
This is a recorded-parent transport theorem, not arbitrary reobservation,
carrier/view-changing refresh, recursive dictionary completion, or general B4. -/
namespace Yulang.GeneralDictionaryAgreedRefresh174
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionaryRecursiveEvidence
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralDictionaryInspectionTransport
open GeneralDictionaryAgreedEvidence174
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

abbrev refreshed (before : Tracked roles) (next : Observation before.current.context.state) :
    Tracked roles :=
  {before with current := regenerate before.current (reobserve before.current.context next)}

/-- The final journal model also models the earlier journal by the actual
Refresh certificate. Stored packet evidence and finished inspection transport
use this SAME assignment; no existential branch model is substituted. -/
theorem recorded_instance (before : Tracked roles)
    (formed : GeneralNominalActualInspectionSteps.SourceFormed registry root before)
    (packet : Packet roles) (member : packet ∈ before.current.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context before.current.context)
    (next : Observation before.current.context.state)
    (view : next.view = before.current.context.state.view)
    (certificate : GeneralNominalCycleSteps.Refresh before.current (reobserve before.current.context next))
    (model : Assignment) (valid : Models (refreshed before next).current model) :
    Instance registry (refreshed before next).current.context model
      packet.site.occurrence packet.declaration.id packet.children := by
  have earlier := (GeneralNominalCycleSteps.refresh_models certificate model).mp valid
  have old := GeneralDictionarySharedRecordedEvidence.current_instance
    (GeneralNominalActualInspectionSteps.formed_shared formed) packet member growth model earlier
  exact GeneralDictionaryFinishedEvidence.instance_refinement registry before.current.context next
    view certificate.refines model valid.1 _ _ _ old

theorem recorded_evidence (before : Tracked roles)
    (formed : GeneralNominalActualInspectionSteps.SourceFormed registry root before)
    (packet : Packet roles) (member : packet ∈ before.current.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context before.current.context)
    (next : Observation before.current.context.state)
    (view : next.view = before.current.context.state.view)
    (certificate : GeneralNominalCycleSteps.Refresh before.current (reobserve before.current.context next))
    (model : Assignment) (valid : Models (refreshed before next).current model)
    (dictionaries : List Payload)
    (given : All₂ (Evidence registry (refreshed before next).current.context model) packet.children dictionaries) :
    Evidence registry (refreshed before next).current.context model
      packet.site.occurrence (.node packet.declaration.id dictionaries) :=
  evidence_node _ _ _ _ _ _ _
    (recorded_instance before formed packet member growth next view certificate model valid) given

/-- This is the existing administrative rule, with its real Known-progress
premises; semantic transport alone is not passed off as a transition. -/
theorem actual_step (before : Tracked roles) (focus : Occurrence roles)
    (generated : Generated before.current root focus)
    (next : Observation before.current.context.state)
    (certificate : GeneralNominalCycleSteps.Refresh before.current (reobserve before.current.context next))
    (identity : Nat) (member : identity ∈ GeneralNominalState.sources before.current.context.state)
    (unknown : ¬ GeneralNominalState.Known before.current.context.state identity)
    (known : GeneralNominalState.Known (reobserve before.current.context next).state identity) :
    GeneralNominalActualInspectionSteps.Step registry root before (refreshed before next) :=
  ⟨focus,generated,.administrative focus _ (.refresh focus _ certificate identity member unknown known)⟩

theorem ordinary_then_refresh_actual (context : GeneralNominalCandidates.Context)
    (before : Tracked roles)
    (path : B4Target.Steps (OrdinaryStep registry root) (initial context root) before)
    (focus : Occurrence roles) (generated : Generated before.current root focus)
    (next : Observation before.current.context.state)
    (certificate : GeneralNominalCycleSteps.Refresh before.current (reobserve before.current.context next))
    (identity : Nat) (member : identity ∈ GeneralNominalState.sources before.current.context.state)
    (unknown : ¬ GeneralNominalState.Known before.current.context.state identity)
    (known : GeneralNominalState.Known (reobserve before.current.context next).state identity) :
    B4Target.Steps (GeneralNominalActualInspectionSteps.Step registry root)
      (initial context root) (refreshed before next) :=
  .tail (ordinary_steps_actual path) (actual_step before focus generated next certificate identity member unknown known)

/-- Ordinary initial history discharges packet-to-current Extension at the
pre-refresh endpoint. The conclusion lives at the post-refresh context. -/
theorem ordinary_then_refresh_instance (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (before : Tracked roles)
    (path : B4Target.Steps (OrdinaryStep registry root) (initial context root) before)
    (packet : Packet roles) (member : packet ∈ before.current.packets)
    (next : Observation before.current.context.state)
    (view : next.view = before.current.context.state.view)
    (certificate : GeneralNominalCycleSteps.Refresh before.current (reobserve before.current.context next))
    (model : Assignment) (valid : Models (refreshed before next).current model) :
    Instance registry (refreshed before next).current.context model
      packet.site.occurrence packet.declaration.id packet.children :=
  recorded_instance before (ordinary_initial_formed context source path) packet member
    (ordinary_initial_extensions context path packet member) next view certificate model valid

theorem ordinary_then_refresh_evidence (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (before : Tracked roles)
    (path : B4Target.Steps (OrdinaryStep registry root) (initial context root) before)
    (packet : Packet roles) (member : packet ∈ before.current.packets)
    (next : Observation before.current.context.state)
    (view : next.view = before.current.context.state.view)
    (certificate : GeneralNominalCycleSteps.Refresh before.current (reobserve before.current.context next))
    (model : Assignment) (valid : Models (refreshed before next).current model)
    (dictionaries : List Payload)
    (given : All₂ (Evidence registry (refreshed before next).current.context model) packet.children dictionaries) :
    Evidence registry (refreshed before next).current.context model
      packet.site.occurrence (.node packet.declaration.id dictionaries) :=
  recorded_evidence before (ordinary_initial_formed context source path) packet member
    (ordinary_initial_extensions context path packet member) next view certificate model valid dictionaries given

/-- Operational and semantic conclusions together for one genuine improving
refresh after the ordinary initial trace. Child evidence is still an explicit
premise at the final context, so no recursive completion is claimed. -/
theorem ordinary_then_refresh_result (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (before : Tracked roles)
    (path : B4Target.Steps (OrdinaryStep registry root) (initial context root) before)
    (packet : Packet roles) (recorded : packet ∈ before.current.packets)
    (focus : Occurrence roles) (generated : Generated before.current root focus)
    (next : Observation before.current.context.state)
    (view : next.view = before.current.context.state.view)
    (certificate : GeneralNominalCycleSteps.Refresh before.current (reobserve before.current.context next))
    (identity : Nat) (member : identity ∈ GeneralNominalState.sources before.current.context.state)
    (unknown : ¬ GeneralNominalState.Known before.current.context.state identity)
    (known : GeneralNominalState.Known (reobserve before.current.context next).state identity)
    (model : Assignment) (valid : Models (refreshed before next).current model)
    (dictionaries : List Payload)
    (given : All₂ (Evidence registry (refreshed before next).current.context model) packet.children dictionaries) :
    B4Target.Steps (GeneralNominalActualInspectionSteps.Step registry root)
      (initial context root) (refreshed before next) ∧
    Evidence registry (refreshed before next).current.context model
      packet.site.occurrence (.node packet.declaration.id dictionaries) :=
  ⟨ordinary_then_refresh_actual context before path focus generated next certificate identity member unknown known,
    ordinary_then_refresh_evidence context source before path packet recorded next view certificate model valid dictionaries given⟩

end Yulang.GeneralDictionaryAgreedRefresh174
