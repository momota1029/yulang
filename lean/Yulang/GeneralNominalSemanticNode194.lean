import Yulang.GeneralNominalCommittedEvidence192

/-! Semantic node composition does not require an installation certificate.
A current head frame, actual request readiness and the branch in the very same
model suffice. This factors the missing general bridge without postulating
recursive Evidence or a solver. -/
namespace Yulang.GeneralNominalSemanticNode194
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}
variable {plan : Plan roles} {root : Occurrence roles} {key : Nat}

/-- Per-model semantic bridge: only the branch for the given assignment is used.
No all-raw-model commitment or generated-edge coverage is required. -/
theorem instance_of_frame (frame : Frame registry state.core root key plan)
    (ready : GeneralNominalRecursiveCandidates.RequestReady plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.checked plan.packet.bounds)
    (model : Assignment) (branch : plan.packet.Holds model) :
    GeneralDictionaryRecursiveEvidence.Instance registry state.core.erased.current.context model root key plan.packet.children := by
  have instanceRule : GeneralDictionaryRecursiveEvidence.Instance plan.packet.registry plan.packet.context model
      plan.packet.site.occurrence plan.packet.declaration.id plan.packet.children := by
    refine ⟨plan.packet.declaration,?_,plan.packet.checked,rfl,?_,plan.packet.bounds,?_,?_,ready,rfl,?_,branch⟩
    · simpa only [frame.registry_eq] using frame.visible
    · simpa only [frame.occurrence_eq] using frame.role_eq
    · rw [frame.occurrence_eq]; exact frame.located
    · have prepared := frame.prepared
      rw [← frame.context_eq] at prepared
      obtain ⟨_,_,_,bounds,found,finished,_⟩ := prepared
      have same := Option.some.inj (frame.located.symm.trans found)
      subst bounds
      exact finished
    · simpa only [frame.registry_eq,frame.context_eq] using frame.prepared.1
  simpa only [frame.registry_eq,frame.context_eq,frame.occurrence_eq,frame.key_eq] using instanceRule

/-- Actual request coverage and materialization are separate from semantic
commitment. This does not infer readiness from head selection alone. -/
theorem request_ready (frame : Frame registry state.core root key plan)
    (effects : EffectsReady state.core root plan)
    (materialized : (GeneralNominalRecursiveCandidates.generated plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.checked plan.packet.bounds).unknown = false) :
    GeneralNominalRecursiveCandidates.RequestReady plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.checked plan.packet.bounds := by
  constructor
  · intro output member
    apply effects.1 output
    apply request_retained plan.packet.site frame.raw_recorded
    · rw [frame.occurrence_eq]; exact .refl _
    · exact member
  · exact materialized

/-- Parent and children are interpreted in exactly one supplied state/model.
The frame and request-readiness premises are structural; branch truth is the
explicit semantic gap when no current journal packet is available. -/
theorem evidence_of_frame (frame : Frame registry state.core root key plan)
    (ready : GeneralNominalRecursiveCandidates.RequestReady plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.checked plan.packet.bounds)
    (model : Assignment) (branch : plan.packet.Holds model) (payloads : List Payload)
    (children : All₂ ((boundary roles).Evidence registry state model) plan.packet.children payloads) :
    (boundary roles).Evidence registry state model root (.node key payloads) :=
  GeneralDictionaryRecursiveEvidence.evidence_node registry state.core.erased.current.context model
    root key plan.packet.children payloads (instance_of_frame frame ready model branch) children

/-- A current recorded packet supplies branch truth for every full state model;
no extra packet.Holds or Installable assumption is imposed on the caller. The
current-frame and readiness premises remain explicit and are not globally proved. -/
theorem evidence_of_recorded (frame : Frame registry state.core root key plan)
    (ready : GeneralNominalRecursiveCandidates.RequestReady plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.checked plan.packet.bounds)
    (recorded : plan.packet ∈ state.core.erased.current.packets)
    (model : Assignment) (valid : Models state model) (payloads : List Payload)
    (children : All₂ ((boundary roles).Evidence registry state model) plan.packet.children payloads) :
    (boundary roles).Evidence registry state model root (.node key payloads) :=
  evidence_of_frame frame ready model (valid.1.1.2.1 plan.packet recorded) payloads children

/-- A recorded historical packet can be read in a later ordinary context.
The Frame belongs to its actual earlier snapshot, not an invented current Frame.
Only the later journal supplies the branch; every child uses the same later model.
This supports actual installations without assuming Installable again at readback. -/
theorem trace_evidence_of_recorded {after : State roles} (traceRoot : Occurrence roles)
    (frame : Frame registry state.core root key plan)
    (ready : GeneralNominalRecursiveCandidates.RequestReady plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.checked plan.packet.bounds)
    (path : B4Target.Steps (GeneralNominalOrdinaryEvidence191.OrdinaryStep registry traceRoot) state after)
    (recorded : plan.packet ∈ after.core.erased.current.packets)
    (model : Assignment) (valid : Models after model) (payloads : List Payload)
    (children : All₂ ((boundary roles).Evidence registry after model) plan.packet.children payloads) :
    (boundary roles).Evidence registry after model root (.node key payloads) := by
  have old := instance_of_frame frame ready model (valid.1.1.2.1 plan.packet recorded)
  have current := GeneralDictionaryOrdinaryTrace.instance_extension registry _ _
    (GeneralNominalOrdinaryEvidence191.trace_growth path) model valid.1.1.1 root key plan.packet.children old
  exact GeneralDictionaryRecursiveEvidence.evidence_node registry _ model root key _ payloads current children
end Yulang.GeneralNominalSemanticNode194
