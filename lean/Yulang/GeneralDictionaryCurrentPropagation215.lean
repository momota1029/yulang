import Yulang.GeneralDictionaryDefaultProjectionBounds215
import Yulang.GeneralDictionaryDefaultAliasProjection215
import Yulang.GeneralDictionaryCheckedAnchors215
import Yulang.GeneralDictionaryCheckedOrigins215

/-! Actual alias readback discharges current raw capture cross-constraints and
self-checks in the journal model. Merge-slot equations remain explicit. -/
namespace Yulang.GeneralDictionaryCurrentPropagation215
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalQueryProvenance183 (headInspection)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

theorem capture_compatible (candidate : Plan roles) (model : Assignment)
    (projection : ProjectionModels candidate.packet.context.state (headInspection candidate) model) :
    GeneralNominalAllocation.Compatible candidate.packet.bindings model := by
  rw [← GeneralDictionaryDefaultProjectionBounds215.head_bindings candidate]
  intro first one last two same
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp one
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp two
  obtain ⟨origin,located,_⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    candidate.packet.context.state _ candidate.packet.bounds _ 0 a ha
  have anchored := GeneralNominalCaptureAnchors.many_anchored
    candidate.packet.context.state _ candidate.packet.bounds _ 0 a ha origin located
  obtain ⟨value,observed⟩ := (projection.1 _ anchored).1
  exact subtype_trans ((projection.1 _ anchored).2 value observed).1
    (projection.2.2.1 a ha b hb same origin located value observed).2

theorem centered_checks (candidate : Plan roles) (model : Assignment)
    (projection : ProjectionModels candidate.packet.context.state (headInspection candidate) model) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (selfChecks candidate.packet.context.state (headInspection candidate)) := by
  intro atom member
  obtain ⟨bounds,present,rfl⟩ := List.mem_map.mp member
  obtain ⟨origin,anchored⟩ := GeneralDictionaryCheckedAnchors215.many_anchored
    candidate.packet.context.state _ candidate.packet.bounds _ 0 bounds present
  obtain ⟨value,observed⟩ := (projection.1 _ anchored).1
  exact subtype_trans ((projection.1 _ anchored).2 value observed).1
    ((projection.1 _ anchored).2 value observed).2

theorem raw_checks (candidate : Plan roles)
    (inputRegistered : candidate.input ∈ state.core.sites)
    (located : GeneralNominalRecursiveCandidates.arguments candidate.packet.context
      (GeneralNominalCenteredHeadCandidates.inputs candidate.input.occurrence) = some candidate.packet.bounds)
    (model : Assignment) (valid : Models state model)
    (projection : ProjectionModels candidate.packet.context.state (headInspection candidate) model) :
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (selfChecks candidate.packet.context.state
        (GeneralNominalRecursiveCandidates.report candidate.packet.context candidate.packet.declaration candidate.packet.bounds)) := by
  intro atom member
  obtain ⟨bounds,present,rfl⟩ := List.mem_map.mp member
  change bounds ∈ candidate.packet.bounds ++ _ at present
  rcases List.mem_append.mp present with root | checked
  · obtain ⟨index,bounded,found⟩ := List.mem_iff_getElem.mp root
    have fit := GeneralDictionaryDefaultAliasProjection215.root_bounds candidate inputRegistered located model valid ⟨index,bounded⟩
    obtain ⟨value,observed⟩ := fit.1
    have fits := fit.2 value observed
    simp only [Fin.getElem_fin,found] at fits
    exact subtype_trans fits.1 fits.2
  · have equal := GeneralDictionaryCheckedOrigins215.many_shape candidate.packet.context.state
      (GeneralNominalInspection.queries candidate.packet.context.state candidate.packet.context.interpretation candidate.packet.declaration)
      candidate.packet.bounds (fun _ => none)
      (fun index => some (.source ((List.ofFn candidate.input.center)[index]?.getD 0))) 0 0
    rw [GeneralDictionaryCheckedOrigins215.shape] at equal
    rw [equal] at checked
    exact centered_checks candidate model projection _ (List.mem_map.mpr ⟨bounds,checked,rfl⟩)

end Yulang.GeneralDictionaryCurrentPropagation215
