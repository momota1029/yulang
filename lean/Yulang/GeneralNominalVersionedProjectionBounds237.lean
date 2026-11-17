import Yulang.GeneralNominalVersionedCapture231
import Yulang.GeneralNominalVersionedPlans231
import Yulang.GeneralDictionaryDefaultProjectionBounds215
import Yulang.GeneralNominalCenteredHeadMatSemanticLabels
set_option backward.isDefEq.respectTransparency false
/-! Projection bounds for actual centered observations using versioned aggregate
merges. Inherited packet projections are not identified with head projections. -/
namespace Yulang.GeneralNominalVersionedProjectionBounds237
open GeneralDeclarations GeneralNominalCenters GeneralNominalRecursiveInspection
open GeneralNominalAllocation (occurrences)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalQueryProvenance183 (headInspection)
open CommonNominalFullCarrier

theorem merged_iff_raw (state : GeneralNominalState.State) (report : Report state)
    (registry : Registry) (invocation : Nat) (declaration : Declaration) (model : Assignment)
    (recorded : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalVersionedAllocation231.merges state registry invocation declaration (bindings state report)))
    (name : Nat) (declared : name ∈ declaration.inputNames)
    (nonempty : occurrences (bindings state report) name ≠ []) (value : Ty) :
    GeneralNominalCaptureMerges.Fits model
      ((GeneralNominalVersionedAllocation231.capture state registry invocation declaration.id (bindings state report)).inputs name) value ↔
    ∀ captured ∈ report.captures, captured.name = name → Fits state model captured.bounds value := by
  rw [GeneralNominalVersionedCapture231.capture_interval_exact state registry invocation declaration
    (bindings state report) model recorded name declared nonempty value]
  constructor
  · intro all captured present same
    exact all _ ((GeneralNominalCaptureBounds187.occurrence_iff ..).mpr ⟨captured,present,same,rfl⟩)
  · intro all pair present
    obtain ⟨captured,member,same,rfl⟩ := (GeneralNominalCaptureBounds187.occurrence_iff ..).mp present
    exact all captured member same

theorem projected_merged (state : GeneralNominalState.State) (report : Report state)
    (registry : Registry) (invocation : Nat) (declaration : Declaration)
    (model : Assignment) (projection : ProjectionModels state report model)
    (recorded : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalVersionedAllocation231.merges state registry invocation declaration (bindings state report)))
    (captured : Capture state) (present : captured ∈ report.captures)
    (declared : captured.name ∈ declaration.inputNames)
    (origin : Origin) (source : captured.origin = some origin)
    (value : Ty) (seen : Observes model origin value) :
    GeneralNominalCaptureMerges.Fits model
      ((GeneralNominalVersionedAllocation231.capture state registry invocation declaration.id (bindings state report)).inputs captured.name) value := by
  apply (merged_iff_raw state report registry invocation declaration model recorded captured.name
    declared (GeneralNominalCaptureBounds187.occurrence_nonempty state report captured present) value).mpr
  intro last member same
  exact projected_capture_sound state report model projection captured last present member same.symm origin source value seen

theorem head_use (plan : Plan roles) (model : Assignment)
    (finished : Finished (headInspection plan))
    (projection : ProjectionModels plan.packet.context.state (headInspection plan) model)
    (merges : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalVersionedAllocation231.merges plan.packet.context.state plan.packet.registry
        plan.packet.site.occurrence.identity plan.packet.declaration plan.packet.bindings))
    (entry : GeneralNominalMaterialization.Use) (member : entry ∈ plan.headSchema.variables)
    (value : Ty) (seen : Observes model entry.origin value) :
    GeneralNominalCaptureMerges.Fits model ((GeneralNominalVersionedFrame231.capture plan.packet).inputs entry.name) value := by
  obtain ⟨captured,present,name,origin⟩ := GeneralNominalSchemaCapture187.schemas_capture
    plan.packet.context.state _ plan.packet.bounds _ 0 finished entry member
  have declared : captured.name ∈ plan.packet.declaration.inputNames :=
    name ▸ GeneralNominalHeadSchemaNames186.head_input plan entry member
  rw [← GeneralDictionaryDefaultProjectionBounds215.head_bindings plan] at merges
  have fitted := projected_merged plan.packet.context.state (headInspection plan) plan.packet.registry
    plan.packet.site.occurrence.identity plan.packet.declaration model projection merges captured present declared entry.origin origin value seen
  simpa only [GeneralDictionaryDefaultProjectionBounds215.head_bindings,name,GeneralNominalVersionedFrame231.capture,GeneralNominalVersionedFrame231.frame] using fitted

theorem capture_fits (plan : Plan roles) (model : Assignment)
    (finished : Finished (headInspection plan))
    (projection : ProjectionModels plan.packet.context.state (headInspection plan) model)
    (merges : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalVersionedAllocation231.merges plan.packet.context.state plan.packet.registry
        plan.packet.site.occurrence.identity plan.packet.declaration plan.packet.bindings))
    (schema : GeneralNominalVersionedPlans231.SchemaHolds plan plan.headSchema model)
    (name : Nat) (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) :
    GeneralNominalCaptureMerges.Fits model ((GeneralNominalVersionedFrame231.capture plan.packet).inputs name)
      (model (GeneralNominalVersionedFrame231.binder plan name)).1 := by
  have named : name ∈ plan.packet.declaration.inputNames :=
    needed.elim id (GeneralNominalCenteredHeadMatSemanticLabels.needed_in_head (plan := plan))
  obtain ⟨origin,present⟩ := GeneralNominalHeadSchemaSemantic186.input_use plan finished name named
  have same : GeneralNominalOriginTerms.Same model origin (.source (GeneralNominalVersionedFrame231.binder plan name)) := by
    simpa only [ite_true] using schema.2 ⟨name,origin,.actual⟩ present
  obtain ⟨value,seen⟩ := same.1
  have fit := head_use plan model finished projection merges ⟨name,origin,.actual⟩ present value seen
  exact (GeneralNominalCaptureBounds187.fits_equivalent model _ value _
    (same.2.2 value _ seen (.source _))).mp fit
end Yulang.GeneralNominalVersionedProjectionBounds237
