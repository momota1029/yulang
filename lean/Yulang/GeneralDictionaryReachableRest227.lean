import Yulang.GeneralDictionaryReachablePacket226

/-! In any current frame, total head schema plus raw merges imply
all capture Fits obligations. The current journal already supplies input Holds.
Neither component needs a separate finite-support protection list. -/
namespace Yulang.GeneralDictionaryReachableRest227
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection
open GeneralNominalQueryProvenance183 (headInspection)
open GeneralNominalCenteredHeadMatPlans (emittedSchema childSchema)
open GeneralNominalCenteredFrame179 (Agree siteSources site_iff)
open GeneralDictionaryDefaultTotalFrame212 (resolve)
open GeneralDictionaryDefaultModeSupport213 (schemaSources)
open GeneralDictionaryDefaultModeEffects213 (plan_schema_iff)
open GeneralDictionaryReachablePacket226 (mergeSources)
variable {roles : Roles.RoleDecls} {state : State roles}
set_option backward.isDefEq.respectTransparency false

/-- The head schema provides its own tests and shared-origin equalities.
No reachability or initial-groundness argument is needed once it holds. -/
theorem centered_projection (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model) :
    ProjectionModels plan.packet.context.state (headInspection plan) model := by
  have agreement := GeneralDictionaryHeadSharing220.agreement_of_holds plan model
    (GeneralDictionaryHeadSharing220.schema_holds plan model schema)
  have anchors : ∀ anchor ∈ (headInspection plan).anchors,
      (∃ value, Observes model anchor.1 value) ∧
      ∀ value, Observes model anchor.1 value → Fits plan.packet.context.state model anchor.2 value := by
    apply GeneralDictionaryRecursiveBounds215.many_bounds
    · rw [frame.context_eq]; exact valid.1
    · intro index
      simpa only [Nat.zero_add] using GeneralDictionaryCurrentRoots215.root_bounds plan frame model valid index
    · exact schema.1
  have anchored (captured : Capture plan.packet.context.state)
      (member : captured ∈ (headInspection plan).captures) (origin : Origin)
      (located : captured.origin = some origin) :=
    GeneralNominalCaptureAnchors.many_anchored plan.packet.context.state _ plan.packet.bounds _ 0 captured member origin located
  refine ⟨anchors,?_,?_,?_⟩
  · intro test member value seen
    have used := GeneralDictionaryInspectionSchema215.many_tests plan.packet.context.state _ plan.packet.bounds _ 0 test member
    exact (schema.1 test used).2 value seen
  · intro a one b two names origin located value seen
    obtain ⟨other,atOther,_⟩ := GeneralNominalCenteredCaptureSchema.many_capture
      plan.packet.context.state _ plan.packet.bounds _ 0 b two
    have same := agreement a one b two names origin other located atOther
    obtain ⟨actual,observed⟩ := same.2.1
    have fit := (anchors _ (anchored b two other atOther)).2 actual observed
    have equal := same.2.2 value actual seen observed
    exact ⟨CommonNominalFullCarrier.subtype_trans fit.1 equal.2,
      CommonNominalFullCarrier.subtype_trans equal.1 fit.2⟩
  · intro a one b two names first last atFirst atLast x y seenX seenY
    exact (agreement a one b two names first last atFirst atLast).2.2 x y seenX seenY

/-- With a head schema in hand, raw projection follows in every current frame. -/
theorem raw_projection (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model) :
    ProjectionModels plan.packet.context.state
      (GeneralNominalRecursiveCandidates.report plan.packet.context plan.packet.declaration plan.packet.bounds) model := by
  have centered := centered_projection plan frame model valid schema
  have rawValid : GeneralNominalState.Models plan.packet.context.state model := by
    rw [frame.context_eq]; exact valid.1
  change ProjectionModels plan.packet.context.state
    (inspectMany plan.packet.context.state (GeneralNominalInspection.queries plan.packet.context.state
      plan.packet.context.interpretation plan.packet.declaration) plan.packet.bounds (fun _ => none) 0) model
  apply GeneralDictionaryWeakReport215.projection plan.packet.context.state _ (headInspection plan) _ centered
  apply GeneralDictionaryRawProjection215.many_related plan.packet.context.state model rawValid _ plan.packet.bounds
    (fun i => .source ((List.ofFn plan.input.center)[i]?.getD 0)) 0
  · intro index
    simpa only [Nat.zero_add] using GeneralDictionaryCurrentRoots215.root_bounds plan frame model valid index
  · exact schema.1

/-- The only remaining raw-head constraints are the allocated merge equations. -/
theorem head_iff_merges (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model) :
    GeneralNominalCenteredHeadCandidates.HeadModels plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.bounds model ↔
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges plan.packet.context.state plan.packet.registry
        plan.packet.site.occurrence.identity plan.packet.declaration plan.packet.bindings) := by
  constructor
  · exact GeneralDictionaryCurrentBranch215.branch_merges plan model
  · intro merges
    have centered := centered_projection plan frame model valid schema
    refine ⟨?_,raw_projection plan frame model valid schema⟩
    unfold GeneralNominalRecursiveCandidates.privateState
    apply (GeneralNominalState.extend_models ..).mpr
    refine ⟨?_,?_⟩
    · apply (GeneralNominalAllocation.propagate_models ..).mpr
      refine ⟨?_,GeneralDictionaryCurrentPropagation215.capture_compatible plan model centered,merges⟩
      rw [frame.context_eq]; exact valid.1
    · have located := frame.located
      rw [← frame.occurrence_eq,← plan.input_exact] at located
      exact GeneralDictionaryCurrentPropagation215.raw_checks plan frame.center_recorded located model valid centered

/-- Capture Fits is a derived fact at any current frame, not a packet premise. -/
theorem capture_fits
    (plan : Plan roles) (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model)
    (merges : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges plan.packet.context.state plan.packet.registry
        plan.packet.site.occurrence.identity plan.packet.declaration plan.packet.bindings))
    (name : Nat)
    (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) :
    GeneralNominalCaptureMerges.Fits model ((GeneralNominalPacketSupport.capture plan.packet).inputs name)
      (model (plan.binder name)).1 := by
  have declared : name ∈ plan.packet.declaration.inputNames := by
    rcases needed with input | ⟨clause,member,used⟩
    · exact input
    · exact plan.packet.checked.scope.1 clause member name used
  have projection := centered_projection plan frame model valid schema
  obtain ⟨captured,present,equal⟩ := GeneralNominalCompleteNames183.declaration_input_capture
    plan.packet.context.state plan.packet.context.interpretation plan.packet.declaration
    plan.packet.bounds _ 0 (GeneralDictionaryDefaultRevisit214.frame_finished frame) name declared
  obtain ⟨origin,located,used⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    plan.packet.context.state _ plan.packet.bounds _ 0 captured present
  have same : GeneralNominalOriginTerms.Same model origin (.source (plan.binder captured.name)) := by
    exact schema.2 ⟨captured.name,origin,.actual⟩ used
  obtain ⟨value,seen⟩ := same.1
  have recorded := merges
  rw [← GeneralDictionaryDefaultProjectionBounds215.head_bindings plan] at recorded
  have fits := GeneralNominalCaptureBounds187.projected_merged plan.packet.context.state
    (headInspection plan) plan.packet.registry plan.packet.site.occurrence.identity plan.packet.declaration
    model projection recorded captured present (equal ▸ declared) origin located value seen
  have equivalent := same.2.2 value (model (plan.binder captured.name)).1 seen (.source _)
  have result := (GeneralNominalCaptureBounds187.fits_equivalent model _ _ _ equivalent).mp fits
  simpa only [GeneralDictionaryDefaultProjectionBounds215.head_bindings,equal] using result

/-- Packet tail after removing the two semantically redundant obligations. -/
def Rest (plan : Plan roles) (model : Assignment) : Prop :=
  plan.SchemaHolds plan.headSchema model ∧
  (emittedSchema plan).Holds (GeneralNominalCenteredHeadMatEffects.variables plan model) model ∧
  ∀ clause ∈ plan.packet.declaration.requirements, ∀ valid,
    (plan.childSite clause valid).Holds model ∧
    (childSchema plan clause valid).Holds (GeneralNominalCenteredHeadMatEffects.variables plan model) model

def restSources (plan : Plan roles) : List Nat :=
  GeneralNominalModeFrame181.schemaSources plan plan.headSchema ++
    schemaSources (resolve plan) (emittedSchema plan) ++ GeneralDictionaryDefaultPacketSupport213.childSources plan

theorem rest_iff (plan : Plan roles) (same : Agree (restSources plan) first last) :
    Rest plan first ↔ Rest plan last := by
  unfold Rest
  apply and_congr (GeneralNominalModeFrame181.schema_iff plan plan.headSchema
    (fun name member => same name (by simp [restSources,member])))
  apply and_congr (plan_schema_iff plan (emittedSchema plan)
    (fun name member => same name (by simp [restSources,member])))
  apply forall_congr'; intro clause
  apply forall_congr'; intro member
  apply forall_congr'; intro valid
  have support : Agree (siteSources (plan.childSite clause valid) ++
      schemaSources (resolve plan) (childSchema plan clause valid)) first last := by
    intro name present
    apply same
    have contained : name ∈ GeneralDictionaryDefaultPacketSupport213.childSources plan :=
      List.mem_flatMap.mpr ⟨⟨clause,member⟩,by simp,present⟩
    simp [restSources,contained]
  exact and_congr (site_iff _ (fun name member => support name (List.mem_append_left _ member)))
    (plan_schema_iff _ _ (fun name member => support name (List.mem_append_right _ member)))

/-- Exact characterization on a journal model. No packet satisfiability,
Agreement, Fits, or input-model premise is added. -/
theorem packet_characterization
    (plan : Plan roles) (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model) :
    GeneralNominalCenteredHeadMatStepPackets.Holds plan model ↔
      PresenceNormalForm.All CommonNominalFullCarrier.model model
        (GeneralNominalAllocation.merges plan.packet.context.state plan.packet.registry
          plan.packet.site.occurrence.identity plan.packet.declaration plan.packet.bindings) ∧ Rest plan model := by
  rw [← GeneralNominalCenteredHeadMatStepPackets.models_iff]
  constructor
  · rintro ⟨head,_,_,schema,emitted,children⟩
    exact ⟨GeneralDictionaryCurrentBranch215.branch_merges plan model head,schema,emitted,children⟩
  · rintro ⟨merges,schema,emitted,children⟩
    refine ⟨(head_iff_merges plan frame model valid schema).mpr merges,valid.2.2.2.1 plan.input frame.center_recorded,?_,schema,emitted,children⟩
    exact capture_fits plan frame model valid schema merges

def packetSources (plan : Plan roles) : List Nat := mergeSources plan ++ restSources plan

theorem packet_iff
    (plan : Plan roles) (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (one : Models state first) (two : Models state last)
    (same : Agree (packetSources plan) first last) :
    GeneralNominalCenteredHeadMatStepPackets.Holds plan first ↔
      GeneralNominalCenteredHeadMatStepPackets.Holds plan last := by
  rw [packet_characterization plan frame first one,
    packet_characterization plan frame last two]
  apply and_congr
  · unfold PresenceNormalForm.All
    apply forall_congr'; intro atom
    apply forall_congr'; intro member
    apply GeneralNominalCenteredModelExtension.atom_same
    intro name present
    exact same name (List.mem_append_left _ (List.mem_flatMap.mpr ⟨atom,member,present⟩))
  · exact rest_iff plan (fun name member => same name (List.mem_append_right _ member))

end Yulang.GeneralDictionaryReachableRest227
