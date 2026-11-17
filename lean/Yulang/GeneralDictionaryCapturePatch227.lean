import Yulang.GeneralDictionaryPointCaptureSupport227

namespace Yulang.GeneralDictionaryCapturePatch227
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionarySemanticTrace227 GeneralDictionaryFootprintCenters227
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection
open GeneralNominalQueryProvenance183 (headInspection)
variable {roles : Roles.RoleDecls}

/-- All unprotected coordinates may change together. Preserving the zero
sentinel and the semantic footprint preserves Fits at every current capture;
the changed assignment need not separately satisfy the head schema. -/
theorem capture_fits
    (trace : Footprint registry context root state pool)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (first last : Assignment) (valid : Models state first)
    (schema : plan.SchemaHolds plan.headSchema first)
    (same : GeneralNominalCenteredFrame179.Agree (pool ++ [0]) first last)
    (captured : Capture plan.packet.context.state)
    (member : captured ∈ (headInspection plan).captures)
    (located : captured.origin = some origin)
    (observed : Observes first origin actual) :
    Models state last ∧ Fits plan.packet.context.state last captured.bounds actual := by
  have retained : Models state last :=
    (trace.depends first last (fun n h => same n (List.mem_append_left _ h))).mp valid
  have roots n (h : n ∈ List.ofFn plan.input.center ++ [0]) : first n = last n := by
    apply same
    rcases List.mem_append.mp h with center | zero
    · exact List.mem_append_left _ (frame_input_centers trace frame center)
    · exact List.mem_append_right _ zero
  have tests : ∀ test ∈ plan.headSchema.tests,
      GeneralNominalOriginTerms.Head last test.1 test.2 := by
    intro test used
    exact (GeneralNominalCenteredFrame179.head_iff _ _
      (roots _ ((GeneralDictionaryDefault214ActualSupport.head_roots plan).1 test used))).mp
      (schema.1 test used)
  have anchors : ∀ anchor ∈ (headInspection plan).anchors,
      (∃ value, Observes last anchor.1 value) ∧
      ∀ value, Observes last anchor.1 value → Fits plan.packet.context.state last anchor.2 value := by
    apply GeneralDictionaryRecursiveBounds215.many_bounds
    · rw [frame.context_eq]; exact retained.1
    · intro index
      simpa only [Nat.zero_add] using GeneralDictionaryCurrentRoots215.root_bounds plan frame last retained index
    · exact tests
  have anchored := GeneralNominalCaptureAnchors.many_anchored plan.packet.context.state
    _ plan.packet.bounds _ 0 captured member origin located
  obtain ⟨other,atOther,used⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    plan.packet.context.state _ plan.packet.bounds _ 0 captured member
  have eqOrigin : other = origin := Option.some.inj (atOther.symm.trans located)
  subst other
  exact ⟨retained,(anchors _ anchored).2 actual
    ((GeneralNominalCenteredFrame179.observes_iff origin
      (roots _ ((GeneralDictionaryDefault214ActualSupport.head_roots plan).2 _ used)) actual).mp observed)⟩
/-- Finite simultaneous patch specialization, retaining all journal effects
and the concrete captured bounds. -/
theorem finite_capture_fits
    (trace : Footprint registry context root state pool)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model)
    (names : Fin count → Nat) (values : Fin count → CommonNominalFullCarrier.Ty)
    (outside : ∀ index, names index ∉ pool ++ [0])
    (captured : Capture plan.packet.context.state)
    (member : captured ∈ (headInspection plan).captures)
    (located : captured.origin = some origin)
    (observed : Observes model origin actual) :
    Models state (GeneralNominalCenteredModelExtension.assign model names values) ∧
    Fits plan.packet.context.state (GeneralNominalCenteredModelExtension.assign model names values)
      captured.bounds actual :=
  capture_fits trace plan frame model _ valid schema
    (GeneralNominalCenteredFrame179.assign_agree names values (pool ++ [0]) outside)
    captured member located observed

end Yulang.GeneralDictionaryCapturePatch227
