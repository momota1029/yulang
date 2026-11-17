import Yulang.GeneralDictionaryEffectProvenance227
import Yulang.GeneralNominalCenteredHeadMatHeadShape

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryPointCaptureSupport227
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionarySemanticTrace227 GeneralDictionaryFootprintCenters227
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection
open GeneralNominalQueryProvenance183 (headInspection)
open GeneralNominalCenteredModelExtension
variable {roles : Roles.RoleDecls}

/-- A point capture cannot be an unprotected mutable coordinate: its observed
origin is fixed by registered positional input roots and the current tests. -/
theorem point_capture_mem
    (trace : Footprint registry context root state pool)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model)
    (captured : Capture plan.packet.context.state)
    (member : captured ∈ (headInspection plan).captures)
    (located : captured.origin = some origin)
    (lower : plan.packet.context.state.base.source captured.bounds.1 = identity)
    (upper : plan.packet.context.state.base.source captured.bounds.2 = identity)
    (nonzero : identity ≠ 0) : identity ∈ pool := by
  classical
  by_cases absent : identity ∈ pool
  · exact absent
  apply False.elim
  let changed (value : CommonNominalFullCarrier.Ty) : Assignment :=
    fun n => if n = identity then (value,(model n).2) else model n
  have preserved value : Models state (changed value) :=
    (trace.depends model (changed value) (by
      intro n present
      have different : n ≠ identity := by intro equal; exact absent (equal ▸ present)
      simp [changed,different])).mp valid
  have sameRoots value n (present : n ∈ List.ofFn plan.input.center ++ [0]) :
      model n = changed value n := by
    have different : n ≠ identity := by
      intro equal
      rcases List.mem_append.mp present with center | zero
      · exact absent (equal ▸ frame_input_centers trace frame center)
      · exact nonzero (equal.symm.trans (List.mem_singleton.mp zero))
    simp [changed,different]
  have tests value : ∀ test ∈ plan.headSchema.tests,
      GeneralNominalOriginTerms.Head (changed value) test.1 test.2 := by
    intro test used
    exact (GeneralNominalCenteredFrame179.head_iff _ _
      (sameRoots value _ ((GeneralDictionaryDefault214ActualSupport.head_roots plan).1 test used))).mp (schema.1 test used)
  have anchors value : ∀ anchor ∈ (headInspection plan).anchors,
      (∃ actual, Observes (changed value) anchor.1 actual) ∧
      ∀ actual, Observes (changed value) anchor.1 actual → Fits plan.packet.context.state (changed value) anchor.2 actual := by
    apply GeneralDictionaryRecursiveBounds215.many_bounds
    · rw [frame.context_eq]; exact (preserved value).1
    · intro index
      simpa only [Nat.zero_add] using GeneralDictionaryCurrentRoots215.root_bounds plan frame (changed value) (preserved value) index
    · exact tests value
  have anchored := GeneralNominalCaptureAnchors.many_anchored plan.packet.context.state
    _ plan.packet.bounds _ 0 captured member origin located
  obtain ⟨other,atOther,used⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    plan.packet.context.state _ plan.packet.bounds _ 0 captured member
  have eqOrigin : other = origin := Option.some.inj (atOther.symm.trans located)
  subst other
  have originRoot := (GeneralDictionaryDefault214ActualSupport.head_roots plan).2 _ used
  obtain ⟨actual,observed⟩ := (anchors .bottom _ anchored).1
  have equalRoots : changed .bottom (originSource origin) = changed (.base .int) (originSource origin) :=
    (sameRoots .bottom _ originRoot).symm.trans (sameRoots (.base .int) _ originRoot)
  have observedInt := (GeneralNominalCenteredFrame179.observes_iff origin equalRoots actual).mp observed
  have bottomFit := (anchors .bottom _ anchored).2 actual observed
  have intFit := (anchors (.base .int) _ anchored).2 actual observedInt
  simp only [Fits,GeneralNominalCaptureMerges.Fits,lower,upper,changed,ite_true] at bottomFit intFit
  exact GeneralNominalCenteredHeadMatHeadShape.bottom_no_head (.scalar .int)
    ⟨CommonNominalFullCarrier.subtype_trans bottomFit.1 intFit.2,
      CommonNominalFullCarrier.subtype_trans intFit.1 bottomFit.2⟩

/-- In particular every freshly named point capture, including merge p0/p1,
is already semantically protected. No source or groundness hypothesis is used. -/
theorem fresh_point_capture_mem
    (trace : Footprint registry context root state pool)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model)
    (captured : Capture plan.packet.context.state)
    (member : captured ∈ (headInspection plan).captures)
    (located : captured.origin = some origin)
    (lower : plan.packet.context.state.base.source captured.bounds.1 =
      fresh seed invocation declaration purpose owner position)
    (upper : plan.packet.context.state.base.source captured.bounds.2 =
      fresh seed invocation declaration purpose owner position) :
    fresh seed invocation declaration purpose owner position ∈ pool :=
  point_capture_mem trace plan frame model valid schema captured member located lower upper
    GeneralDictionaryBodyProvenance227.fresh_ne_zero

/-- An unprotected nonzero endpoint can be assigned any carrier value while
retaining the journal and all observations of the captured origin. -/
theorem absent_capture_fits
    (trace : Footprint registry context root state pool)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model)
    (captured : Capture plan.packet.context.state)
    (member : captured ∈ (headInspection plan).captures)
    (located : captured.origin = some origin)
    (nonzero : identity ≠ 0) (absent : identity ∉ pool)
    (actual : CommonNominalFullCarrier.Ty) (observed : Observes model origin actual)
    (value : CommonNominalFullCarrier.Ty) :
    Fits plan.packet.context.state
      (fun n => if n = identity then (value,(model n).2) else model n)
      captured.bounds actual := by
  classical
  let changed (value : CommonNominalFullCarrier.Ty) : Assignment :=
    fun n => if n = identity then (value,(model n).2) else model n
  have preserved value : Models state (changed value) :=
    (trace.depends model (changed value) (by
      intro n present
      have different : n ≠ identity := by intro equal; exact absent (equal ▸ present)
      simp [changed,different])).mp valid
  have sameRoots value n (present : n ∈ List.ofFn plan.input.center ++ [0]) :
      model n = changed value n := by
    have different : n ≠ identity := by
      intro equal
      rcases List.mem_append.mp present with center | zero
      · exact absent (equal ▸ frame_input_centers trace frame center)
      · exact nonzero (equal.symm.trans (List.mem_singleton.mp zero))
    simp [changed,different]
  have tests value : ∀ test ∈ plan.headSchema.tests,
      GeneralNominalOriginTerms.Head (changed value) test.1 test.2 := by
    intro test used
    exact (GeneralNominalCenteredFrame179.head_iff _ _
      (sameRoots value _ ((GeneralDictionaryDefault214ActualSupport.head_roots plan).1 test used))).mp (schema.1 test used)
  have anchors value : ∀ anchor ∈ (headInspection plan).anchors,
      (∃ actual, Observes (changed value) anchor.1 actual) ∧
      ∀ actual, Observes (changed value) anchor.1 actual → Fits plan.packet.context.state (changed value) anchor.2 actual := by
    apply GeneralDictionaryRecursiveBounds215.many_bounds
    · rw [frame.context_eq]; exact (preserved value).1
    · intro index
      simpa only [Nat.zero_add] using GeneralDictionaryCurrentRoots215.root_bounds plan frame (changed value) (preserved value) index
    · exact tests value
  have anchored := GeneralNominalCaptureAnchors.many_anchored plan.packet.context.state
    _ plan.packet.bounds _ 0 captured member origin located
  obtain ⟨other,atOther,used⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    plan.packet.context.state _ plan.packet.bounds _ 0 captured member
  have eqOrigin : other = origin := Option.some.inj (atOther.symm.trans located)
  subst other
  have originRoot := (GeneralDictionaryDefault214ActualSupport.head_roots plan).2 _ used
  exact (anchors value _ anchored).2 actual
    ((GeneralNominalCenteredFrame179.observes_iff origin (sameRoots value _ originRoot) actual).mp observed)

/-- An absent lower endpoint is possible only at a semantically top origin. -/
theorem absent_lower_top
    (trace : Footprint registry context root state pool)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model)
    (captured : Capture plan.packet.context.state)
    (member : captured ∈ (headInspection plan).captures)
    (located : captured.origin = some origin)
    (nonzero : plan.packet.context.state.base.source captured.bounds.1 ≠ 0)
    (absent : plan.packet.context.state.base.source captured.bounds.1 ∉ pool)
    (observed : Observes model origin actual) :
    CommonNominalFullCarrier.Subtype .top actual := by
  have fit := absent_capture_fits trace plan frame model valid schema captured member located nonzero absent actual observed .top
  simpa only [Fits,GeneralNominalCaptureMerges.Fits,ite_true] using fit.1

/-- Dually an absent upper endpoint forces a semantically bottom origin. -/
theorem absent_upper_bottom
    (trace : Footprint registry context root state pool)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model)
    (captured : Capture plan.packet.context.state)
    (member : captured ∈ (headInspection plan).captures)
    (located : captured.origin = some origin)
    (nonzero : plan.packet.context.state.base.source captured.bounds.2 ≠ 0)
    (absent : plan.packet.context.state.base.source captured.bounds.2 ∉ pool)
    (observed : Observes model origin actual) :
    CommonNominalFullCarrier.Subtype actual .bottom := by
  have fit := absent_capture_fits trace plan frame model valid schema captured member located nonzero absent actual observed .bottom
  simpa only [Fits,GeneralNominalCaptureMerges.Fits,ite_true] using fit.2

/-- A non-extremal observed value forces its nonzero lower endpoint into the
existing footprint; the result does not assert this for a top-valued origin. -/
theorem lower_mem_of_not_top
    (trace : Footprint registry context root state pool)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model)
    (captured : Capture plan.packet.context.state)
    (member : captured ∈ (headInspection plan).captures)
    (located : captured.origin = some origin)
    (nonzero : plan.packet.context.state.base.source captured.bounds.1 ≠ 0)
    (observed : Observes model origin actual)
    (notTop : ¬ CommonNominalFullCarrier.Subtype .top actual) :
    plan.packet.context.state.base.source captured.bounds.1 ∈ pool := by
  classical
  by_cases present : plan.packet.context.state.base.source captured.bounds.1 ∈ pool
  · exact present
  · exact False.elim (notTop (absent_lower_top trace plan frame model valid schema captured member located nonzero present observed))

theorem upper_mem_of_not_bottom
    (trace : Footprint registry context root state pool)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model)
    (captured : Capture plan.packet.context.state)
    (member : captured ∈ (headInspection plan).captures)
    (located : captured.origin = some origin)
    (nonzero : plan.packet.context.state.base.source captured.bounds.2 ≠ 0)
    (observed : Observes model origin actual)
    (notBottom : ¬ CommonNominalFullCarrier.Subtype actual .bottom) :
    plan.packet.context.state.base.source captured.bounds.2 ∈ pool := by
  classical
  by_cases present : plan.packet.context.state.base.source captured.bounds.2 ∈ pool
  · exact present
  · exact False.elim (notBottom (absent_upper_bottom trace plan frame model valid schema captured member located nonzero present observed))

end Yulang.GeneralDictionaryPointCaptureSupport227
