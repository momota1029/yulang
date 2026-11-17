import Yulang.GeneralNominalVersionedEvidence231
import Yulang.GeneralNominalVersionedJournal232
import Yulang.GeneralNominalVersionedHeadSharing232
import Yulang.GeneralDictionaryCountedProjection216
import Yulang.GeneralDictionaryCurrentRoots215
set_option backward.isDefEq.respectTransparency false
/-! Current centered projection is exactly same-name sharing once actual schema
 tests hold. Uses real versioned Frame and full mixed Models, not legacy reachability. -/
namespace Yulang.GeneralNominalVersionedCurrentProjection237
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms
open GeneralNominalQueryProvenance183 (headInspection)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryStructuralProjection215 (Bounded)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}
theorem root_bounds (candidate : Plan roles)
    (frame : GeneralNominalVersionedEvidence231.Frame registry state.core focus key candidate)
    (model : Assignment) (valid : Models state model)
    (index : Fin candidate.packet.bounds.length) :
    Bounded candidate.packet.context.state model candidate.packet.bounds[index]
      (.source ((List.ofFn candidate.input.center)[index.val]?.getD 0)) := by
  have mapped := GeneralNominalPacketCaptureReadback.locate_sources
    candidate.packet.context.state.base (List.ofFn focus.demand.arguments) candidate.packet.bounds frame.located
  have occurrence : candidate.input.occurrence = focus := candidate.input_exact.trans frame.occurrence_eq
  have held := valid.1.2.2.2.1 candidate.input frame.center_recorded
  have length : candidate.packet.bounds.length = (roles focus.demand.role).arity := by
    have lengths := congrArg List.length mapped
    simpa only [List.length_map,List.length_ofFn] using lengths
  have bounded : index.val < (roles focus.demand.role).arity := by omega
  have pair := congrArg (fun xs => xs[index.val]?) mapped
  simp only [List.getElem?_map,List.getElem?_eq_getElem,index.isLt,Option.map_some,
    List.getElem?_ofFn,bounded,↓reduceDIte] at pair
  have pairEq := Option.some.inj pair
  generalize siteEq : candidate.input = site at *
  cases site with
  | mk input centers =>
    simp only at occurrence held ⊢
    subst input
    simp only [List.getElem?_ofFn,bounded,↓reduceDIte,Option.getD_some]
    refine ⟨⟨_,.source _⟩,?_⟩
    intro value seen
    cases seen
    have fit := held ⟨index.val,bounded⟩
    change CommonNominalFullCarrier.Subtype _ _ ∧ CommonNominalFullCarrier.Subtype _ _
    rw [← pairEq] at fit
    exact fit

theorem projection_iff
    (candidate : Plan roles) (frame : GeneralNominalVersionedEvidence231.Frame registry state.core focus key candidate)
    (model : Assignment) (valid : Models state model)
    (tests : ∀ test ∈ candidate.headSchema.tests, Head model test.1 test.2) :
    ProjectionModels candidate.packet.context.state (headInspection candidate) model ↔ GeneralDictionaryCountedProjection216.Agreement candidate model := by
  have anchors : ∀ anchor ∈ (headInspection candidate).anchors,
      (∃ value, Observes model anchor.1 value) ∧
      ∀ value, Observes model anchor.1 value → Fits candidate.packet.context.state model anchor.2 value := by
    apply GeneralDictionaryRecursiveBounds215.many_bounds
    · rw [frame.context_eq]; exact valid.1.1
    · intro index
      simpa only [Nat.zero_add] using root_bounds candidate frame model valid index
    · exact tests
  have anchored (captured : Capture candidate.packet.context.state)
      (member : captured ∈ (headInspection candidate).captures) (origin : Origin) (located : captured.origin = some origin) :=
    GeneralNominalCaptureAnchors.many_anchored candidate.packet.context.state _ candidate.packet.bounds _ 0 captured member origin located
  constructor
  · intro projection a one b two names first last atFirst atLast
    exact ⟨(anchors _ (anchored a one first atFirst)).1,
      (anchors _ (anchored b two last atLast)).1,
      projection.2.2.2 a one b two names first last atFirst atLast⟩
  · intro agreement
    refine ⟨anchors,?_,?_,?_⟩
    · intro test member value seen
      have used := GeneralDictionaryInspectionSchema215.many_tests candidate.packet.context.state _ candidate.packet.bounds _ 0 test member
      exact (tests test used).2 value seen
    · intro a one b two names origin located value seen
      obtain ⟨other,atOther,_⟩ := GeneralNominalCenteredCaptureSchema.many_capture
        candidate.packet.context.state _ candidate.packet.bounds _ 0 b two
      have same := agreement a one b two names origin other located atOther
      obtain ⟨actual,observed⟩ := same.2.1
      have fit := (anchors _ (anchored b two other atOther)).2 actual observed
      have equal := same.2.2 value actual seen observed
      exact ⟨subtype_trans fit.1 equal.2,subtype_trans equal.1 fit.2⟩
    · intro a one b two names first last atFirst atLast x y seenX seenY
      exact (agreement a one b two names first last atFirst atLast).2.2 x y seenX seenY

theorem frame_finished (candidate : Plan roles)
    (frame : GeneralNominalVersionedEvidence231.Frame registry state.core focus key candidate) :
    Finished (headInspection candidate) := by
  have prepared := frame.prepared
  rw [← frame.context_eq] at prepared
  obtain ⟨_,_,bounds,found,_,finished,_⟩ := prepared
  have equal : bounds = candidate.packet.bounds := Option.some.inj (found.symm.trans frame.located)
  subst bounds
  exact GeneralNominalInspectionAlignment.finished_origins candidate.packet.context.state _ candidate.packet.bounds _ _ 0 0 finished

theorem schema_projection (candidate : Plan roles)
    (frame : GeneralNominalVersionedEvidence231.Frame registry state.core focus key candidate)
    (model : Assignment) (valid : Models state model)
    (schema : GeneralNominalVersionedPlans231.SchemaHolds candidate candidate.headSchema model) :
    ProjectionModels candidate.packet.context.state (headInspection candidate) model :=
  (projection_iff candidate frame model valid schema.1).mpr
    (GeneralDictionaryHeadSharing220.agreement_of_holds candidate model
      (GeneralNominalVersionedHeadSharing232.schema_holds candidate model schema))
end Yulang.GeneralNominalVersionedCurrentProjection237
