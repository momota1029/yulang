import Yulang.GeneralVersionedAliasReadback312
import Yulang.GeneralDictionaryDefaultAliasRawProjection215
import Yulang.GeneralDictionaryCurrentPropagation215
import Yulang.GeneralDictionaryInspectionConflicts215
import Yulang.GeneralVersionedProtectedPeer312

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
/-! Readback at an alias yields actual current nonaggregate report semantics
without already assuming the prospective historic candidate is Prepared. -/
namespace Yulang.GeneralVersionedAliasReport312
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms
open GeneralNominalQueryProvenance183 (headInspection)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryStructuralProjection215 (Bounded)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {state : State roles}
theorem root_bounds (candidate : Plan roles)
    (registered : candidate.input ∈ state.core.sites)
    (located : GeneralNominalRecursiveCandidates.arguments candidate.packet.context
      (GeneralNominalVersionedCandidates231.inputs candidate.packet.site.occurrence) = some candidate.packet.bounds)
    (model : Assignment) (valid : Models state model)
    (index : Fin candidate.packet.bounds.length) :
    Bounded candidate.packet.context.state model candidate.packet.bounds[index]
      (.source ((List.ofFn candidate.input.center)[index.val]?.getD 0)) := by
  have mapped := GeneralNominalPacketCaptureReadback.locate_sources
    candidate.packet.context.state.base (List.ofFn candidate.packet.site.occurrence.demand.arguments) candidate.packet.bounds located
  have occurrence := candidate.input_exact
  have held := valid.1.2.2.2.1 candidate.input registered
  have length : candidate.packet.bounds.length = (roles candidate.packet.site.occurrence.demand.role).arity := by
    have lengths := congrArg List.length mapped
    simpa only [List.length_map,List.length_ofFn] using lengths
  have bounded : index.val < (roles candidate.packet.site.occurrence.demand.role).arity := by omega
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
    (candidate : Plan roles)
    (current : candidate.packet.context = state.core.erased.current.context)
    (registered : candidate.input ∈ state.core.sites)
    (located : GeneralNominalRecursiveCandidates.arguments candidate.packet.context
      (GeneralNominalVersionedCandidates231.inputs candidate.packet.site.occurrence) = some candidate.packet.bounds)
    (model : Assignment) (valid : Models state model)
    (tests : ∀ test ∈ candidate.headSchema.tests, Head model test.1 test.2) :
    ProjectionModels candidate.packet.context.state (headInspection candidate) model ↔ GeneralDictionaryCountedProjection216.Agreement candidate model := by
  have anchors : ∀ anchor ∈ (headInspection candidate).anchors,
      (∃ value, Observes model anchor.1 value) ∧
      ∀ value, Observes model anchor.1 value → Fits candidate.packet.context.state model anchor.2 value := by
    apply GeneralDictionaryRecursiveBounds215.many_bounds
    · rw [current]; exact valid.1.1
    · intro index
      simpa only [Nat.zero_add] using root_bounds candidate registered located model valid index
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

theorem from_tests (candidate : Plan roles)
    (current : candidate.packet.context = state.core.erased.current.context)
    (registered : candidate.input ∈ state.core.sites)
    (located : GeneralNominalRecursiveCandidates.arguments candidate.packet.context
      (GeneralNominalVersionedCandidates231.inputs candidate.packet.site.occurrence) = some candidate.packet.bounds)
    (model : Assignment) (valid : Models state model)
    (tests : ∀ test ∈ candidate.headSchema.tests, Head model test.1 test.2)
    (agreement : GeneralDictionaryCountedProjection216.Agreement candidate model) :
    (GeneralNominalPacketSupport.report candidate.packet).conflicts = [] ∧
    GeneralVersionedProtectedPeer312.Raw candidate.packet model := by
  have rawValid : GeneralNominalState.Models candidate.packet.context.state model := by
    rw [current]
    exact valid.1.1
  have centered := (projection_iff candidate current registered located model valid tests).mpr agreement
  have bound := root_bounds candidate registered located model valid
  have conflict : (GeneralNominalPacketSupport.report candidate.packet).conflicts = [] := by
    apply GeneralDictionaryInspectionConflicts215.many_clear_any_origins candidate.packet.context.state model
      rawValid _ candidate.packet.bounds (fun i => .source ((List.ofFn candidate.input.center)[i]?.getD 0)) 0
    · intro index
      simpa only [Nat.zero_add,GeneralDictionaryStructuralProjection215.Bounded,
        GeneralDictionaryDefaultNominalProjection215.Bounded] using bound index
    · exact tests
  have raw : ProjectionModels candidate.packet.context.state
      (GeneralNominalPacketSupport.report candidate.packet) model := by
    change ProjectionModels candidate.packet.context.state
      (inspectMany candidate.packet.context.state (GeneralNominalInspection.queries candidate.packet.context.state
        candidate.packet.context.interpretation candidate.packet.declaration) candidate.packet.bounds (fun _ => none) 0) model
    apply GeneralDictionaryWeakReport215.projection candidate.packet.context.state _ (headInspection candidate) _ centered
    apply GeneralDictionaryRawProjection215.many_related candidate.packet.context.state model rawValid _ candidate.packet.bounds
      (fun i => .source ((List.ofFn candidate.input.center)[i]?.getD 0)) 0
    · intro index
      simpa only [Nat.zero_add,GeneralDictionaryStructuralProjection215.Bounded,
        GeneralDictionaryDefaultNominalProjection215.Bounded] using bound index
    · exact tests
  refine ⟨conflict,GeneralDictionaryCurrentPropagation215.capture_compatible candidate model centered,?_,raw⟩
  intro atom member
  obtain ⟨bounds,present,rfl⟩ := List.mem_map.mp member
  change bounds ∈ candidate.packet.bounds ++ _ at present
  rcases List.mem_append.mp present with root | checked
  · obtain ⟨index,bounded,found⟩ := List.mem_iff_getElem.mp root
    obtain ⟨value,observed⟩ := (bound ⟨index,bounded⟩).1
    have fit := (bound ⟨index,bounded⟩).2 value observed
    simp only [Fin.getElem_fin,found] at fit
    exact subtype_trans fit.1 fit.2
  · have equal := GeneralDictionaryCheckedOrigins215.many_shape candidate.packet.context.state
      (GeneralNominalInspection.queries candidate.packet.context.state candidate.packet.context.interpretation candidate.packet.declaration)
      candidate.packet.bounds (fun _ => none)
      (fun index => some (.source ((List.ofFn candidate.input.center)[index]?.getD 0))) 0 0
    rw [GeneralDictionaryCheckedOrigins215.shape] at equal
    rw [equal] at checked
    exact GeneralDictionaryCurrentPropagation215.centered_checks candidate model centered _
      (List.mem_map.mpr ⟨bounds,checked,rfl⟩)

theorem from_alias
    (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root state)
    (historical candidate : Plan roles) (stored : historical ∈ state.plans)
    (registered : candidate.input ∈ state.core.sites)
    (current : candidate.packet.context = state.core.erased.current.context)
    (located : GeneralNominalRecursiveCandidates.arguments candidate.packet.context
      (GeneralNominalVersionedCandidates231.inputs candidate.packet.site.occurrence) = some candidate.packet.bounds)
    (alias : GeneralNominalSaturationState.Alias state.core.erased.current
      candidate.packet.site.occurrence.identity historical.packet.site.occurrence.identity)
    (decl : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model) :
    (GeneralNominalPacketSupport.report candidate.packet).conflicts = [] ∧
    GeneralVersionedProtectedPeer312.Raw candidate.packet model := by
  obtain ⟨tests,captures⟩ := GeneralVersionedAliasReadback312.readback checked path stored registered current alias decl valid
  apply from_tests candidate current registered located model valid tests
  apply GeneralDictionaryHeadSharing220.agreement_of_holds candidate model
  apply (GeneralDictionaryHeadSharing220.holds_iff candidate model).mpr
  intro first one last two equal
  have head := captures first one
  rw [equal] at head
  exact same_trans head (same_symm (captures last two))

end Yulang.GeneralVersionedAliasReport312
