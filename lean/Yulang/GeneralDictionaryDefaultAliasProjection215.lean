import Yulang.GeneralDictionaryInspectionSchema215
import Yulang.GeneralDictionaryDefaultAliasReadback215
import Yulang.GeneralDictionaryRecursiveBounds215
import Yulang.GeneralNominalPacketCaptureReadback

/-! Current centered projection assembly. Historical origin readback supplies
sharing; only recursive current-anchor interval soundness remains explicit. -/
namespace Yulang.GeneralDictionaryDefaultAliasProjection215
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalQueryProvenance183 (headInspection)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

theorem capture_readback {model : Assignment} (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (registered : historical ∈ state.core.plans)
    (current : candidate.packet.context = state.core.erased.current.context)
    (inputRegistered : candidate.input ∈ state.core.sites)
    (alias : GeneralNominalSaturationState.Alias state.core.erased.current
      candidate.packet.site.occurrence.identity historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (valid : Models state model)
    (captured : Capture candidate.packet.context.state)
    (present : captured ∈ (headInspection candidate).captures) :
    ∃ origin, captured.origin = some origin ∧
      GeneralNominalOriginTerms.Same model origin (.source (historical.binder captured.name)) := by
  obtain ⟨origin,recorded,used⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    candidate.packet.context.state _ candidate.packet.bounds _ 0 captured present
  exact ⟨origin,recorded,GeneralDictionaryDefaultAliasReadback215.candidate_actual checked source path
    historical candidate registered current inputRegistered alias declaration ⟨captured.name,origin,.actual⟩ used rfl valid⟩

theorem projection_of_anchors (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (registered : historical ∈ state.core.plans)
    (current : candidate.packet.context = state.core.erased.current.context)
    (inputRegistered : candidate.input ∈ state.core.sites)
    (alias : GeneralNominalSaturationState.Alias state.core.erased.current
      candidate.packet.site.occurrence.identity historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model)
    (anchors : ∀ anchor ∈ (headInspection candidate).anchors,
      (∃ value, Observes model anchor.1 value) ∧
      ∀ value, Observes model anchor.1 value → Fits candidate.packet.context.state model anchor.2 value) :
    ProjectionModels candidate.packet.context.state (headInspection candidate) model := by
  have readings := capture_readback checked source path historical candidate registered current inputRegistered alias declaration valid
  have same (a b : Capture candidate.packet.context.state)
      (one : a ∈ (headInspection candidate).captures) (two : b ∈ (headInspection candidate).captures)
      (names : a.name = b.name) (first last : Origin) (firstAt : a.origin = some first)
      (lastAt : b.origin = some last) : GeneralNominalOriginTerms.Same model first last := by
    obtain ⟨x,atX,left⟩ := readings a one
    obtain ⟨y,atY,right⟩ := readings b two
    cases Option.some.inj (atX.symm.trans firstAt)
    cases Option.some.inj (atY.symm.trans lastAt)
    rw [names] at left
    exact GeneralNominalOriginTerms.same_trans left (GeneralNominalOriginTerms.same_symm right)
  refine ⟨anchors,?_,?_,?_⟩
  · intro test present value seen
    have used := GeneralDictionaryInspectionSchema215.many_tests candidate.packet.context.state _
      candidate.packet.bounds _ 0 test present
    exact (GeneralDictionaryDefaultAliasReadback215.candidate_tests checked source path historical candidate registered
      current inputRegistered alias declaration model valid test used).2 value seen
  · intro a one b two names origin located value seen
    obtain ⟨other,atOther,readback⟩ := readings b two
    have linked := same a b one two names origin other located atOther
    obtain ⟨actual,observed⟩ := linked.2.1
    have fit := (anchors (other,b.bounds)
      (GeneralNominalCaptureAnchors.many_anchored candidate.packet.context.state _ candidate.packet.bounds
        _ 0 b two other atOther)).2 actual observed
    have equal := linked.2.2 value actual seen observed
    exact ⟨subtype_trans fit.1 equal.2,subtype_trans equal.1 fit.2⟩
  · intro a one b two names first last firstAt lastAt x y seenX seenY
    exact (same a b one two names first last firstAt lastAt).2.2 x y seenX seenY


set_option backward.isDefEq.respectTransparency false
theorem root_bounds (candidate : Plan roles)
    (inputRegistered : candidate.input ∈ state.core.sites)
    (located : GeneralNominalRecursiveCandidates.arguments candidate.packet.context
      (GeneralNominalCenteredHeadCandidates.inputs candidate.input.occurrence) = some candidate.packet.bounds)
    (model : Assignment) (valid : Models state model)
    (index : Fin candidate.packet.bounds.length) :
    GeneralDictionaryDefaultNominalProjection215.Bounded candidate.packet.context.state model candidate.packet.bounds[index]
      (.source ((List.ofFn candidate.input.center)[index.val]?.getD 0)) := by
  have mapped := GeneralNominalPacketCaptureReadback.locate_sources
    candidate.packet.context.state.base (List.ofFn candidate.input.occurrence.demand.arguments) candidate.packet.bounds located
  let focus := candidate.input.occurrence
  have occurrence : candidate.input.occurrence = focus := rfl
  have held := valid.2.2.2.1 candidate.input inputRegistered
  have length : candidate.packet.bounds.length = (roles focus.demand.role).arity := by
    have lengths := congrArg List.length mapped
    simpa only [List.length_map,List.length_ofFn] using lengths
  have bounded : index.val < (roles focus.demand.role).arity := by omega
  change _ = List.ofFn focus.demand.arguments at mapped
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

theorem projection (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (registered : historical ∈ state.core.plans)
    (current : candidate.packet.context = state.core.erased.current.context)
    (inputRegistered : candidate.input ∈ state.core.sites)
    (located : GeneralNominalRecursiveCandidates.arguments candidate.packet.context
      (GeneralNominalCenteredHeadCandidates.inputs candidate.input.occurrence) = some candidate.packet.bounds)
    (alias : GeneralNominalSaturationState.Alias state.core.erased.current
      candidate.packet.site.occurrence.identity historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model) :
    ProjectionModels candidate.packet.context.state (headInspection candidate) model := by
  apply projection_of_anchors checked source path historical candidate registered current inputRegistered alias declaration model valid
  apply GeneralDictionaryRecursiveBounds215.many_bounds
  · rw [current]
    exact valid.1
  · intro index
    simpa only [Nat.zero_add,GeneralDictionaryStructuralProjection215.Bounded,
      GeneralDictionaryDefaultNominalProjection215.Bounded] using root_bounds candidate inputRegistered located model valid index
  · exact GeneralDictionaryDefaultAliasReadback215.candidate_tests checked source path historical candidate registered
      current inputRegistered alias declaration model valid

end Yulang.GeneralDictionaryDefaultAliasProjection215
