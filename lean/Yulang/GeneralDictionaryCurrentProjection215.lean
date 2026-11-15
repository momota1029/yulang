import Yulang.GeneralDictionaryInspectionSchema215
import Yulang.GeneralDictionaryDefaultRevisit214

/-! Current centered projection assembly. Historical origin readback supplies
sharing; only recursive current-anchor interval soundness remains explicit. -/
namespace Yulang.GeneralDictionaryCurrentProjection215
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalQueryProvenance183 (headInspection)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}

theorem capture_readback {model : Assignment} (checked : Checked registry)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (registered : historical ∈ state.core.plans)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (valid : Models state model)
    (captured : Capture candidate.packet.context.state)
    (present : captured ∈ (headInspection candidate).captures) :
    ∃ origin, captured.origin = some origin ∧
      GeneralNominalOriginTerms.Same model origin (.source (historical.binder captured.name)) := by
  obtain ⟨origin,recorded,used⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    candidate.packet.context.state _ candidate.packet.bounds _ 0 captured present
  exact ⟨origin,recorded,GeneralDictionaryDefaultCandidateActual214.candidate_actual checked path
    historical candidate registered frame identity declaration ⟨captured.name,origin,.actual⟩ used rfl valid⟩

theorem projection_of_anchors (checked : Checked registry)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (historical candidate : Plan roles) (registered : historical ∈ state.core.plans)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (identity : candidate.packet.site.occurrence.identity = historical.packet.site.occurrence.identity)
    (declaration : candidate.packet.declaration = historical.packet.declaration)
    (model : Assignment) (valid : Models state model)
    (anchors : ∀ anchor ∈ (headInspection candidate).anchors,
      (∃ value, Observes model anchor.1 value) ∧
      ∀ value, Observes model anchor.1 value → Fits candidate.packet.context.state model anchor.2 value) :
    ProjectionModels candidate.packet.context.state (headInspection candidate) model := by
  have readings := capture_readback checked path historical candidate registered frame identity declaration valid
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
    exact (GeneralDictionaryDefaultRevisit214.candidate_tests checked path historical candidate registered
      frame identity declaration model valid test used).2 value seen
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
end Yulang.GeneralDictionaryCurrentProjection215
