import Yulang.GeneralDictionaryCountedCandidate216
import Yulang.GeneralDictionaryRecursiveBounds215
import Yulang.GeneralDictionaryInspectionSchema215
import Yulang.GeneralDictionaryCurrentPropagation215

/-! Exact remaining centered projection condition for any current Frame:
recursive tests and anchors follow from actual counted inputs; same-name capture
agreement is still required. No historical declaration is assumed. -/
namespace Yulang.GeneralDictionaryCountedProjection216
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalRecursiveInspection GeneralNominalOriginTerms
open GeneralNominalQueryProvenance183 (headInspection)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}
set_option backward.isDefEq.respectTransparency false

def Agreement (candidate : Plan roles) (model : Assignment) : Prop :=
  ∀ a ∈ (headInspection candidate).captures, ∀ b ∈ (headInspection candidate).captures,
    a.name = b.name → ∀ first last, a.origin = some first → b.origin = some last → Same model first last

theorem projection_iff
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles) (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (model : Assignment) (valid : Models state model) :
    ProjectionModels candidate.packet.context.state (headInspection candidate) model ↔ Agreement candidate model := by
  have tests := GeneralDictionaryCountedCandidate216.tests source point ground coverage path candidate frame model valid
  have anchors : ∀ anchor ∈ (headInspection candidate).anchors,
      (∃ value, Observes model anchor.1 value) ∧
      ∀ value, Observes model anchor.1 value → Fits candidate.packet.context.state model anchor.2 value := by
    apply GeneralDictionaryRecursiveBounds215.many_bounds
    · rw [frame.context_eq]; exact valid.1
    · intro index
      simpa only [Nat.zero_add] using GeneralDictionaryCurrentRoots215.root_bounds candidate frame model valid index
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

end Yulang.GeneralDictionaryCountedProjection216
