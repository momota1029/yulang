import Yulang.GeneralDictionaryCountedProjection216
import Yulang.GeneralDictionaryRawProjection215
import Yulang.GeneralDictionaryCurrentBranch215

/-! In any corrected current Frame, capture agreement gives raw projection;
merge equations are then exactly the remaining fixed-journal-model head test. -/
namespace Yulang.GeneralDictionaryCountedRawHead216
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryCountedProjection216 (Agreement)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}
set_option backward.isDefEq.respectTransparency false

 theorem raw_projection
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles) (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (model : Assignment) (valid : Models state model) (agreement : Agreement candidate model) :
    ProjectionModels candidate.packet.context.state
      (GeneralNominalRecursiveCandidates.report candidate.packet.context candidate.packet.declaration candidate.packet.bounds) model := by
  have centered := (GeneralDictionaryCountedProjection216.projection_iff source point ground coverage path candidate frame model valid).mpr agreement
  have tests := GeneralDictionaryCountedCandidate216.tests source point ground coverage path candidate frame model valid
  have rawValid : GeneralNominalState.Models candidate.packet.context.state model := by rw [frame.context_eq]; exact valid.1
  change ProjectionModels candidate.packet.context.state
    (inspectMany candidate.packet.context.state (GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration) candidate.packet.bounds (fun _ => none) 0) model
  apply GeneralDictionaryWeakReport215.projection candidate.packet.context.state _ (GeneralNominalQueryProvenance183.headInspection candidate) _ centered
  apply GeneralDictionaryRawProjection215.many_related candidate.packet.context.state model rawValid _ candidate.packet.bounds
    (fun i => .source ((List.ofFn candidate.input.center)[i]?.getD 0)) 0
  · intro index
    simpa only [Nat.zero_add] using GeneralDictionaryCurrentRoots215.root_bounds candidate frame model valid index
  · exact tests

 theorem head_iff_merges
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (candidate : Plan roles) (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key candidate)
    (model : Assignment) (valid : Models state model) (agreement : Agreement candidate model) :
    GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
      candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model ↔
    PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.merges candidate.packet.context.state candidate.packet.registry
        candidate.packet.site.occurrence.identity candidate.packet.declaration candidate.packet.bindings) := by
  constructor
  · exact GeneralDictionaryCurrentBranch215.branch_merges candidate model
  · intro merges
    have centered := (GeneralDictionaryCountedProjection216.projection_iff source point ground coverage path candidate frame model valid).mpr agreement
    refine ⟨?_,raw_projection source point ground coverage path candidate frame model valid agreement⟩
    unfold GeneralNominalRecursiveCandidates.privateState
    apply (GeneralNominalState.extend_models ..).mpr
    refine ⟨?_,?_⟩
    · apply (GeneralNominalAllocation.propagate_models ..).mpr
      refine ⟨?_,GeneralDictionaryCurrentPropagation215.capture_compatible candidate model centered,merges⟩
      rw [frame.context_eq]; exact valid.1
    · have located := frame.located
      rw [← frame.occurrence_eq,← candidate.input_exact] at located
      exact GeneralDictionaryCurrentPropagation215.raw_checks candidate frame.center_recorded located model valid centered

end Yulang.GeneralDictionaryCountedRawHead216
