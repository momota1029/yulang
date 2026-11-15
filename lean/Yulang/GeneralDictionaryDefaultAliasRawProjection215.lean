import Yulang.GeneralDictionaryDefaultAliasProjection215
import Yulang.GeneralDictionaryRawProjection215

/-! Full raw report projection follows from historical actual alias evidence
before current Prepared, with no point-input restriction. -/
namespace Yulang.GeneralDictionaryDefaultAliasRawProjection215
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles} {state : State roles}
set_option backward.isDefEq.respectTransparency false

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
    ProjectionModels candidate.packet.context.state
      (GeneralNominalRecursiveCandidates.report candidate.packet.context candidate.packet.declaration candidate.packet.bounds) model := by
  have rawValid : GeneralNominalState.Models candidate.packet.context.state model := by
    rw [current]
    exact valid.1
  have centered := GeneralDictionaryDefaultAliasProjection215.projection checked source path historical candidate registered
    current inputRegistered located alias declaration model valid
  change ProjectionModels candidate.packet.context.state
    (inspectMany candidate.packet.context.state (GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration) candidate.packet.bounds (fun _ => none) 0) model
  apply GeneralDictionaryWeakReport215.projection candidate.packet.context.state _ (GeneralNominalQueryProvenance183.headInspection candidate) _ centered
  apply GeneralDictionaryRawProjection215.many_related candidate.packet.context.state model rawValid _ candidate.packet.bounds
    (fun i => .source ((List.ofFn candidate.input.center)[i]?.getD 0)) 0
  · intro index
    simpa only [Nat.zero_add,GeneralDictionaryStructuralProjection215.Bounded,
      GeneralDictionaryDefaultNominalProjection215.Bounded] using
      GeneralDictionaryDefaultAliasProjection215.root_bounds candidate inputRegistered located model valid index
  · exact GeneralDictionaryDefaultAliasReadback215.candidate_tests checked source path historical candidate registered
      current inputRegistered alias declaration model valid

end Yulang.GeneralDictionaryDefaultAliasRawProjection215
