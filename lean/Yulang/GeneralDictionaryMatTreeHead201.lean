import Yulang.GeneralDictionaryMatInputAssembly201
import Yulang.GeneralNominalTreeFacts

/-! Structural head models are realized in the given assignment, not borrowed
from the existential Prepared witness. Named root outputs are unrestricted. -/
namespace Yulang.GeneralDictionaryMatTreeHead201
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls}

/-- Only existing finite-tree and exact inspection/allocation data. -/
structure HeadTree (plan : Plan roles) where
  arity : Nat
  names : Fin arity → Nat
  distinct : Function.Injective names
  inputs : plan.packet.declaration.inputNames = List.ofFn names
  bounds : Fin arity → GeneralNominalInspection.Bounds plan.packet.context.state
  slot : Fin plan.packet.context.state.base.slots
  tree : GeneralNominalTreeFacts.Tree plan.packet.context.state names bounds slot
  query : GeneralNominalInspection.queries plan.packet.context.state plan.packet.context.interpretation
    plan.packet.declaration = [tree.query]
  located : plan.packet.bounds = [(slot,slot)]

theorem head_models (plan : Plan roles) (shape : HeadTree plan)
    (assignment : Assignment) (valid : GeneralNominalState.Models plan.packet.context.state assignment) :
    GeneralNominalCenteredHeadCandidates.HeadModels plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.bounds assignment := by
  rw [shape.located]
  exact GeneralNominalTreeFacts.private_models plan.packet.context plan.packet.registry
    (GeneralNominalCenteredHeadCandidates.inputs plan.packet.site.occurrence)
    plan.packet.declaration shape.names shape.distinct shape.inputs shape.bounds shape.tree shape.query assignment valid

theorem current_head_models (plan : Plan roles) (shape : HeadTree plan)
    (state : GeneralNominalCenteredHeadMatStepJournal.State roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (assignment : Assignment) (models : GeneralNominalCenteredHeadMatStepJournal.Models state assignment) :
    GeneralNominalCenteredHeadCandidates.HeadModels plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.bounds assignment := by
  apply head_models plan shape assignment
  rw [frame.context_eq]
  exact models.1

/-- The whole common head component is derived, rather than assumed. -/
theorem packet_of_current_tree (effect : GeneralNominalCenteredHeadMatStepJournal.Effect roles)
    (state : GeneralNominalCenteredHeadMatStepJournal.State roles)
    (snapshot : effect.snapshot = state.core)
    (shape : HeadTree effect.plan)
    (restricted : GeneralDictionaryMatInputVariables201.InputVariableClauses effect.plan.packet.declaration)
    (assignment : Assignment) (models : GeneralNominalCenteredHeadMatStepJournal.Models state assignment)
    (chosen : effect.Holds assignment) :
    GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan assignment :=
  GeneralDictionaryMatInputAssembly201.holds_of_head_class effect.plan effect.snapshot
    effect.frame.raw_recorded assignment
    (current_head_models effect.plan shape state (snapshot ▸ effect.frame) assignment models)
    chosen.1 chosen.2 restricted

end Yulang.GeneralDictionaryMatTreeHead201
