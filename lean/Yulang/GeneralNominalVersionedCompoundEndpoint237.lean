import Yulang.GeneralNominalVersionedChildIntervals237
import Yulang.GeneralNominalVersionedJournal232
set_option backward.isDefEq.respectTransparency false
/-! A precise local obstruction to current total-packet completion. Versioned
capture endpoints do not version compound child endpoint targets. No reachable,
selected, stable or EvidenceNode counterexample is asserted here. -/
namespace Yulang.GeneralNominalVersionedCompoundEndpoint237
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedPlans231
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatSchemas GeneralNominalCenteredHeadMatExpressions
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls}

theorem variant_lower_target (plan : Plan roles) (clause : Clause) (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity)
    (pattern : clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt) = .variant tag (.var name)) :
    ((GeneralNominalVersionedFrame231.childSite plan clause signature).occurrence.demand.arguments index).1 =
      fresh plan.packet.context.state.seed plan.packet.site.occurrence.identity plan.packet.declaration.id 3 clause.id index.val := by
  change (GeneralDeclarationDemands.inputInterval _ _ _).1 = _
  rw [pattern]
  rfl

theorem variant_lower_value (plan : Plan roles) (model : Assignment) (clause : Clause)
    (member : clause ∈ plan.packet.declaration.requirements) (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity)
    (pattern : clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt) = .variant tag (.var name))
    (notOutput : name ∉ plan.packet.declaration.outputNames) (outputs : Outputs plan model) :
    Equivalent (model (fresh plan.packet.context.state.seed plan.packet.site.occurrence.identity
      plan.packet.declaration.id 3 clause.id index.val)).1
      (variant tag (model ((GeneralNominalVersionedFrame231.capture plan.packet).inputs name).1).1) := by
  have request := (GeneralNominalVersionedChildIntervals237.endpoint_requests plan clause member signature index).1
  have compiled : translate plan.packet.registry.constructors plan.packet.context.interpretation
      (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)) = some (.variant tag (.variable name)) := by
    rw [pattern]; rfl
  have semantic := generated_equation outputs request compiled
  rw [variant_lower_target plan clause signature index pattern] at semantic
  simpa only [value,variables,notOutput,ite_false] using semantic

theorem simultaneous_lower_equivalent (first last : Plan roles) (model : Assignment) (clause : Clause)
    (one : clause ∈ first.packet.declaration.requirements) (two : clause ∈ last.packet.declaration.requirements)
    (signature : clause.Signature roles) (index : Fin (roles clause.role).arity)
    (pattern : clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt) = .variant tag (.var name))
    (firstInput : name ∉ first.packet.declaration.outputNames) (lastInput : name ∉ last.packet.declaration.outputNames)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration.id = last.packet.declaration.id)
    (oldOutputs : Outputs first model) (newOutputs : Outputs last model) :
    Equivalent (model ((GeneralNominalVersionedFrame231.capture first.packet).inputs name).1).1
      (model ((GeneralNominalVersionedFrame231.capture last.packet).inputs name).1).1 := by
  have old := variant_lower_value first model clause one signature index pattern firstInput oldOutputs
  have current := variant_lower_value last model clause two signature index pattern lastInput newOutputs
  rw [seed,identity,declaration] at old
  exact ⟨(common_variant_iff ..).mp (subtype_trans old.2 current.1),
    (common_variant_iff ..).mp (subtype_trans current.2 old.1)⟩

theorem recorded_excludes_current (state : GeneralNominalVersionedJournal232.State roles)
    (first last : Plan roles) (model : Assignment) (recorded : first ∈ state.plans)
    (valid : GeneralNominalVersionedJournal232.Models state model) (clause : Clause)
    (one : clause ∈ first.packet.declaration.requirements) (two : clause ∈ last.packet.declaration.requirements)
    (signature : clause.Signature roles) (index : Fin (roles clause.role).arity)
    (pattern : clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt) = .variant tag (.var name))
    (firstInput : name ∉ first.packet.declaration.outputNames) (lastInput : name ∉ last.packet.declaration.outputNames)
    (seed : first.packet.context.state.seed = last.packet.context.state.seed)
    (identity : first.packet.site.occurrence.identity = last.packet.site.occurrence.identity)
    (declaration : first.packet.declaration.id = last.packet.declaration.id)
    (changed : ¬ Equivalent (model ((GeneralNominalVersionedFrame231.capture first.packet).inputs name).1).1
      (model ((GeneralNominalVersionedFrame231.capture last.packet).inputs name).1).1) : ¬ Holds last model := by
  intro completed
  exact changed (simultaneous_lower_equivalent first last model clause one two signature index pattern
    firstInput lastInput seed identity declaration (valid.2.1 first recorded).2.2 completed.2.2)
end Yulang.GeneralNominalVersionedCompoundEndpoint237
