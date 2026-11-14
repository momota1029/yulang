import Yulang.GeneralNominalCenteredHeadMatStepHeadMatching

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCenteredHeadMatStepChildReadback
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatStepPackets (Holds)
open GeneralNominalCenteredHeadMatEffects (variables)
open GeneralNominalCenteredCaptureLabels (Ready)
open GeneralNominalOriginTerms GeneralNominalFiniteMeaning GeneralNominalCompoundReadback
open CommonNominalFullCarrier GeneralNominalGroundAccessibility GeneralNominalCanonicalTemplates GeneralNominalChildAssembly
variable {roles : Roles.RoleDecls} {plan : Plan roles} {model : Assignment}

theorem argument_value (branch : Holds plan model) (member : clause ∈ plan.packet.declaration.requirements)
    (signature : clause.Signature roles) (index : Fin (roles clause.role).arity)
    (translated : GeneralNominalCenteredHeadMatExpressions.translate plan.packet.registry.constructors
      plan.packet.context.interpretation
      (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)) = some expression) :
    Equivalent (model ((plan.childSite clause signature).center index)).1
      (GeneralNominalCenteredHeadMatExpressions.value (variables plan model) .actual expression) := by
  have schema := (branch.2.1.2.2.2.2.2.2 clause member signature).2
  exact GeneralNominalCenteredHeadMatSchemas.generated_equation schema
    (List.mem_ofFn.mpr ⟨index,rfl⟩) translated

theorem variable_argument (branch : Holds plan model) (member : clause ∈ plan.packet.declaration.requirements)
    (signature : clause.Signature roles) (index : Fin (roles clause.role).arity)
    (isVariable : clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt) = .var name) :
    Equivalent (model ((plan.childSite clause signature).center index)).1 (model (plan.binder name)).1 := by
  have translated : GeneralNominalCenteredHeadMatExpressions.translate plan.packet.registry.constructors
      plan.packet.context.interpretation
      (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)) = some (.variable name) := by
    rw [isVariable]; rfl
  have result := argument_value branch member signature index translated
  change Equivalent _ (if name ∈ plan.packet.declaration.outputNames then
    (model (plan.binder name)).1 else (model (plan.binder name)).1) at result
  split at result <;> exact result

theorem variable_meaning (branch : Holds plan model) (ready : Ready context plan model capture)
    (member : clause ∈ plan.packet.declaration.requirements)
    (signature : clause.Signature roles) (index : Fin (roles clause.role).arity)
    (isVariable : clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt) = .var name) :
    ∃ term, ClosedTerm context (capture name) term ∧
      At model .actual (.source ((plan.childSite clause signature).center index)) (denote (fun _ => .bottom) term) := by
  have used : GeneralNominalSharedCaptures.Needed plan.packet name := by
    refine ⟨clause,member,?_⟩
    apply argument_variables _ (.var name)
    · rw [normalize_map]
      exact List.mem_map.mpr ⟨_,List.getElem_mem ..,by rw [isVariable]; rfl⟩
    · exact List.mem_singleton_self _
  obtain ⟨term,closed,meaning⟩ := (ready.2.2 name used).1
  refine ⟨term,closed,⟨_,.source _⟩,?_⟩
  intro actual seen
  cases seen
  have center := variable_argument branch member signature index isVariable
  have captured := meaning.2 _ (.source _)
  exact ⟨subtype_trans center.1 captured.1,subtype_trans captured.2 center.2⟩

end Yulang.GeneralNominalCenteredHeadMatStepChildReadback
