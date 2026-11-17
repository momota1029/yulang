import Yulang.GeneralNominalVersionedHeadReadback237
namespace Yulang.GeneralNominalVersionedChildLabels237
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatPatternSemantics GeneralNominalCenteredHeadMatSemanticSubstitution
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra compiled_normalized)
open GeneralNominalCenteredHeadMatSemanticLabels
open CommonNominalFullCarrier
set_option backward.isDefEq.respectTransparency false
variable {roles : Roles.RoleDecls} {plan : Plan roles} {model : GeneralNominalCommonBridge.Assignment}

theorem argument_value (branch : GeneralNominalVersionedPlans231.Holds plan model)
    (member : clause ∈ plan.packet.declaration.requirements) (signature : clause.Signature roles)
    (index : Fin (roles clause.role).arity)
    (translated : GeneralNominalCenteredHeadMatExpressions.translate plan.packet.registry.constructors
      plan.packet.context.interpretation
      (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)) = some expression) :
    Equivalent (model ((GeneralNominalVersionedFrame231.childSite plan clause signature).center index)).1
      (GeneralNominalCenteredHeadMatExpressions.value (GeneralNominalVersionedPlans231.variables plan model) .actual expression) := by
  have schema := (branch.2.1.2.2.2.2.2.2 clause member signature).2
  exact GeneralNominalCenteredHeadMatSchemas.generated_equation schema
    (List.mem_ofFn.mpr ⟨index,rfl⟩) translated

theorem child_normalized (branch : GeneralNominalVersionedPlans231.Holds plan model)
    (member : clause ∈ plan.packet.declaration.requirements) (signature : GeneralDeclarations.Clause.Signature roles clause)
    (index : Fin (roles clause.role).arity)
    (covered : GeneralNominalCenteredHeadWFSource.PatternCovered plan.packet.registry.constructors plan.packet.context.interpretation
      (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt))) :
    Equivalent (model ((GeneralNominalVersionedFrame231.childSite plan clause signature).center index)).1
      (eval (algebra plan.packet.registry.constructors plan.packet.context.interpretation)
        (fun name => (model (plan.binder name)).1)
        (normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt)))) := by
  obtain ⟨expression,translated⟩ := GeneralNominalCenteredHeadMatExpressions.translate_complete covered
  have actual := argument_value branch member signature index translated
  have normalized := compiled_normalized (variables := GeneralNominalVersionedPlans231.variables plan model) translated
  have variables : GeneralNominalVersionedPlans231.variables plan model .actual = fun name => (model (plan.binder name)).1 := by
    funext name
    simp only [GeneralNominalVersionedPlans231.variables,ite_self,GeneralNominalVersionedFrame231.binder_eq]
  rw [variables] at normalized
  exact eqv_trans actual normalized

theorem child_meaning (branch : GeneralNominalVersionedPlans231.Holds plan model)
    (captures : Captures plan model capture) (member : clause ∈ plan.packet.declaration.requirements)
    (signature : clause.Signature roles) (index : Fin (roles clause.role).arity)
    (source : GeneralNominalCenteredHeadWFSource.PatternCovered plan.packet.registry.constructors plan.packet.context.interpretation
      (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt))) :
    CountedMeaning (algebra plan.packet.registry.constructors plan.packet.context.interpretation)
      (model ((GeneralNominalVersionedFrame231.childSite plan clause signature).center index)).1
      ((normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt))).subst (images capture)) := by
  let pattern := normalize (clause.arguments[index.val]'(by rw [signature.1]; exact index.isLt))
  have needed : ∀ name ∈ pattern.variables, GeneralNominalSharedCaptures.Needed plan.packet name :=
    fun name used => argument_needed member signature index used
  have complete : covered pattern = true := by
    apply GeneralNominalChildAssembly.covered_member (normalizeArgs clause.arguments)
      (plan.packet.checked.countsCovered clause member).2 pattern
    rw [GeneralNominalChildAssembly.normalize_map]
    exact List.mem_map.mpr ⟨_,List.getElem_mem ..,rfl⟩
  have closed := subst_closed pattern (images capture) (fun name used => (captures.2 name (needed name used)).1)
  have coveredSubst := GeneralNominalTemplateSubstitution.subst_covered pattern complete (images capture) captures.1
  refine ⟨normalized_closed closed,GeneralPatternNormalForm.covered_normal _
    (GeneralPatternNormalForm.normalized _ coveredSubst),?_⟩
  have before := child_normalized branch member signature index source
  have substituted := normalized_subst_meaning (images capture)
    (fun name used => (captures.2 name (needed name used)).2.2)
  exact eqv_trans before substituted

theorem child_inputs (branch : GeneralNominalVersionedPlans231.Holds plan model)
    (captures : Captures plan model capture) (member : clause ∈ plan.packet.declaration.requirements)
    (signature : clause.Signature roles)
    (source : GeneralNominalCenteredHeadWFSource.PatternsCovered plan.packet.registry.constructors
      plan.packet.context.interpretation clause.arguments) :
    Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model
      (GeneralNominalVersionedFrame231.childSite plan clause signature) (labels capture clause) := by
  have length : (labels capture clause).length = (roles clause.role).arity := by
    simpa only [labels,GeneralNominalChildAssembly.substitute_map,GeneralNominalChildAssembly.normalize_map,
      List.length_map] using signature.1
  refine ⟨length,?_⟩
  intro index
  have meaning := child_meaning branch captures member signature index
    (GeneralNominalCenteredHeadMatSchemas.patterns_member source (List.getElem_mem ..))
  simpa only [labels,GeneralNominalChildAssembly.substitute_map,GeneralNominalChildAssembly.normalize_map,
    List.getElem_map] using meaning


end Yulang.GeneralNominalVersionedChildLabels237
