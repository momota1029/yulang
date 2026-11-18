import Yulang.GeneralNominalInputReadback254
import Yulang.GeneralDeclarationOutputDepth253
set_option backward.isDefEq.respectTransparency false

/-! Actual emitted outputs with input-only templates have a closed finite
readback bounded by template depth plus source-label mass. This bound is for
the displayed substituted representative, before a second normalization. -/
namespace Yulang.GeneralNominalOutputReadback254
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatPatternSemantics GeneralNominalCenteredHeadMatSemanticSubstitution
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalCenteredHeadMatSemanticLabels (Inputs)
open GeneralNominalCenteredHeadMatSchemaMass (Part)
open GeneralNominalPatersonLineage (mass)
open GeneralPatternAdditiveDepth253 (depth)
open CommonNominalFullCarrier (Equivalent)
variable {roles : Roles.RoleDecls} {plan : Plan roles} {model : GeneralNominalCommonBridge.Assignment}

theorem emitted_meaning
 (branch : GeneralNominalVersionedPlans231.Holds plan model)
 (member : request ∈ GeneralNominalVersionedPlans231.emittedRequests plan.packet)
 (actual : request.mode = .actual)
 (compiled : GeneralNominalCenteredHeadMatExpressions.translate plan.packet.registry.constructors
   plan.packet.context.interpretation request.pattern = some expression) :
 Equivalent (model request.target).1
   (eval (algebra plan.packet.registry.constructors plan.packet.context.interpretation)
     (fun name => (model (plan.binder name)).1) (normalize request.pattern)) := by
 have equation := GeneralNominalCenteredHeadMatSchemas.generated_equation branch.2.2 member compiled
 rw [actual] at equation
 have meaning := GeneralNominalCenteredHeadMatCompilerSemantics.compiled_normalized
   (variables := GeneralNominalVersionedPlans231.variables plan model) compiled
 have values : GeneralNominalVersionedPlans231.variables plan model .actual =
   fun name => (model (plan.binder name)).1 := by
   funext name
   simp only [GeneralNominalVersionedPlans231.variables,GeneralNominalVersionedFrame231.binder_eq]
   by_cases h : name ∈ plan.packet.declaration.outputNames <;> simp only [h,ite_true,ite_false]
 rw [values] at meaning
 exact eqv_trans equation meaning

theorem emitted_readback
 (frame : GeneralNominalVersionedEvidence231.Frame registry state focus key plan)
 (branch : GeneralNominalVersionedPlans231.Holds plan model)
 (known : Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model plan.input labels)
 (member : request ∈ GeneralNominalVersionedPlans231.emittedRequests plan.packet)
 (actual : request.mode = .actual)
 (compiled : GeneralNominalCenteredHeadMatExpressions.translate plan.packet.registry.constructors
   plan.packet.context.interpretation request.pattern = some expression)
 (scope : ∀ name ∈ (normalize request.pattern).variables, name ∈ plan.packet.declaration.inputNames) :
 ∃ result : Pattern, result.variables = [] ∧
 Equivalent (model request.target).1
   (eval (algebra plan.packet.registry.constructors plan.packet.context.interpretation) (fun _ => .bottom) result) ∧
 depth result ≤ depth (normalize request.pattern) + mass labels := by
 obtain ⟨capture,_,_,parts,_,bounded⟩ := GeneralNominalInputReadback254.readback frame branch known
 refine ⟨(normalize request.pattern).subst capture,?_,?_,?_⟩
 · exact subst_closed _ capture (fun name used => (parts name (scope name used)).1.1)
 · have meaning := emitted_meaning branch member actual compiled
   have substituted := eval_congr (algebra := algebra plan.packet.registry.constructors plan.packet.context.interpretation) (normalize request.pattern) (fun name used => (parts name (scope name used)).2)
   rw [← eval_subst (normalize request.pattern) capture] at substituted
   exact eqv_trans meaning substituted
 · exact GeneralDeclarationOutputDepth253.subst_supported _ capture _ (fun name used => bounded name (scope name used))

/-- A checked leaf cannot have an output-only binder: each such binder must
have a designated where-child producer under the existing declaration rule. -/
theorem leaf_no_output_names
 (checked : DeclarationChecked constructors roles declaration)
 (leaf : declaration.requirements = []) : declaration.outputNames = [] := by
 apply List.eq_nil_iff_forall_not_mem.mpr
 intro name member
 obtain ⟨binder,present,_⟩ := List.mem_map.mp member
 obtain ⟨clause,child,_⟩ := checked.produced binder present
 rw [leaf] at child
 cases child

theorem leaf_associated_scope
 (checked : DeclarationChecked constructors roles declaration)
 (leaf : declaration.requirements = [])
 (member : equation ∈ declaration.associated) :
 ∀ name ∈ (normalize equation.rhs).variables, name ∈ declaration.inputNames := by
 intro name used
 rcases checked.scope.2.1 equation member name used with input | output
 · exact input
 · rw [leaf_no_output_names checked leaf] at output
   cases output


theorem leaf_root_readback
 (frame : GeneralNominalVersionedEvidence231.Frame registry state focus key plan)
 (branch : GeneralNominalVersionedPlans231.Holds plan model)
 (known : Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model plan.input labels)
 (leaf : plan.packet.declaration.requirements = [])
 (coverage : GeneralNominalCenteredHeadWFSource.DeclarationCovered plan.packet.registry.constructors
   plan.packet.context.interpretation plan.packet.declaration)
 (request : GeneralNominalMaterialization.Request)
 (member : request ∈ GeneralNominalMaterialization.rootRequests plan.packet.declaration plan.packet.site.occurrence) :
 ∃ result : Pattern, result.variables = [] ∧
 Equivalent (model request.target).1
   (eval (algebra plan.packet.registry.constructors plan.packet.context.interpretation) (fun _ => .bottom) result) ∧
 depth result ≤ depth (normalize request.pattern) + mass labels := by
 obtain ⟨output,_,within⟩ := List.mem_flatMap.mp member
 obtain ⟨equation,found,same⟩ := List.mem_map.mp within
 have equationMember := List.mem_of_find?_eq_some (Option.mem_toList.mp found)
 have covered := coverage.2.2 equation equationMember
 obtain ⟨expression,compiled⟩ := GeneralNominalCenteredHeadMatExpressions.translate_complete covered
 have retained : request ∈ GeneralNominalVersionedPlans231.emittedRequests plan.packet :=
   List.mem_append_left _ (List.mem_flatMap.mpr ⟨output,by assumption,List.mem_map.mpr ⟨equation,found,same⟩⟩)
 subst request
 exact emitted_readback frame branch known retained rfl compiled
   (leaf_associated_scope plan.packet.checked leaf equationMember)

end Yulang.GeneralNominalOutputReadback254

