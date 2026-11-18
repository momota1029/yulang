import Yulang.GeneralNominalBinderProducer254
import Yulang.GeneralNominalDefaultReadback254
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalCapturedOutput254
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatPatternSemantics GeneralNominalCenteredHeadMatSemanticSubstitution
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra)
open GeneralNominalCenteredHeadMatSemanticLabels (Inputs)
open GeneralNominalPatersonLineage (mass)
open GeneralPatternAdditiveDepth253 (depth)
open GeneralDictionaryAssociatedProvenance (Body Supplies)
open CommonNominalFullCarrier (Equivalent)
variable {roles : Roles.RoleDecls} {plan : Plan roles} {model : GeneralNominalCommonBridge.Assignment}

def BinderBound (plan : Plan roles) (model : GeneralNominalCommonBridge.Assignment) (bound : Nat) : Prop :=
 ∀ name ∈ plan.packet.declaration.outputNames, ∃ result : Pattern, result.variables = [] ∧
 Equivalent (model (plan.binder name)).1
   (eval (algebra plan.packet.registry.constructors plan.packet.context.interpretation) (fun _ => .bottom) result) ∧
 depth result ≤ bound

/-- Combine disjoint input captures with actual output-binder readbacks.
Unmentioned names remain symbolic; only the declared input/output domain is
asserted closed and bounded. -/
theorem combined
 (frame : GeneralNominalVersionedEvidence231.Frame registry state focus key plan)
 (branch : GeneralNominalVersionedPlans231.Holds plan model)
 (known : Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model plan.input labels)
 (outputs : BinderBound plan model bound) :
 ∃ capture : Nat → Pattern, ∀ name,
 name ∈ plan.packet.declaration.inputNames ∨ name ∈ plan.packet.declaration.outputNames →
 (capture name).variables = [] ∧
 Equivalent (model (plan.binder name)).1
   (eval (algebra plan.packet.registry.constructors plan.packet.context.interpretation) (fun _ => .bottom) (capture name)) ∧
 depth (capture name) ≤ max (mass labels) bound := by
 classical
 obtain ⟨inputs,_,_,parts,_,bounds⟩ := GeneralNominalInputReadback254.readback frame branch known
 let capture : Nat → Pattern := fun name => if output : name ∈ plan.packet.declaration.outputNames
   then Classical.choose (outputs name output) else inputs name
 refine ⟨capture,?_⟩
 intro name domain
 by_cases output : name ∈ plan.packet.declaration.outputNames
 · have facts := Classical.choose_spec (outputs name output)
   simp only [capture,dite_eq_left output]
   exact ⟨facts.1,facts.2.1,Nat.le_trans facts.2.2 (Nat.le_max_right _ _)⟩
 · have input : name ∈ plan.packet.declaration.inputNames := domain.resolve_right output
   simp only [capture,dite_eq_right output]
   exact ⟨(parts name input).1.1,(parts name input).2,Nat.le_trans (bounds name input) (Nat.le_max_left _ _)⟩

def bodyDepth : Body → Nat
 | .explicit equation => depth (normalize equation.rhs)
 | .default _ _ rhs => depth (GeneralNominalDefaultReadback254.pattern rhs)

theorem explicit_readback
 (frame : GeneralNominalVersionedEvidence231.Frame registry state focus key plan)
 (branch : GeneralNominalVersionedPlans231.Holds plan model)
 (known : Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model plan.input labels)
 (outputs : BinderBound plan model bound)
 (member : equation ∈ plan.packet.declaration.associated)
 (compiled : GeneralNominalCenteredHeadMatEffects.compileBody plan (.explicit equation) = some expression)
 (held : GeneralNominalCenteredHeadMatEffects.BodyHolds plan target model (.explicit equation)) :
 ∃ result : Pattern, result.variables = [] ∧
 Equivalent (model target).1
   (eval (algebra plan.packet.registry.constructors plan.packet.context.interpretation) (fun _ => .bottom) result) ∧
 depth result ≤ depth (normalize equation.rhs) + max (mass labels) bound := by
 obtain ⟨capture,values⟩ := combined frame branch known outputs
 have scope := plan.packet.checked.scope.2.1 equation member
 have heldValue := (GeneralNominalCenteredHeadMatEffects.body_equation compiled).mp held
 have normalized := GeneralNominalCenteredHeadMatCompilerSemantics.compiled_normalized
   (variables := GeneralNominalCenteredHeadMatEffects.variables plan model) compiled
 have actual : GeneralNominalCenteredHeadMatEffects.variables plan model .actual =
   fun name => (model (plan.binder name)).1 := by
   funext name
   simp only [GeneralNominalCenteredHeadMatEffects.variables,ite_self]
 rw [actual] at normalized
 have substituted := eval_congr (algebra := algebra plan.packet.registry.constructors plan.packet.context.interpretation)
   (normalize equation.rhs) (fun name used => (values name (scope name used)).2.1)
 rw [← eval_subst (normalize equation.rhs) capture] at substituted
 exact ⟨(normalize equation.rhs).subst capture,
   subst_closed _ _ (fun name used => (values name (scope name used)).1),
   eqv_trans (eqv_trans heldValue normalized) substituted,
   GeneralDeclarationOutputDepth253.subst_supported _ capture _ (fun name used => (values name (scope name used)).2.2)⟩

/-- Actual explicit/default output witnesses yield finite ground representatives
once the actual child-produced binders have finite representatives. -/
theorem witness_readback
 (frame : GeneralNominalVersionedEvidence231.Frame registry state focus key plan)
 (branch : GeneralNominalVersionedPlans231.Holds plan model)
 (known : Inputs (algebra plan.packet.registry.constructors plan.packet.context.interpretation) model plan.input labels)
 (outputs : BinderBound plan model bound)
 (witness : GeneralDictionaryDefaultEvidence204.OutputWitness plan model output) :
 ∃ body, Supplies roles plan.packet.declaration output.name body ∧
 ∃ result : Pattern, result.variables = [] ∧
 Equivalent (model output.target).1
   (eval (algebra plan.packet.registry.constructors plan.packet.context.interpretation) (fun _ => .bottom) result) ∧
 depth result ≤ bodyDepth body + max (mass labels) bound := by
 obtain ⟨body,supplied,⟨expression,compiled⟩,held⟩ := witness
 refine ⟨body,supplied,?_⟩
 cases supplied with
 | explicit equation present named =>
   exact explicit_readback frame branch known outputs present compiled held
 | default rhs absent declared =>
   have sameRole : plan.packet.declaration.role = plan.input.occurrence.demand.role := by
     rw [plan.input_exact,frame.occurrence_eq]; exact frame.role_eq
   obtain ⟨result,closed,meaning,small⟩ :=
     GeneralNominalDefaultReadback254.default_readback known sameRole declared compiled held
   exact ⟨result,closed,meaning,Nat.le_trans small (Nat.add_le_add_left (Nat.le_max_left _ _) _)⟩

end Yulang.GeneralNominalCapturedOutput254
