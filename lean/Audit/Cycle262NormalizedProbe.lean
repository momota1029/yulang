import Yulang.GeneralRebasePlanSemantic262
import Yulang.GeneralNominalCenteredHeadMatSemanticSubstitution

namespace Cycle262NormalizedProbe
open Yulang GeneralNominalCenters GeneralDeclarationPatterns
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatEffects
open GeneralNominalCenteredHeadMatExpressions (Expr value)
open GeneralNominalCenteredHeadMatPatternSemantics (eval eqv_trans eqv_symm)
open CommonNominalFullCarrier

theorem explicit_value (first last : Plan roles) (assignment : Assignment)
 (layout : GeneralRebasePlanSemantic262.Layout first last)
 (equation : GeneralDeclarations.Equation) (expression : Expr)
 (compiled : compileBody first (.explicit equation) = some expression)
 (same : ∀ name ∈ (normalize equation.rhs).variables,
   Equivalent (assignment (first.binder name)).1 (assignment (last.binder name)).1) :
 Equivalent (value (variables first assignment) .actual expression)
   (value (variables last assignment) .actual expression) := by
 have compiled' : compileBody last (.explicit equation) = some expression :=
   (GeneralRebasePlanSemantic262.compile_eq first last layout _).symm.trans compiled
 have one := GeneralNominalCenteredHeadMatCompilerSemantics.compiled_normalized
   (variables := variables first assignment) compiled
 have two := GeneralNominalCenteredHeadMatCompilerSemantics.compiled_normalized
   (variables := variables last assignment) compiled'
 have middle : Equivalent
   (eval (GeneralNominalCenteredHeadMatCompilerSemantics.algebra first.packet.registry.constructors
     first.packet.context.interpretation) (variables first assignment .actual) (normalize equation.rhs))
   (eval (GeneralNominalCenteredHeadMatCompilerSemantics.algebra last.packet.registry.constructors
     last.packet.context.interpretation) (variables last assignment .actual) (normalize equation.rhs)) := by
   rw [layout.constructors,layout.interpretation]
   apply GeneralNominalCenteredHeadMatSemanticSubstitution.eval_congr
   intro name member
   simpa only [actual_variable] using same name member
 exact eqv_trans one (eqv_trans middle (eqv_symm two))

theorem explicit_body (first last : Plan roles) (assignment : Assignment)
 (layout : GeneralRebasePlanSemantic262.Layout first last)
 (equation : GeneralDeclarations.Equation) (target : Nat)
 (same : ∀ name ∈ (normalize equation.rhs).variables,
   Equivalent (assignment (first.binder name)).1 (assignment (last.binder name)).1) :
 GeneralNominalVersionedEffects231.BodyHolds first target assignment (.explicit equation) ↔
 GeneralNominalVersionedEffects231.BodyHolds last target assignment (.explicit equation) := by
 rw [GeneralNominalVersionedEffects231.body_holds_iff,GeneralNominalVersionedEffects231.body_holds_iff]
 have compile := GeneralRebasePlanSemantic262.compile_eq first last layout (.explicit equation)
 cases result : compileBody first (.explicit equation) with
 | none =>
   have other := compile.symm.trans result
   simp [BodyHolds,bodySchema,result,other,GeneralNominalCenteredHeadMatSchemas.Schema.Holds]
 | some expression =>
   rw [body_equation result,body_equation (compile.symm.trans result)]
   exact GeneralNominalRawCongruence238.equiv_iff
     (GeneralDictionaryDefaultExpression209.equivalent_refl _) (explicit_value first last assignment layout equation expression result same)
end Cycle262NormalizedProbe
#print axioms Cycle262NormalizedProbe.explicit_value
#print axioms Cycle262NormalizedProbe.explicit_body
