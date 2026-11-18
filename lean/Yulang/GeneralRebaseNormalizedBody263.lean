import Yulang.GeneralRebasePlanSemantic262
import Yulang.GeneralNominalCenteredHeadMatSemanticSubstitution

namespace Yulang.GeneralRebaseNormalizedBody263
open GeneralNominalCenters GeneralDeclarationPatterns
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

/-- Only normalized explicit-RHS support is compared. Shadowed raw expression
names need not occur here. Defaults still use positional center meanings. -/
structure Compatible (first last : Plan roles) (assignment : Assignment) : Prop where
 layout : GeneralRebasePlanSemantic262.Layout first last
 explicit : ∀ equation ∈ first.packet.declaration.associated,
   ∀ name ∈ (normalize equation.rhs).variables,
   Equivalent (assignment (first.binder name)).1 (assignment (last.binder name)).1
 centers : ∀ index : Nat, Equivalent
   (assignment ((List.ofFn first.input.center)[index]?.getD 0)).1
   (assignment ((List.ofFn last.input.center)[index]?.getD 0)).1

theorem default_body (first last : Plan roles) (assignment : Assignment)
 (layout : GeneralRebasePlanSemantic262.Layout first last)
 (centers : ∀ index : Nat, Equivalent
   (assignment ((List.ofFn first.input.center)[index]?.getD 0)).1
   (assignment ((List.ofFn last.input.center)[index]?.getD 0)).1)
 (role name target : Nat) (term : Roles.Term) :
 GeneralNominalVersionedEffects231.BodyHolds first target assignment (.default role name term) ↔
 GeneralNominalVersionedEffects231.BodyHolds last target assignment (.default role name term) := by
 unfold GeneralNominalVersionedEffects231.BodyHolds bodySchema
 rw [← GeneralRebasePlanSemantic262.compile_eq first last layout (.default role name term)]
 cases compiled : compileBody first (.default role name term) with
 | none => simp [GeneralNominalCenteredHeadMatSchemas.Schema.Holds]
 | some expression =>
   simp only [GeneralNominalCenteredHeadMatSchemas.Schema.Holds,List.mem_singleton,forall_eq]
   unfold GeneralNominalCenteredHeadMatSchemas.Equation.Holds
   exact GeneralNominalRawCongruence238.equiv_iff
     (GeneralDictionaryDefaultExpression209.equivalent_refl _)
     (GeneralRebasePlanSemantic262.actual_value _ _ centers expression)

theorem supplied_body (first last : Plan roles) (assignment : Assignment)
 (compatible : Compatible first last assignment) (name target : Nat)
 (body : GeneralDictionaryAssociatedProvenance.Body)
 (supplied : GeneralDictionaryAssociatedProvenance.Supplies roles first.packet.declaration name body) :
 GeneralNominalVersionedEffects231.BodyHolds first target assignment body ↔
 GeneralNominalVersionedEffects231.BodyHolds last target assignment body := by
 cases supplied with
 | explicit equation present _ =>
   exact explicit_body first last assignment compatible.layout equation target (compatible.explicit equation present)
 | default rhs _ _ =>
   exact default_body first last assignment compatible.layout compatible.centers _ _ target rhs

theorem lookup_body (first last : Plan roles) (assignment : Assignment)
 (compatible : Compatible first last assignment) (name target : Nat)
 (body : GeneralDictionaryAssociatedProvenance.Body)
 (found : GeneralDictionaryAssociatedProvenance.lookup roles first.packet.declaration name = some body) :
 GeneralNominalVersionedEffects231.BodyHolds first target assignment body ↔
 GeneralNominalVersionedEffects231.BodyHolds last target assignment body :=
 supplied_body first last assignment compatible name target body
   ((GeneralDictionaryAssociatedProvenance.lookup_exact roles first.packet.declaration
     first.packet.checked.identified.2.2.1 name body).mp found)

theorem effects (first last : Plan roles) (assignment : Assignment)
 (compatible : Compatible first last assignment) (outputs : List GeneralSourceState.Output) :
 GeneralRebaseClassTable261.Effects first outputs assignment ↔
 GeneralRebaseClassTable261.Effects last outputs assignment := by
 constructor
 · rintro ⟨bodies,pairs⟩
   refine ⟨?_,pairs⟩
   intro output member body found
   have original : GeneralDictionaryAssociatedProvenance.lookup roles first.packet.declaration output.name = some body := by
     rw [compatible.layout.declaration]; exact found
   exact (lookup_body first last assignment compatible output.name output.target body original).mp
     (bodies output member body original)
 · rintro ⟨bodies,pairs⟩
   refine ⟨?_,pairs⟩
   intro output member body found
   have other : GeneralDictionaryAssociatedProvenance.lookup roles last.packet.declaration output.name = some body := by
     rw [← compatible.layout.declaration]; exact found
   exact (lookup_body first last assignment compatible output.name output.target body found).mpr
     (bodies output member body other)

theorem class_effects (first last : Plan roles) (assignment : Assignment)
 (compatible : Compatible first last assignment)
 (source : GeneralNominalCenteredSteps.State roles) (root : GeneralSourceDictionaries.Occurrence roles) :
 GeneralNominalVersionedEffects231.ClassEffects source root first assignment ↔
 GeneralNominalVersionedEffects231.ClassEffects source root last assignment := effects first last assignment compatible _
end Yulang.GeneralRebaseNormalizedBody263
