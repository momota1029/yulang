import Yulang.GeneralDictionaryDefault214ActualSupport
import Yulang.GeneralNominalCenteredHeadMatCompilerSemantics

/-! Semantic explicit-body support uses normalized names. Raw total expression
reads may contain shadowed fields; their evaluation is not replaced or weakened.
The existing compiler normalization theorem proves that those reads are inert. -/
namespace Yulang.GeneralDictionaryDefault214ActualBodyFrame
open GeneralDeclarations GeneralDeclarationPatterns GeneralNominalCenters
open GeneralNominalCenteredHeadMatPatternSemantics
open GeneralNominalCenteredHeadMatEffects
open GeneralNominalCenteredFrame179 (Agree)
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
variable {roles : Roles.RoleDecls} {first last : Assignment}

mutual
 theorem eval_same (algebra : Algebra) (pattern : Pattern)
     (same : ∀ name ∈ pattern.variables, one name = two name) :
     eval algebra one pattern = eval algebra two pattern := by
   cases pattern with
   | var name => exact same name (List.mem_singleton_self _)
   | app name arguments => exact congrArg (algebra.application name) (evals_same algebra arguments same)
   | record label payload tail =>
       simp only [eval]
       rw [eval_same algebra payload (fun n h => same n (List.mem_append_left _ h)),
         eval_same algebra tail (fun n h => same n (List.mem_append_right _ h))]
   | variant tag payload => exact congrArg (variant tag) (eval_same algebra payload same)
   | join a b =>
       simp only [eval]
       rw [eval_same algebra a (fun n h => same n (List.mem_append_left _ h)),
         eval_same algebra b (fun n h => same n (List.mem_append_right _ h))]
 theorem evals_same (algebra : Algebra) (patterns : List Pattern)
     (same : ∀ name ∈ variablesArgs patterns, one name = two name) :
     evals algebra one patterns = evals algebra two patterns := by
   cases patterns with
   | nil => rfl
   | cons head tail =>
       simp only [evals]
       rw [eval_same algebra head (fun n h => same n (List.mem_append_left _ h)),
         evals_same algebra tail (fun n h => same n (List.mem_append_right _ h))]
end

 def bodySources (plan : Plan roles) (target : Nat) : Body → List Nat
   | .explicit equation => target :: (normalize equation.rhs).variables.map plan.binder
   | body@(.default _ _ _) => GeneralDictionaryDefaultModeEffects213.bodySources plan target body

 theorem explicit_value_same (plan : Plan roles) (equation : GeneralDeclarations.Equation)
     (compiled : compileBody plan (.explicit equation) = some expression)
     (same : Agree ((normalize equation.rhs).variables.map plan.binder) first last) :
     Equivalent (GeneralNominalCenteredHeadMatExpressions.value (variables plan first) .actual expression)
       (GeneralNominalCenteredHeadMatExpressions.value (variables plan last) .actual expression) := by
   have one := GeneralNominalCenteredHeadMatCompilerSemantics.compiled_normalized
     (variables := variables plan first) compiled
   have two := GeneralNominalCenteredHeadMatCompilerSemantics.compiled_normalized
     (variables := variables plan last) compiled
   have equal : eval (GeneralNominalCenteredHeadMatCompilerSemantics.algebra plan.packet.registry.constructors
       plan.packet.context.interpretation) (variables plan first .actual) (normalize equation.rhs) =
       eval (GeneralNominalCenteredHeadMatCompilerSemantics.algebra plan.packet.registry.constructors
       plan.packet.context.interpretation) (variables plan last .actual) (normalize equation.rhs) := by
     apply eval_same
     intro name member
     rw [actual_variable,actual_variable,same _ (List.mem_map.mpr ⟨name,member,rfl⟩)]
   rw [equal] at one
   exact eqv_trans one (eqv_symm two)

 theorem body_iff (plan : Plan roles) (target : Nat) (body : Body)
     (same : Agree (bodySources plan target body) first last) :
     BodyHolds plan target first body ↔ BodyHolds plan target last body := by
   cases body with
   | default role name term => exact GeneralDictionaryDefaultModeEffects213.body_iff plan target _ same
   | explicit equation =>
       cases compiled : compileBody plan (.explicit equation) with
       | none => simp [BodyHolds,bodySchema,compiled,GeneralNominalCenteredHeadMatSchemas.Schema.Holds]
       | some expression =>
           rw [body_equation compiled,body_equation compiled]
           have targetEq := congrArg Prod.fst (same target (List.mem_cons_self ..))
           have valueEq := explicit_value_same plan equation compiled (fun name member => same name (List.mem_cons_of_mem _ member))
           change Equivalent (first target).1 _ ↔ Equivalent (last target).1 _
           rw [targetEq]
           exact ⟨fun valid => eqv_trans valid valueEq,fun valid => eqv_trans valid (eqv_symm valueEq)⟩

 noncomputable def classSources (state : GeneralNominalCenteredSteps.State roles)
     (focus : GeneralSourceDictionaries.Occurrence roles) (plan : Plan roles) : List Nat :=
   (GeneralNominalCenteredHeadOutputs.requests state focus).flatMap fun output =>
     output.target :: ((GeneralDictionaryAssociatedProvenance.lookup roles plan.packet.declaration output.name).toList.flatMap
       fun body => bodySources plan output.target body)

 theorem class_iff (state : GeneralNominalCenteredSteps.State roles)
     (focus : GeneralSourceDictionaries.Occurrence roles) (plan : Plan roles)
     (same : Agree (classSources state focus plan) first last) :
     ClassEffects state focus plan first ↔ ClassEffects state focus plan last := by
   have target output (member : output ∈ GeneralNominalCenteredHeadOutputs.requests state focus) :
       first output.target = last output.target :=
     same _ (List.mem_flatMap.mpr ⟨output,member,List.mem_cons_self ..⟩)
   unfold ClassEffects
   apply and_congr
   · apply forall_congr'; intro output
     apply forall_congr'; intro member
     apply forall_congr'; intro body
     apply forall_congr'; intro found
     apply body_iff
     intro name present
     apply same
     apply List.mem_flatMap.mpr
     refine ⟨output,member,List.mem_cons_of_mem _ ?_⟩
     exact List.mem_flatMap.mpr ⟨body,Option.mem_toList.mpr found,present⟩
   · unfold GeneralNominalCenteredHeadOutputs.EqualOutputs
     apply forall_congr'; intro a
     apply forall_congr'; intro aMember
     apply forall_congr'; intro b
     apply forall_congr'; intro bMember
     rw [target a aMember,target b bMember]

end Yulang.GeneralDictionaryDefault214ActualBodyFrame
