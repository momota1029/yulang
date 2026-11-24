import Yulang.GeneralDeclarativeI65B6MixedOutput401

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65

open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessConstructorModes357 (Environment Use)
open GeneralCandidateInspection (Primitive)
open GeneralSourceMetadataRows291 (interpretation)
open GeneralSourceMetadataBundle291 (registry)
open GeneralNominalCenteredHeadMatExpressions (application Expr primitiveValue)

mutual
def keepOriginalB6Plan401 {s c p} : B6ValuePlan398 s c p → B6MixedRhs401 s c p
  | .binder n => .binder n ()
  | .record label a b => .record label (keepOriginalB6Plan401 a) (keepOriginalB6Plan401 b)
  | .variant tag a => .variant tag (keepOriginalB6Plan401 a)
  | .join a b => .join (keepOriginalB6Plan401 a) (keepOriginalB6Plan401 b)
  | .declaredApp n use kinds exacts args => .declaredApp n use kinds exacts (keepOriginalB6Args401 args)

def keepOriginalB6Arg401 {s c param p} :
    B6ArgPlan398 s c param p → MixedArg401 s (fun _ _ => Unit) c param p
  | .valuePoint n k md => .valuePoint n k md ()
  | .valueInterval n k md => .valueInterval n k md ()
  | .rowPoint n k md => .rowPoint n k md ()
  | .rowInterval n k md => .rowInterval n k md ()
  | .valueTree k compound child => .valueTree k compound (keepOriginalB6Plan401 child)

def keepOriginalB6Args401 {s c params ps} :
    B6ArgPlans398 s c params ps → MixedArgs401 s (fun _ _ => Unit) c params ps
  | .nil => .nil
  | .cons a b => .cons (keepOriginalB6Arg401 a) (keepOriginalB6Args401 b)
end

/-- Conservativity for the earlier *typed plan*, not a conversion
to or from the retired C386 flat receipt. The richer carrier adds
no slot requirements and does not change any actual model value of
this pre-existing typed sublanguage. -/
theorem original_typed_plan_keeps_reads_and_values401 {s c p} (m : Model)
    (slots : Nat → Option Capture) (plan : B6ValuePlan398 s c p) :
    mixedRhsNeeds401 (keepOriginalB6Plan401 plan) = plan.needs ∧
    evaluateMixedRhs401 (sourceRead401 m slots) (keepOriginalB6Plan401 plan) =
      actualPlanValue400 m slots plan := by
  refine B6ValuePlan398.rec
    (motive_1 := fun _ _ t => mixedRhsNeeds401 (keepOriginalB6Plan401 t) = t.needs ∧
      evaluateMixedRhs401 (sourceRead401 m slots) (keepOriginalB6Plan401 t) = actualPlanValue400 m slots t)
    (motive_2 := fun _ _ _ t => mixedArgNeeds401 (keepOriginalB6Arg401 t) = t.needs ∧
      evaluateMixedArg401 (sourceRead401 m slots) (keepOriginalB6Arg401 t) = actualPlanArg400 m slots t)
    (motive_3 := fun _ _ _ t => mixedArgsNeeds401 (keepOriginalB6Args401 t) = t.needs ∧
      evaluateMixedArgs401 (sourceRead401 m slots) (keepOriginalB6Args401 t) = actualPlanArgs400 m slots t)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ plan
  · intro c n
    refine ⟨rfl,?_⟩
    change ((slots n).map (fun cap => m.assignment cap.center)).map Prod.fst =
      (slots n).map (fun cap => (m.assignment cap.center).1)
    cases slots n <;> rfl
  · intro c p q tag a b ha hb
    simp [keepOriginalB6Plan401,mixedRhsNeeds401,B6ValuePlan398.needs,ha.1,hb.1,
      evaluateMixedRhs401,actualPlanValue400,ha.2,hb.2]
  · intro c p tag a ha
    simp [keepOriginalB6Plan401,mixedRhsNeeds401,B6ValuePlan398.needs,ha.1,
      evaluateMixedRhs401,actualPlanValue400,ha.2]
  · intro c p q a b ha hb
    simp [keepOriginalB6Plan401,mixedRhsNeeds401,B6ValuePlan398.needs,ha.1,hb.1,
      evaluateMixedRhs401,actualPlanValue400,ha.2,hb.2]
  · intro ps c params n use has recorded a ha
    simp [keepOriginalB6Plan401,mixedRhsNeeds401,B6ValuePlan398.needs,ha.1,
      evaluateMixedRhs401,actualPlanValue400,ha.2]
  · intro ctx param n kind mode
    refine ⟨rfl,?_⟩
    change ((slots n).map (fun cap => m.assignment cap.center)).map (Sum.inl ∘ Prod.fst) =
      ((slots n).map (fun cap => (m.assignment cap.center).1)).map Sum.inl
    cases slots n <;> rfl
  · intro ctx param n kind mode
    refine ⟨rfl,?_⟩
    change ((slots n).map (fun cap => m.assignment cap.center)).map (Sum.inl ∘ Prod.fst) =
      ((slots n).map (fun cap => (m.assignment cap.center).1)).map Sum.inl
    cases slots n <;> rfl
  · intro ctx param n kind mode
    refine ⟨rfl,?_⟩
    change ((slots n).map (fun cap => m.assignment cap.center)).map (Sum.inr ∘ Prod.snd) =
      ((slots n).map (fun cap => (m.assignment cap.center).2)).map Sum.inr
    cases slots n <;> rfl
  · intro ctx param n kind mode
    refine ⟨rfl,?_⟩
    change ((slots n).map (fun cap => m.assignment cap.center)).map (Sum.inr ∘ Prod.snd) =
      ((slots n).map (fun cap => (m.assignment cap.center).2)).map Sum.inr
    cases slots n <;> rfl
  · intro param p ctx kind compound a ha
    simp [keepOriginalB6Arg401,mixedArgNeeds401,B6ArgPlan398.needs,ha.1,
      evaluateMixedArg401,actualPlanArg400,ha.2]
  · intros; exact ⟨rfl,rfl⟩
  · intro c first rest p ps a b ha hb
    simp [keepOriginalB6Args401,mixedArgsNeeds401,B6ArgPlans398.needs,ha.1,hb.1,
      evaluateMixedArgs401,actualPlanArgs400,ha.2,hb.2]

/-- The known authored primitive tag is also the one selected by the
existing application interpreter in its ordinary fragment. This is
layout and source metadata agreement, not decoding a solver result. -/
theorem exact_original_primitive_interpreter401 {e : Environment} {n : Nat}
    (args : List Expr) (use : Use e n args.length) (prim : Primitive)
    (actual : use.mode = .primitive prim) :
    application (registry e.source).constructors (interpretation e.source.snapshot) n args =
      some (.primitive prim args) := by
  obtain ⟨existsDecl,known,shape,arity⟩ := mixed_primitive_has_exact_authored_mode401 use prim actual
  simp [application,existsDecl,interpretation,known,shape,arity]

end Yulang.GeneralDeclarativeI65
