import Yulang.GeneralDeclarativeHeadDetermines320
import Yulang.GeneralDeclarativeCaptureClosure320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 4300000
namespace Yulang.GeneralDeclarativeCanonicalRead320
open CommonNominalFullCarrier (Ty Equivalent)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveInspection (Test shapeValue)
open GeneralNominalOriginTerms (arity)
open GeneralNominalFiniteMeaning (denote build)
open GeneralNominalReadbackFunctionality (Canonical)
open GeneralNominalCenteredHeadMatExpressions (Expr value values)
open GeneralDeclarativeWhere319 (Capture variables)
open GeneralDeclarativeHead320 (State Models values_ofFn)
open GeneralDeclarativeSubstitution320 (EquationRead equation_read)
open GeneralDeclarativeHeadDetermines320 (visible_capture pattern_congruent)
open GeneralNominalCenteredHeadMatPatternSemantics (Algebra eval eqv_trans eqv_symm)
open GeneralNominalStructuralReadback (recordValues)
open GeneralDeclarationPatterns (Pattern normalize)
open GeneralNominalMaterialization (Mode)

def fields : List (Nat × Expr) → Expr
  | [] => .primitive .emptyRecord []
  | first :: rest => .record first.1 first.2 (fields rest)

def embed : GeneralNominalOriginTerms.Expr Nat → Expr
  | .leaf name => .variable name
  | .node (.scalar b) _ => .primitive (.scalar b) []
  | .node (.structural .pair) kids => .primitive .pair [embed (kids ⟨0,by decide⟩),embed (kids ⟨1,by decide⟩)]
  | .node (.structural (.variant tag)) kids => .variant tag (embed (kids ⟨0,by change (0 : Nat) < 1; decide⟩))
  | .node (.structural .exactEmpty) _ => .primitive .exactEmpty []
  | .node (.structural (.record labels)) kids => fields (labels.zip (List.ofFn fun i => embed (kids i)))
  | .node (.nominal name _) kids => .nominal name (List.ofFn fun i => embed (kids i))

theorem field_values (env : Mode → Nat → Ty) (xs : List (Nat × Expr)) :
    value env .actual (fields xs) =
      recordValues (xs.map fun x => (x.1,value env .actual x.2)) := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [fields,List.map_cons,value,recordValues,List.foldr_cons,ih]

theorem embed_actual (term : GeneralNominalOriginTerms.Expr Nat) (env : Mode → Nat → Ty) :
    value env .actual (embed term) = denote (env .actual) term := by
  induction term with
  | leaf name => rfl
  | node test kids ih =>
    cases test with
    | scalar => rfl
    | nominal name count =>
      simp only [embed,value,values_ofFn,denote,build,List.map_ofFn,Function.comp_def,ih]
    | structural shape =>
      cases shape with
      | pair =>
        simp only [embed,value,values,GeneralNominalCenteredHeadMatExpressions.primitiveValue,denote,build,ih]
        rfl
      | variant tag =>
        simp only [embed,value,denote,build,ih]
        rfl
      | exactEmpty => rfl
      | record labels =>
        simp only [embed,field_values,denote,build]
        rw [GeneralNominalRecordInversion.record_shape _ _ (by simp [arity,GeneralNormalizedObservation.Shape.arity])]
        have zipped : (labels.zip (List.ofFn fun i => embed (kids i))).map
            (fun x => (x.1,value env .actual x.2)) =
              labels.zip (List.ofFn fun i => value env .actual (embed (kids i))) := by
          have rep := (List.zip_map_right
            (f := value env .actual) (l₁ := labels) (l₂ := List.ofFn fun i => embed (kids i))).symm
          rw [List.map_ofFn] at rep
          exact rep
        rw [zipped]
        simp only [ih]

/-- Actual reads of the same canonical constructor head force equivalent
captures on every visible binder, even if the two read plans used different
logical names. This extends direct head determination to ordinary readbacks. -/
theorem captures_agree {s : State} {m : Assignment} {first last : Nat → Capture}
    {root : Nat} {term : GeneralNominalOriginTerms.Expr Nat} (canonical : Canonical term)
    (a : EquationRead s first .actual root (embed term))
    (b : EquationRead s last .actual root (embed term))
    (valid : Models s m) :
    ∀ name ∈ term.leaves, Equivalent (variables first m .actual name) (variables last m .actual name) := by
  have same := eqv_trans (eqv_symm (equation_read a m valid)) (equation_read b m valid)
  rw [embed_actual,embed_actual] at same
  exact visible_capture term canonical _ _ same

theorem associated_agrees {s : State} {m : Assignment} {first last : Nat → Capture}
    {root : Nat} {term : GeneralNominalOriginTerms.Expr Nat} (canonical : Canonical term)
    (a : EquationRead s first .actual root (embed term))
    (b : EquationRead s last .actual root (embed term))
    (valid : Models s m) (algebra : Algebra) (rhs : Pattern)
    (scope : ∀ n ∈ (normalize rhs).variables, n ∈ term.leaves) :
    Equivalent (eval algebra (variables first m .actual) (normalize rhs))
      (eval algebra (variables last m .actual) (normalize rhs)) :=
  pattern_congruent algebra _ (fun name used => captures_agree canonical a b valid name (scope name used))

end Yulang.GeneralDeclarativeCanonicalRead320
