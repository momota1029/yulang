import Yulang.CommonPatternInversion
import Yulang.CommonPatternDefaults

/-!
# Finite constraints for shared structural-pattern binding references

The binding terms are shared references, not independent copies at each use.
The recursive traversal splits them in written order and adds only the preceding
part to the Q4 priorBindings. The original captured environment is retained separately.
No semantic typing predicate is added to the finite formula language.

This module targets the existing intermediate CommonPatternTyping judgment;
it does not silently extend its list/nominal/presence/coverage boundaries.
-/

namespace Yulang.CommonPatternGeneration

set_option backward.isDefEq.respectTransparency false

open Core.PresenceGeneration
open CommonPatternEnvironment
open CasePatterns (Pattern)
open CommonPatternTyping (Typing)

def renameBindings (f : α → β) (bindings : NamedTerms α) : NamedTerms β :=
  bindings.map fun binding => (binding.1, binding.2.rename f)

@[simp] theorem evalTypes_rename (f : α → β) (ρ : β → Comp Common.model)
    (bindings : NamedTerms α) :
    evalTypes ρ (renameBindings f bindings) = evalTypes (ρ ∘ f) bindings := by
  simp [evalTypes, renameBindings, List.map_map]

@[simp] theorem evalTypes_take (ρ : α → Comp Common.model) (n : Nat)
    (bindings : NamedTerms α) :
    evalTypes ρ (bindings.take n) = (evalTypes ρ bindings).take n := by
  simp [evalTypes, List.map_take]

@[simp] theorem evalTypes_drop (ρ : α → Comp Common.model) (n : Nat)
    (bindings : NamedTerms α) :
    evalTypes ρ (bindings.drop n) = (evalTypes ρ bindings).drop n := by
  simp [evalTypes, List.map_drop]

/-- All fallback computation rows are existential here. Their contribution to
the whole case row is a separate B3 integration obligation. -/
def DefaultTyping (outer : List (Binding Common.model))
    (priorBindings : NamedTypes) (code : Inference.Expr) (type : Common.Ty) : Prop :=
  ∃ row, Core.PresenceGeneration.Typing Common.model (semanticPrefix priorBindings ++ outer)
    code (type, row)

def nilBindings (bindings : NamedTerms α) (constraints : Formula α) : Formula α :=
  match bindings with
  | [] => constraints
  | _ :: _ => .bot

/-- Internal decomposition slots are fresh, while both or branches consume the
same external binding references. Even syntactic values remain monomorphic. -/
def generatePattern : Pattern Empty Inference.Expr → {α : Type} →
    SchemeEnv α → NamedTerms α → TyTerm α → NamedTerms α → Formula α
  | .wildcard, _, _, _, _, bindings => nilBindings bindings .top
  | .bind name, _, _, _, input, bindings =>
      match bindings with
      | [(actual, type)] => if actual = name then .tyLe input type else .bot
      | _ => .bot
  | .literal expected, _, _, _, input, bindings =>
      nilBindings bindings (.tyLe input (.base (Core.CommonData.literalBase expected)))
  | .intRange lower upper, _, _, _, input, bindings =>
      nilBindings bindings (if lower.isSome || upper.isSome then .tyLe input (.base .int) else .bot)
  | .pair p q, _, Γ, priorBindings, input, bindings =>
      let left := renameBindings (fun x => some (some x)) (bindings.take p.names.length)
      let right := renameBindings (fun x => some (some x)) (bindings.drop p.names.length)
      let prior := renameBindings (fun x => some (some x)) priorBindings
      .existsSlot (.existsSlot (
        .and (.tyLe (input.rename fun x => some (some x)) (.pair fresh₀.ty fresh₁.ty))
          (.and (generatePattern p (env₂ Γ) prior fresh₀.ty left)
            (generatePattern q (env₂ Γ) (left ++ prior) fresh₁.ty right))))
  | .recordEnd, _, _, _, input, bindings => nilBindings bindings (.tyLe input .emptyRecord)
  | .field name p rest, _, Γ, priorBindings, input, bindings =>
      let left := renameBindings (fun x => some (some x)) (bindings.take p.names.length)
      let right := renameBindings (fun x => some (some x)) (bindings.drop p.names.length)
      let prior := renameBindings (fun x => some (some x)) priorBindings
      .existsSlot (.existsSlot (
        .and (.tyLe (input.rename fun x => some (some x)) fresh₀.ty)
          (.and (.tyLe fresh₀.ty (.required name fresh₁.ty))
            (.and (generatePattern p (env₂ Γ) prior fresh₁.ty left)
              (generatePattern rest (env₂ Γ) (left ++ prior) fresh₀.ty right)))))
  | .defaultField name fallback p rest, _, Γ, priorBindings, input, bindings =>
      let left := renameBindings (fun x => some (some (some x))) (bindings.take p.names.length)
      let right := renameBindings (fun x => some (some (some x))) (bindings.drop p.names.length)
      let prior := renameBindings (fun x => some (some (some x))) priorBindings
      .existsSlot (.existsSlot (.existsSlot (
        .and (.tyLe (input.rename fun x => some (some (some x))) fresh₀₃.ty)
          (.and (CommonPatternDefaults.optionalConstraints name fresh₀₃.ty fresh₁₃.ty)
            (.and (generate (symbolicPrefix prior ++ env₃ Γ) fallback fresh₂₃)
              (.and (generatePattern p (env₃ Γ) prior (.union fresh₁₃.ty fresh₂₃.ty) left)
                (generatePattern rest (env₃ Γ) (left ++ prior) fresh₀₃.ty right)))))))
  | .variant tag p, _, Γ, priorBindings, input, bindings =>
      .existsSlot (.and (.tyLe (input.rename some) (.variant tag (.var none)))
        (generatePattern p Γ.lift (renameBindings some priorBindings) (.var none)
          (renameBindings some bindings)))
  | .or p q, _, Γ, priorBindings, input, bindings =>
      .and (generatePattern p Γ priorBindings input bindings) (generatePattern q Γ priorBindings input bindings)
  | .as p name, _, Γ, priorBindings, input, bindings =>
      match bindings with
      | (actual, type) :: rest =>
          if actual = name then .and (.tyLe input type) (generatePattern p Γ priorBindings type rest)
          else .bot
      | [] => .bot
  | .nil, _, _, _, _, _ => .bot
  | .cons _ _, _, _, _, _, _ => .bot
  | .snoc _ _, _, _, _, _, _ => .bot
  | .nominal _ _ _, _, _, _, _, _ => .bot

@[simp] theorem nilBindings_exact (bindings : NamedTerms α) (formula : Formula α)
    (ρ : α → Comp Common.model) :
    (nilBindings bindings formula).Holds Common.model ρ ↔
      evalTypes ρ bindings = [] ∧ formula.Holds Common.model ρ := by
  cases bindings <;> simp [nilBindings, Formula.Holds, evalTypes]

private theorem binding_split (ρ : α → Comp Common.model) (bindings : NamedTerms α)
    (typed : Typing defaults types p input left)
    (same : evalTypes ρ bindings = left ++ right) :
    evalTypes ρ (bindings.take p.names.length) = left ∧
      evalTypes ρ (bindings.drop p.names.length) = right := by
  have length : p.names.length = left.length := by
    simpa using congrArg List.length typed.binding_names
  simp [evalTypes_take, evalTypes_drop, same, length]

/-- Exact generation for the existing independent structural judgment. The
captured outer environment and every slot assignment are unrestricted apart
from the standard environment interpretation relation. List/nominal cases
are rejected on both sides because that judgment has no such rules. -/
theorem generatePattern_exact (pattern : Pattern Empty Inference.Expr)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (semantic : List (Binding Common.model))
    (outer : EnvRel Common.model ρ symbolic semantic)
    (priorBindings : NamedTerms α) (input : TyTerm α) (bindings : NamedTerms α) :
    (generatePattern pattern symbolic priorBindings input bindings).Holds Common.model ρ ↔
      Typing (DefaultTyping semantic) (evalTypes ρ priorBindings) pattern
        (input.eval Common.model ρ) (evalTypes ρ bindings) := by
  induction pattern generalizing α with
  | wildcard =>
      simp [generatePattern, Formula.Holds, CommonPatternInversion.wildcard_iff]
  | bind name =>
      cases bindings with
      | nil => simp [generatePattern, Formula.Holds, CommonPatternInversion.bind_iff, evalTypes]
      | cons binding rest =>
        rcases binding with ⟨actual, type⟩
        cases rest with
        | nil =>
          by_cases same : actual = name
          · subst actual
            simp [generatePattern, Formula.Holds, CommonPatternInversion.bind_iff, evalTypes,
              Common.model]
          · simp [generatePattern, same, Formula.Holds, CommonPatternInversion.bind_iff, evalTypes]
        | cons next tail =>
          simp [generatePattern, Formula.Holds, CommonPatternInversion.bind_iff, evalTypes]
  | literal expected =>
      rw [generatePattern, nilBindings_exact]
      simp only [Formula.Holds, TyTerm.eval,
        Common.model, CommonPatternInversion.literal_iff]
  | intRange lower upper =>
      simp only [generatePattern, nilBindings_exact, CommonPatternInversion.range_iff]
      cases lower <;> cases upper <;> simp [Formula.Holds, TyTerm.eval, Common.model]
  | recordEnd =>
      rw [generatePattern, nilBindings_exact]
      simp only [Formula.Holds, TyTerm.eval,
        Common.model, CommonPatternInversion.recordEnd_iff]
  | pair p q ihp ihq =>
      simp only [generatePattern, Formula.Holds]
      have exactChildren (a b : Comp Common.model) :=
        ihp (extend (extend ρ a) b) (env₂ symbolic) ((outer.lift a).lift b)
      have exactRest (a b : Comp Common.model) :=
        ihq (extend (extend ρ a) b) (env₂ symbolic) ((outer.lift a).lift b)
      simp only [exactChildren, exactRest, evalTypes_rename, evalTypes_append,
        Function.comp_def, extend_some, fresh₀, fresh₁, CompTerm.var,
        TyTerm.eval_rename, TyTerm.eval]
      rw [CommonPatternInversion.pair_iff]
      constructor
      · rintro ⟨a, b, below, first, last⟩
        refine ⟨a.1, b.1, _, _, ?_, below, first, last⟩
        simp [evalTypes_take, evalTypes_drop]
      · rintro ⟨a, b, left, right, same, below, first, last⟩
        have parts := binding_split ρ bindings first same
        exact ⟨(a, Common.rowEmpty), (b, Common.rowEmpty), below,
          by simpa [parts.1] using first, by simpa [parts.1, parts.2] using last⟩
  | field name p rest ihp ihr =>
      simp only [generatePattern, Formula.Holds]
      have exactChildren (a b : Comp Common.model) :=
        ihp (extend (extend ρ a) b) (env₂ symbolic) ((outer.lift a).lift b)
      have exactRest (a b : Comp Common.model) :=
        ihr (extend (extend ρ a) b) (env₂ symbolic) ((outer.lift a).lift b)
      simp only [exactChildren, exactRest, evalTypes_rename, evalTypes_append,
        Function.comp_def, extend_some, fresh₀, fresh₁, CompTerm.var,
        TyTerm.eval_rename, TyTerm.eval]
      rw [CommonPatternInversion.field_iff]
      constructor
      · rintro ⟨a, b, below, required, first, last⟩
        refine ⟨a.1, b.1, _, _, ?_, below, required, first, last⟩
        simp [evalTypes_take, evalTypes_drop]
      · rintro ⟨a, b, left, right, same, below, required, first, last⟩
        have parts := binding_split ρ bindings first same
        exact ⟨(a, Common.rowEmpty), (b, Common.rowEmpty), below, required,
          by simpa [parts.1] using first, by simpa [parts.1, parts.2] using last⟩
  | defaultField name fallback p rest ihp ihr =>
      simp only [generatePattern, Formula.Holds]
      have exactChildren (a b c : Comp Common.model) :=
        ihp (extend (extend (extend ρ a) b) c) (env₃ symbolic)
          (((outer.lift a).lift b).lift c)
      have exactRest (a b c : Comp Common.model) :=
        ihr (extend (extend (extend ρ a) b) c) (env₃ symbolic)
          (((outer.lift a).lift b).lift c)
      have exactFallback (a b c : Comp Common.model) :=
        cumulative_default_generation_exact (extend (extend (extend ρ a) b) c)
          (renameBindings (fun x => some (some (some x))) priorBindings)
          (env₃ symbolic) semantic (((outer.lift a).lift b).lift c) fallback fresh₂₃
      simp only [exactChildren, exactRest,
        CommonPatternDefaults.optional_constraints_exact, evalTypes_rename, evalTypes_append,
        Function.comp_def, extend_some, fresh₀₃, fresh₁₃, fresh₂₃,
        CompTerm.var, TyTerm.eval_rename, TyTerm.eval]
      rw [CommonPatternInversion.defaultField_iff]
      constructor
      · rintro ⟨a, b, c, below, optional, fallbackTyped, first, last⟩
        have fallbackResult := (exactFallback a b c).mp fallbackTyped
        simp only [evalTypes_rename, Function.comp_def, extend_some, fresh₂₃, CompTerm.var,
          CompTerm.eval, TyTerm.eval, RowTerm.eval, extend_none] at fallbackResult
        refine ⟨a.1, b.1, c.1, _, _, ?_, below, optional, ⟨c.2, fallbackResult⟩, first, last⟩
        simp [evalTypes_take, evalTypes_drop]
      · rintro ⟨a, b, c, left, right, same, below, optional, ⟨row, fallbackTyped⟩, first, last⟩
        have parts := binding_split ρ bindings first same
        have fallbackResult := (exactFallback (a, Common.rowEmpty) (b, Common.rowEmpty) (c, row)).mpr
          (by simpa [evalTypes_rename, Function.comp_def, fresh₂₃, CompTerm.var,
            CompTerm.eval, TyTerm.eval, RowTerm.eval] using fallbackTyped)
        exact ⟨(a, Common.rowEmpty), (b, Common.rowEmpty), (c, row), below, optional,
          fallbackResult, by rw [parts.1]; exact first,
          by rw [parts.1, parts.2]; exact last⟩
  | variant tag p ih =>
      simp only [generatePattern, Formula.Holds]
      have child (a : Comp Common.model) := ih (extend ρ a) symbolic.lift (outer.lift a)
      simp only [child, evalTypes_rename, TyTerm.eval_rename, extend_comp_some, TyTerm.eval]
      rw [CommonPatternInversion.variant_iff]
      constructor
      · rintro ⟨a, below, typed⟩; exact ⟨a.1, below, typed⟩
      · rintro ⟨a, below, typed⟩; exact ⟨(a, Common.rowEmpty), below, typed⟩
  | or p q ihp ihq =>
      simp only [generatePattern, Formula.Holds, ihp ρ symbolic outer,
        ihq ρ symbolic outer, CommonPatternInversion.or_iff]
  | as p name ih =>
      cases bindings with
      | nil => simp [generatePattern, Formula.Holds, CommonPatternInversion.as_iff, evalTypes]
      | cons binding rest =>
        rcases binding with ⟨actual, type⟩
        by_cases same : actual = name
        · subst actual
          simp only [generatePattern, ↓reduceIte, Formula.Holds, ih ρ symbolic outer,
            CommonPatternInversion.as_iff, evalTypes, List.map_cons]
          constructor
          · rintro ⟨below, typed⟩; exact ⟨_, _, rfl, below, typed⟩
          · rintro ⟨original, more, same, below, typed⟩
            have equal := List.cons.inj same
            cases equal.1
            cases equal.2
            exact ⟨below, typed⟩
        · simp [generatePattern, same, Formula.Holds, CommonPatternInversion.as_iff, evalTypes]
  | nil | cons | snoc | nominal =>
      simp only [generatePattern, Formula.Holds]
      constructor
      · exact False.elim
      · intro typed
        obtain ⟨_, _, root⟩ := (CommonPatternInversion.typing_root_exact _ _ _ _ _).mp typed
        cases root

end Yulang.CommonPatternGeneration
