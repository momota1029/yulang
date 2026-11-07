import Yulang.CommonAlignedPatternInversion
import Yulang.CommonPatternGeneration

/-! Real finite structural generation with an explicit common upper bound
for every default computation row. This bound is an independent static factor;
it does not select the principal aggregate row of a full source case. -/

namespace Yulang.CommonPatternBoundedGeneration

set_option backward.isDefEq.respectTransparency false

open Core.PresenceGeneration
open CommonPatternEnvironment
open CommonPatternGeneration (renameBindings nilBindings evalTypes_rename evalTypes_take evalTypes_drop)
open CommonPatternBindingAlignment (reorder)
open CommonAlignedPatternTyping (RawTyping)
open CasePatterns (Pattern)

def DefaultTyping (outer : List (Binding Common.model)) (cap : Common.Row)
    (prior : NamedTypes) (code : Inference.Expr) (type : Common.Ty) : Prop :=
  ∃ row, Core.PresenceGeneration.Typing Common.model (semanticPrefix prior ++ outer) code (type, row) ∧
    Common.rowLe row cap

def generatePattern : Pattern Empty Inference.Expr → {α : Type} →
    RowTerm α → SchemeEnv α → NamedTerms α → TyTerm α → NamedTerms α → Formula α
  | .wildcard, _, _, _, _, _, bindings => nilBindings bindings .top
  | .bind name, _, _, _, _, input, bindings =>
      match bindings with
      | [(actual, type)] => if actual = name then .tyLe input type else .bot
      | _ => .bot
  | .literal expected, _, _, _, _, input, bindings =>
      nilBindings bindings (.tyLe input (.base (Core.CommonData.literalBase expected)))
  | .intRange lower upper, _, _, _, _, input, bindings =>
      nilBindings bindings (if lower.isSome || upper.isSome then .tyLe input (.base .int) else .bot)
  | .pair p q, _, cap, Γ, priorBindings, input, bindings =>
      let left := renameBindings (fun x => some (some x)) (bindings.take p.names.length)
      let right := renameBindings (fun x => some (some x)) (bindings.drop p.names.length)
      let prior := renameBindings (fun x => some (some x)) priorBindings
      .existsSlot (.existsSlot (
        .and (.tyLe (input.rename fun x => some (some x)) (.pair fresh₀.ty fresh₁.ty))
          (.and (generatePattern p (cap.rename fun x => some (some x)) (env₂ Γ) prior fresh₀.ty left)
            (generatePattern q (cap.rename fun x => some (some x)) (env₂ Γ) (left ++ prior) fresh₁.ty right))))
  | .recordEnd, _, _, _, _, input, bindings => nilBindings bindings (.tyLe input .emptyRecord)
  | .field name p rest, _, cap, Γ, priorBindings, input, bindings =>
      let left := renameBindings (fun x => some (some x)) (bindings.take p.names.length)
      let right := renameBindings (fun x => some (some x)) (bindings.drop p.names.length)
      let prior := renameBindings (fun x => some (some x)) priorBindings
      .existsSlot (.existsSlot (
        .and (.tyLe (input.rename fun x => some (some x)) fresh₀.ty)
          (.and (.tyLe fresh₀.ty (.required name fresh₁.ty))
            (.and (generatePattern p (cap.rename fun x => some (some x)) (env₂ Γ) prior fresh₁.ty left)
              (generatePattern rest (cap.rename fun x => some (some x)) (env₂ Γ) (left ++ prior) fresh₀.ty right)))))
  | .defaultField name fallback p rest, _, cap, Γ, priorBindings, input, bindings =>
      let left := renameBindings (fun x => some (some (some x))) (bindings.take p.names.length)
      let right := renameBindings (fun x => some (some (some x))) (bindings.drop p.names.length)
      let prior := renameBindings (fun x => some (some (some x))) priorBindings
      .existsSlot (.existsSlot (.existsSlot (
        .and (.tyLe (input.rename fun x => some (some (some x))) fresh₀₃.ty)
          (.and (CommonPatternDefaults.optionalConstraints name fresh₀₃.ty fresh₁₃.ty)
            (.and (.and (generate (symbolicPrefix prior ++ env₃ Γ) fallback fresh₂₃)
              (.rowLe fresh₂₃.row (cap.rename fun x => some (some (some x)))))
              (.and (generatePattern p (cap.rename fun x => some (some (some x))) (env₃ Γ) prior (.union fresh₁₃.ty fresh₂₃.ty) left)
                (generatePattern rest (cap.rename fun x => some (some (some x))) (env₃ Γ) (left ++ prior) fresh₀₃.ty right)))))))
  | .variant tag p, _, cap, Γ, priorBindings, input, bindings =>
      .existsSlot (.and (.tyLe (input.rename some) (.variant tag (.var none)))
        (generatePattern p (cap.rename some) Γ.lift (renameBindings some priorBindings) (.var none)
          (renameBindings some bindings)))
  | .or p q, _, cap, Γ, priorBindings, input, bindings =>
      .and (generatePattern p cap Γ priorBindings input bindings)
        (generatePattern q cap Γ priorBindings input (reorder q.names bindings))
  | .as p name, _, cap, Γ, priorBindings, input, bindings =>
      match bindings with
      | (actual, type) :: rest =>
          if actual = name then .and (.tyLe input type) (generatePattern p cap Γ priorBindings type rest)
          else .bot
      | [] => .bot
  | .nil, _, _, _, _, _, _ => .bot
  | .cons _ _, _, _, _, _, _, _ => .bot
  | .snoc _ _, _, _, _, _, _, _ => .bot
  | .nominal _ _ _, _, _, _, _, _, _ => .bot

theorem evalTypes_reorder (ρ : α → Comp Common.model) (names : List Nat) (bindings : NamedTerms α) :
    evalTypes ρ (reorder names bindings) = reorder names (evalTypes ρ bindings) :=
  (CommonPatternBindingAlignment.reorder_mapValues
    (fun type : TyTerm α => type.eval Common.model ρ) names bindings).symm

@[simp] theorem nilBindings_exact (bindings : NamedTerms α) (formula : Formula α)
    (ρ : α → Comp Common.model) :
    (nilBindings bindings formula).Holds Common.model ρ ↔
      evalTypes ρ bindings = [] ∧ formula.Holds Common.model ρ := by
  cases bindings <;> simp [nilBindings, Formula.Holds, evalTypes]

private theorem binding_split (ρ : α → Comp Common.model) (bindings : NamedTerms α)
    (typed : RawTyping defaults types p input left)
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
theorem generatePattern_exact (pattern : Pattern Empty Inference.Expr) (cap : RowTerm α)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (semantic : List (Binding Common.model))
    (outer : EnvRel Common.model ρ symbolic semantic)
    (priorBindings : NamedTerms α) (input : TyTerm α) (bindings : NamedTerms α) :
    (generatePattern pattern cap symbolic priorBindings input bindings).Holds Common.model ρ ↔
      RawTyping (DefaultTyping semantic (cap.eval Common.model ρ)) (evalTypes ρ priorBindings) pattern
        (input.eval Common.model ρ) (evalTypes ρ bindings) := by
  induction pattern generalizing α with
  | wildcard =>
      simp [generatePattern, Formula.Holds, CommonAlignedPatternInversion.wildcard_iff]
  | bind name =>
      cases bindings with
      | nil => simp [generatePattern, Formula.Holds, CommonAlignedPatternInversion.bind_iff, evalTypes]
      | cons binding rest =>
        rcases binding with ⟨actual, type⟩
        cases rest with
        | nil =>
          by_cases same : actual = name
          · subst actual
            simp [generatePattern, Formula.Holds, CommonAlignedPatternInversion.bind_iff, evalTypes,
              Common.model]
          · simp [generatePattern, same, Formula.Holds, CommonAlignedPatternInversion.bind_iff, evalTypes]
        | cons next tail =>
          simp [generatePattern, Formula.Holds, CommonAlignedPatternInversion.bind_iff, evalTypes]
  | literal expected =>
      rw [generatePattern, nilBindings_exact]
      simp only [Formula.Holds, TyTerm.eval,
        Common.model, CommonAlignedPatternInversion.literal_iff]
  | intRange lower upper =>
      simp only [generatePattern, nilBindings_exact, CommonAlignedPatternInversion.range_iff]
      cases lower <;> cases upper <;> simp [Formula.Holds, TyTerm.eval, Common.model]
  | recordEnd =>
      rw [generatePattern, nilBindings_exact]
      simp only [Formula.Holds, TyTerm.eval,
        Common.model, CommonAlignedPatternInversion.recordEnd_iff]
  | pair p q ihp ihq =>
      simp only [generatePattern, Formula.Holds]
      have exactChildren (a b : Comp Common.model) :=
        ihp (cap.rename fun x => some (some x)) (extend (extend ρ a) b) (env₂ symbolic) ((outer.lift a).lift b)
      have exactRest (a b : Comp Common.model) :=
        ihq (cap.rename fun x => some (some x)) (extend (extend ρ a) b) (env₂ symbolic) ((outer.lift a).lift b)
      simp only [exactChildren, exactRest, evalTypes_rename, evalTypes_append,
        Function.comp_def, extend_some, fresh₀, fresh₁, CompTerm.var,
        TyTerm.eval_rename, TyTerm.eval, RowTerm.eval_rename]
      rw [CommonAlignedPatternInversion.pair_iff]
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
        ihp (cap.rename fun x => some (some x)) (extend (extend ρ a) b) (env₂ symbolic) ((outer.lift a).lift b)
      have exactRest (a b : Comp Common.model) :=
        ihr (cap.rename fun x => some (some x)) (extend (extend ρ a) b) (env₂ symbolic) ((outer.lift a).lift b)
      simp only [exactChildren, exactRest, evalTypes_rename, evalTypes_append,
        Function.comp_def, extend_some, fresh₀, fresh₁, CompTerm.var,
        TyTerm.eval_rename, TyTerm.eval, RowTerm.eval_rename]
      rw [CommonAlignedPatternInversion.field_iff]
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
        ihp (cap.rename fun x => some (some (some x))) (extend (extend (extend ρ a) b) c) (env₃ symbolic)
          (((outer.lift a).lift b).lift c)
      have exactRest (a b c : Comp Common.model) :=
        ihr (cap.rename fun x => some (some (some x))) (extend (extend (extend ρ a) b) c) (env₃ symbolic)
          (((outer.lift a).lift b).lift c)
      have exactFallback (a b c : Comp Common.model) :=
        cumulative_default_generation_exact (extend (extend (extend ρ a) b) c)
          (renameBindings (fun x => some (some (some x))) priorBindings)
          (env₃ symbolic) semantic (((outer.lift a).lift b).lift c) fallback fresh₂₃
      simp only [exactChildren, exactRest,
        CommonPatternDefaults.optional_constraints_exact, evalTypes_rename, evalTypes_append,
        Function.comp_def, extend_some, fresh₀₃, fresh₁₃, fresh₂₃,
        CompTerm.var, TyTerm.eval_rename, TyTerm.eval, RowTerm.eval_rename]
      rw [CommonAlignedPatternInversion.defaultField_iff]
      constructor
      · rintro ⟨a, b, c, below, optional, ⟨fallbackTyped, withinCap⟩, first, last⟩
        have fallbackResult := (exactFallback a b c).mp fallbackTyped
        simp only [evalTypes_rename, Function.comp_def, extend_some, fresh₂₃, CompTerm.var,
          CompTerm.eval, TyTerm.eval, RowTerm.eval, extend_none] at fallbackResult
        refine ⟨a.1, b.1, c.1, _, _, ?_, below, optional, ⟨c.2, fallbackResult, withinCap⟩, first, last⟩
        simp [evalTypes_take, evalTypes_drop]
      · rintro ⟨a, b, c, left, right, same, below, optional, ⟨row, fallbackTyped, withinCap⟩, first, last⟩
        have parts := binding_split ρ bindings first same
        have fallbackResult := (exactFallback (a, Common.rowEmpty) (b, Common.rowEmpty) (c, row)).mpr
          (by simpa [evalTypes_rename, Function.comp_def, fresh₂₃, CompTerm.var,
            CompTerm.eval, TyTerm.eval, RowTerm.eval] using fallbackTyped)
        exact ⟨(a, Common.rowEmpty), (b, Common.rowEmpty), (c, row), below, optional,
          ⟨fallbackResult, withinCap⟩, by rw [parts.1]; exact first,
          by rw [parts.1, parts.2]; exact last⟩
  | variant tag p ih =>
      simp only [generatePattern, Formula.Holds]
      have child (a : Comp Common.model) := ih (cap.rename some) (extend ρ a) symbolic.lift (outer.lift a)
      simp only [child, evalTypes_rename, TyTerm.eval_rename, RowTerm.eval_rename, extend_comp_some, TyTerm.eval]
      rw [CommonAlignedPatternInversion.variant_iff]
      constructor
      · rintro ⟨a, below, typed⟩; exact ⟨a.1, below, typed⟩
      · rintro ⟨a, below, typed⟩; exact ⟨(a, Common.rowEmpty), below, typed⟩
  | or p q ihp ihq =>
      simp only [generatePattern, Formula.Holds, ihp cap ρ symbolic outer,
        ihq cap ρ symbolic outer, evalTypes_reorder, CommonAlignedPatternInversion.or_iff]
  | as p name ih =>
      cases bindings with
      | nil => simp [generatePattern, Formula.Holds, CommonAlignedPatternInversion.as_iff, evalTypes]
      | cons binding rest =>
        rcases binding with ⟨actual, type⟩
        by_cases same : actual = name
        · subst actual
          simp only [generatePattern, ↓reduceIte, Formula.Holds, ih cap ρ symbolic outer,
            CommonAlignedPatternInversion.as_iff, evalTypes, List.map_cons]
          constructor
          · rintro ⟨below, typed⟩; exact ⟨_, _, rfl, below, typed⟩
          · rintro ⟨original, more, same, below, typed⟩
            have equal := List.cons.inj same
            cases equal.1
            cases equal.2
            exact ⟨below, typed⟩
        · simp [generatePattern, same, Formula.Holds, CommonAlignedPatternInversion.as_iff, evalTypes]
  | nil | cons | snoc | nominal =>
      simp only [generatePattern, Formula.Holds]
      constructor
      · exact False.elim
      · intro typed
        obtain ⟨_, _, root⟩ := (CommonAlignedPatternInversion.typing_root_exact _ _ _ _ _).mp typed
        cases root

end Yulang.CommonPatternBoundedGeneration
