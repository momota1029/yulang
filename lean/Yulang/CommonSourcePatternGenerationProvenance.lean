import Yulang.CommonSourcePatternAllocation
import Yulang.CommonPatternGenerationProvenance

/-!
# Source structural patterns with optional-input field matching

T2 / X22, spec/03b-patterns.md §3b.3: a field without a default
requires presence only on success; absent fields miss. This additive
successor to CommonAlignedPatternGenerationProvenance changes that rule recursively,
including nested fields, and preserves Q4 scopes and source-name alignment.
The old judgment, generator and strict rejection theorems remain unchanged.
Lists/nominals and the public Core.infer integration remain outside this
structural fragment; this module does not claim full B2 completion.
-/

namespace Yulang.CommonSourcePatternGenerationProvenance

open Core.PresenceGeneration
open CommonPatternEnvironment
open CommonPatternGeneration (renameBindings nilBindings)
open CommonPatternAllocation (Slots close bindingSlots)
open CommonSourcePatternGeneration (generatePattern)
open CommonSourcePatternAllocation (constraints generateAllocatedPattern generateCheckedPattern)
open CommonPatternGenerationProvenance
open CommonPatternBindingAlignment (reorder)
open CasePatterns (Pattern)

theorem bindings_reorder {bindings : NamedTerms α} (good : GoodBindings bindings) (names : List Nat) :
    GoodBindings (reorder names bindings) :=
  fun binding member => good binding (CommonPatternBindingAlignment.reorder_mem names bindings member)

theorem safe_generatePattern (pattern : Pattern Empty Inference.Expr)
    (environment : SchemeEnv α) (environmentGood : SafeEnvironment environment)
    (priorBindings : NamedTerms α) (priorGood : GoodBindings priorBindings)
    (input : TyTerm α) (inputGood : Input input)
    (bindings : NamedTerms α) (bindingsGood : GoodBindings bindings) :
    SafeFormula (generatePattern pattern environment priorBindings input bindings) := by
  induction pattern generalizing α with
  | wildcard => exact safe_nilBindings bindings .top
  | bind name =>
      cases bindings with
      | nil => exact .bot
      | cons binding rest =>
          rcases binding with ⟨actual, type⟩
          cases rest with
          | nil =>
              simp only [generatePattern]
              split
              · have good := bindingsGood (actual, type) List.mem_cons_self
                exact safe_tyLe input type inputGood (.old good.upper) good.rows
              · exact .bot
          | cons => exact .bot
  | literal expected =>
      exact safe_nilBindings bindings (safe_tyLe input _ inputGood (.old rfl) rfl)
  | intRange lower upper =>
      simp only [generatePattern]
      apply safe_nilBindings
      split
      · exact safe_tyLe input _ inputGood (.old rfl) rfl
      · exact .bot
  | recordEnd => exact safe_nilBindings bindings (safe_tyLe input _ inputGood (.old rfl) rfl)
  | pair p q ihp ihq =>
      let rename : α → Option (Option α) := fun x => some (some x)
      have left := bindings_rename (bindings_take bindingsGood p.names.length) rename
      have right := bindings_rename (bindings_drop bindingsGood p.names.length) rename
      have prior := bindings_rename priorGood rename
      exact .existsSlot (.existsSlot (.and
        (safe_tyLe _ _ (inputGood.rename rename) (.old rfl) rfl)
        (.and (ihp _ environmentGood.lift.lift _ prior _ ⟨rfl, rfl, rfl⟩ _ left)
          (ihq _ environmentGood.lift.lift _ (bindings_append left prior) _ ⟨rfl, rfl, rfl⟩ _ right))))
  | field name p rest ihp ihr =>
      let rename : α → Option (Option α) := fun x => some (some x)
      have left := bindings_rename (bindings_take bindingsGood p.names.length) rename
      have right := bindings_rename (bindings_drop bindingsGood p.names.length) rename
      have prior := bindings_rename priorGood rename
      exact .existsSlot (.existsSlot (.and
        (safe_tyLe _ _ (inputGood.rename rename) (.old rfl) rfl)
        (.and (safe_optional name fresh₀.ty fresh₁.ty ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl⟩)
          (.and (ihp _ environmentGood.lift.lift _ prior _ ⟨rfl, rfl, rfl⟩ _ left)
            (ihr _ environmentGood.lift.lift _ (bindings_append left prior) _ ⟨rfl, rfl, rfl⟩ _ right)))))
  | defaultField name fallback p rest ihp ihr =>
      let rename : α → Option (Option (Option α)) := fun x => some (some (some x))
      have left := bindings_rename (bindings_take bindingsGood p.names.length) rename
      have right := bindings_rename (bindings_drop bindingsGood p.names.length) rename
      have prior := bindings_rename priorGood rename
      have fallbackGood := safe_generate _
        (with_bindings environmentGood.lift.lift.lift _ prior) fallback fresh₂₃ ⟨rfl, rfl⟩ rfl
      exact .existsSlot (.existsSlot (.existsSlot (.and
        (safe_tyLe _ _ (inputGood.rename rename) (.old rfl) rfl)
        (.and (safe_optional name fresh₀₃.ty fresh₁₃.ty ⟨rfl, rfl, rfl⟩ ⟨rfl, rfl⟩)
          (.and fallbackGood
            (.and (ihp _ environmentGood.lift.lift.lift _ prior _ ⟨rfl, rfl, rfl⟩ _ left)
              (ihr _ environmentGood.lift.lift.lift _ (bindings_append left prior) _ ⟨rfl, rfl, rfl⟩ _ right)))))))
  | variant tag p ih =>
      exact .existsSlot (.and (safe_tyLe _ _ (inputGood.rename some) (.variant rfl) rfl)
        (ih _ environmentGood.lift _ (bindings_rename priorGood some) _ ⟨rfl, rfl, rfl⟩ _
          (bindings_rename bindingsGood some)))
  | or p q ihp ihq =>
      exact .and (ihp _ environmentGood _ priorGood input inputGood bindings bindingsGood)
        (ihq _ environmentGood _ priorGood input inputGood (reorder q.names bindings)
          (bindings_reorder bindingsGood q.names))
  | as p name ih =>
      cases bindings with
      | nil => exact .bot
      | cons binding rest =>
          rcases binding with ⟨actual, type⟩
          have head := bindingsGood (actual, type) List.mem_cons_self
          have tail : GoodBindings rest := fun b member => bindingsGood b (List.mem_cons_of_mem _ member)
          simp only [generatePattern]
          split
          · exact .and (safe_tyLe input type inputGood (.old head.upper) head.rows)
              (ih _ environmentGood _ priorGood type head.input rest tail)
          · exact .bot
  | nil | cons | snoc | nominal => exact .bot

theorem bindingSlots_good (names : List Nat) : GoodBindings (bindingSlots (α := α) names) := by
  induction names with
  | nil => intro binding member; cases member
  | cons name rest ih =>
      intro binding member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨rfl, rfl⟩
      · exact bindings_rename ih some binding member

theorem safe_close (n : Nat) (formula : Formula (Slots α n)) (good : SafeFormula formula) :
    SafeFormula (close n formula) := by
  induction n with
  | zero => exact good
  | succ n ih => exact ih (.existsSlot formula) good.existsSlot

theorem safe_constraints (pattern : Pattern Empty Inference.Expr)
    (environment : SchemeEnv α) (environmentGood : SafeEnvironment environment)
    (priorBindings : NamedTerms α) (priorGood : GoodBindings priorBindings)
    (input : TyTerm α) (inputGood : Input input) :
    SafeFormula (constraints pattern environment priorBindings input) :=
  safe_generatePattern pattern _ (environmentGood.rename _) _ (bindings_rename priorGood _)
    _ (inputGood.rename _) _ (bindingSlots_good _)

theorem safe_allocated (pattern : Pattern Empty Inference.Expr)
    (environment : SchemeEnv α) (environmentGood : SafeEnvironment environment)
    (priorBindings : NamedTerms α) (priorGood : GoodBindings priorBindings)
    (input : TyTerm α) (inputGood : Input input) :
    SafeFormula (generateAllocatedPattern pattern environment priorBindings input) :=
  safe_close _ _ (safe_constraints pattern environment environmentGood priorBindings priorGood input inputGood)

def principalPattern (pattern : Pattern Empty Inference.Expr) : Formula (Option Empty) :=
  generateCheckedPattern pattern [] [] (.var none)

theorem principal_safe (pattern : Pattern Empty Inference.Expr) : SafeFormula (principalPattern pattern) := by
  unfold principalPattern generateCheckedPattern
  split
  · refine safe_allocated pattern [] ?_ [] ?_ (.var none) ⟨rfl, rfl, rfl⟩
    · constructor <;> intro scheme member <;> cases member
    · intro binding member; cases member
  · exact .bot

/-- Every actual packed pattern clause internally supplies all three finite
syntax premises required by the new all-model solver theorem. -/
theorem generated_invariants (pattern : Pattern Empty Inference.Expr)
    (clause : PresenceNormalForm.Clause (Option Empty))
    (member : clause ∈ PresenceNormalForm.normalise (principalPattern pattern)) :
    CommonPatternConstraintGrammar.GoodAtoms clause.pack ∧
      PresenceSourceConstraintSupport.GoodAtoms clause.pack ∧
      PresenceGeneratedWidth.WidthAtoms clause.pack := by
  have good := principal_safe pattern
  exact ⟨CommonPatternFormulaGrammar.good_pack (CommonPatternFormulaGrammar.good_normalise good.endpoints clause member),
    PresenceSourceConstraintSupport.good_pack (PresenceSourceConstraintSupport.good_normalise good.rows clause member),
    PresenceGeneratedWidth.WidthClause.pack (PresenceGeneratedWidth.guarded_normalise good.widths clause member)⟩

end Yulang.CommonSourcePatternGenerationProvenance
