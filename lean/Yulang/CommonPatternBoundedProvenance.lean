import Yulang.CommonPatternBoundedAllocation
import Yulang.CommonPatternGenerationProvenance

/-! Source or alignment only reorders shared references. It therefore retains
all finite endpoint/row/width invariants of actual structural generation. -/

namespace Yulang.CommonPatternBoundedProvenance

open Core.PresenceGeneration
open CommonPatternEnvironment
open CommonPatternGeneration (renameBindings nilBindings)
open CommonPatternAllocation (Slots close bindingSlots)
open CommonPatternBoundedGeneration (generatePattern)
open CommonPatternBoundedAllocation (constraints generateAllocatedPattern generateCheckedPattern)
open CommonPatternGenerationProvenance
open CommonPatternBindingAlignment (reorder)
open CasePatterns (Pattern)

theorem bindings_reorder {bindings : NamedTerms α} (good : GoodBindings bindings) (names : List Nat) :
    GoodBindings (reorder names bindings) :=
  fun binding member => good binding (CommonPatternBindingAlignment.reorder_mem names bindings member)

theorem safe_generatePattern (pattern : Pattern Empty Inference.Expr) (cap : RowTerm α)
    (capGood : PresenceSourceConstraintSupport.simpleRow cap = true)
    (environment : SchemeEnv α) (environmentGood : SafeEnvironment environment)
    (priorBindings : NamedTerms α) (priorGood : GoodBindings priorBindings)
    (input : TyTerm α) (inputGood : Input input)
    (bindings : NamedTerms α) (bindingsGood : GoodBindings bindings) :
    SafeFormula (generatePattern pattern cap environment priorBindings input bindings) := by
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
        (.and (ihp (cap.rename rename) (by simpa only [PresenceSourceConstraintSupport.simpleRow_rename] using capGood) _ environmentGood.lift.lift _ prior _ ⟨rfl, rfl, rfl⟩ _ left)
          (ihq (cap.rename rename) (by simpa only [PresenceSourceConstraintSupport.simpleRow_rename] using capGood) _ environmentGood.lift.lift _ (bindings_append left prior) _ ⟨rfl, rfl, rfl⟩ _ right))))
  | field name p rest ihp ihr =>
      let rename : α → Option (Option α) := fun x => some (some x)
      have left := bindings_rename (bindings_take bindingsGood p.names.length) rename
      have right := bindings_rename (bindings_drop bindingsGood p.names.length) rename
      have prior := bindings_rename priorGood rename
      exact .existsSlot (.existsSlot (.and
        (safe_tyLe _ _ (inputGood.rename rename) (.old rfl) rfl)
        (.and (safe_tyLe _ _ ⟨rfl, rfl, rfl⟩ (.old rfl) rfl)
          (.and (ihp (cap.rename rename) (by simpa only [PresenceSourceConstraintSupport.simpleRow_rename] using capGood) _ environmentGood.lift.lift _ prior _ ⟨rfl, rfl, rfl⟩ _ left)
            (ihr (cap.rename rename) (by simpa only [PresenceSourceConstraintSupport.simpleRow_rename] using capGood) _ environmentGood.lift.lift _ (bindings_append left prior) _ ⟨rfl, rfl, rfl⟩ _ right)))))
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
          (.and (.and fallbackGood ⟨trivial, by simpa only [PresenceSourceConstraintSupport.GoodFormula,
              PresenceSourceConstraintSupport.simpleRow_rename] using capGood, .rowLe _ _⟩)
            (.and (ihp (cap.rename rename) (by simpa only [PresenceSourceConstraintSupport.simpleRow_rename] using capGood) _ environmentGood.lift.lift.lift _ prior _ ⟨rfl, rfl, rfl⟩ _ left)
              (ihr (cap.rename rename) (by simpa only [PresenceSourceConstraintSupport.simpleRow_rename] using capGood) _ environmentGood.lift.lift.lift _ (bindings_append left prior) _ ⟨rfl, rfl, rfl⟩ _ right)))))))
  | variant tag p ih =>
      exact .existsSlot (.and (safe_tyLe _ _ (inputGood.rename some) (.variant rfl) rfl)
        (ih (cap.rename some) (by simpa only [PresenceSourceConstraintSupport.simpleRow_rename] using capGood) _ environmentGood.lift _ (bindings_rename priorGood some) _ ⟨rfl, rfl, rfl⟩ _
          (bindings_rename bindingsGood some)))
  | or p q ihp ihq =>
      exact .and (ihp cap capGood _ environmentGood _ priorGood input inputGood bindings bindingsGood)
        (ihq cap capGood _ environmentGood _ priorGood input inputGood (reorder q.names bindings)
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
              (ih cap capGood _ environmentGood _ priorGood type head.input rest tail)
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

theorem safe_constraints (pattern : Pattern Empty Inference.Expr) (cap : RowTerm α)
    (capGood : PresenceSourceConstraintSupport.simpleRow cap = true)
    (environment : SchemeEnv α) (environmentGood : SafeEnvironment environment)
    (priorBindings : NamedTerms α) (priorGood : GoodBindings priorBindings)
    (input : TyTerm α) (inputGood : Input input) :
    SafeFormula (constraints pattern cap environment priorBindings input) :=
  safe_generatePattern pattern _ (by simpa only [PresenceSourceConstraintSupport.simpleRow_rename] using capGood) _ (environmentGood.rename _) _ (bindings_rename priorGood _)
    _ (inputGood.rename _) _ (bindingSlots_good _)

theorem safe_allocated (pattern : Pattern Empty Inference.Expr) (cap : RowTerm α)
    (capGood : PresenceSourceConstraintSupport.simpleRow cap = true)
    (environment : SchemeEnv α) (environmentGood : SafeEnvironment environment)
    (priorBindings : NamedTerms α) (priorGood : GoodBindings priorBindings)
    (input : TyTerm α) (inputGood : Input input) :
    SafeFormula (generateAllocatedPattern pattern cap environment priorBindings input) :=
  safe_close _ _ (safe_constraints pattern cap capGood environment environmentGood priorBindings priorGood input inputGood)

end Yulang.CommonPatternBoundedProvenance
