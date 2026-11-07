import Yulang.CommonPatternFormulaGrammar
import Yulang.CommonPatternAllocation

/-! Actual pattern generation supplies finite endpoint, row, and paired-width
invariants. These are properties of symbolic syntax, not free parameters. -/

namespace Yulang.CommonPatternGenerationProvenance

open Core.PresenceGeneration
open CommonPatternEnvironment
open CommonPatternGeneration
open CommonPatternAllocation
open CasePatterns (Pattern)
open CommonPatternBoundInspection (Upper)

structure Input (term : TyTerm α) : Prop where
  lower : PresenceGeneratedChildGrammar.lower term = true
  noWidth : PresenceGeneratedWidth.widthTail term = none
  rows : PresenceSourceConstraintSupport.simpleTyRows term = true

structure BinderType (term : TyTerm α) : Prop where
  upper : PresenceGeneratedChildGrammar.upper term = true
  rows : PresenceSourceConstraintSupport.simpleTyRows term = true

theorem Input.rename {term : TyTerm α} (good : Input term) (f : α → β) : Input (term.rename f) :=
  ⟨by simpa using good.lower, by simpa using good.noWidth, by simpa using good.rows⟩

theorem BinderType.rename {term : TyTerm α} (good : BinderType term) (f : α → β) : BinderType (term.rename f) :=
  ⟨by simpa using good.upper, by simpa using good.rows⟩

theorem BinderType.input {term : TyTerm α} (good : BinderType term) : Input term :=
  ⟨PresenceGeneratedChildGrammar.upper_lower term good.upper,
    PresenceGeneratedWidth.upper_no_width term good.upper, good.rows⟩

def GoodBindings (bindings : NamedTerms α) : Prop := ∀ binding ∈ bindings, BinderType binding.2

theorem bindings_rename {bindings : NamedTerms α} (good : GoodBindings bindings) (f : α → β) :
    GoodBindings (renameBindings f bindings) := by
  intro binding member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact (good original present).rename f

theorem bindings_take {bindings : NamedTerms α} (good : GoodBindings bindings) (n : Nat) :
    GoodBindings (bindings.take n) := fun binding member => good binding (List.mem_of_mem_take member)

theorem bindings_drop {bindings : NamedTerms α} (good : GoodBindings bindings) (n : Nat) :
    GoodBindings (bindings.drop n) := fun binding member => good binding (List.mem_of_mem_drop member)

theorem bindings_append {first last : NamedTerms α} (left : GoodBindings first) (right : GoodBindings last) :
    GoodBindings (first ++ last) := fun binding member => (List.mem_append.mp member).elim (left binding) (right binding)

structure SafeEnvironment (environment : SchemeEnv α) : Prop where
  endpoints : PresenceGeneratedChildGrammar.GoodEnv environment
  rows : PresenceSourceConstraintSupport.GoodEnv environment
  widths : PresenceGeneratedWidth.GuardedEnv environment

theorem SafeEnvironment.lift {environment : SchemeEnv α} (good : SafeEnvironment environment) :
    SafeEnvironment environment.lift := ⟨good.endpoints.lift, good.rows.lift, good.widths.lift⟩

theorem SafeEnvironment.rename {environment : SchemeEnv α} (good : SafeEnvironment environment) (f : α → β) :
    SafeEnvironment (environment.rename f) :=
  ⟨good.endpoints.rename f, good.rows.rename f, good.widths.rename f⟩

theorem with_bindings {environment : SchemeEnv α} (good : SafeEnvironment environment)
    (bindings : NamedTerms α) (valid : GoodBindings bindings) :
    SafeEnvironment (symbolicPrefix bindings ++ environment) := by
  induction bindings with
  | nil => exact good
  | cons binding rest ih =>
      have head := valid binding List.mem_cons_self
      have tail : GoodBindings rest := fun b member => valid b (List.mem_cons_of_mem _ member)
      have prior := ih tail
      exact ⟨prior.endpoints.cons (PresenceGeneratedChildGrammar.good_mono head.upper),
        prior.rows.cons (PresenceSourceConstraintSupport.good_mono ⟨head.rows, rfl⟩),
        prior.widths.cons (PresenceGeneratedWidth.guarded_mono head.upper)⟩

structure SafeFormula (formula : Formula α) : Prop where
  endpoints : CommonPatternFormulaGrammar.GoodFormula formula
  rows : PresenceSourceConstraintSupport.GoodFormula formula
  widths : PresenceGeneratedWidth.Guarded formula

theorem SafeFormula.top : SafeFormula (.top : Formula α) := ⟨trivial, trivial, .top⟩
theorem SafeFormula.bot : SafeFormula (.bot : Formula α) := ⟨trivial, trivial, .bot⟩

theorem SafeFormula.and {first last : Formula α} (left : SafeFormula first) (right : SafeFormula last) :
    SafeFormula (.and first last) :=
  ⟨⟨left.endpoints, right.endpoints⟩, ⟨left.rows, right.rows⟩, .and left.widths right.widths⟩

theorem SafeFormula.or {first last : Formula α} (left : SafeFormula first) (right : SafeFormula last) :
    SafeFormula (.or first last) :=
  ⟨⟨left.endpoints, right.endpoints⟩, ⟨left.rows, right.rows⟩, .or left.widths right.widths⟩

theorem SafeFormula.existsSlot {formula : Formula (Option α)} (good : SafeFormula formula) :
    SafeFormula (.existsSlot formula) := ⟨good.endpoints, good.rows, .existsSlot good.widths⟩

theorem safe_tyLe (source target : TyTerm α) (first : Input source) (last : Upper target)
    (rows : PresenceSourceConstraintSupport.simpleTyRows target = true) : SafeFormula (.tyLe source target) :=
  ⟨⟨first.lower, last⟩, ⟨first.rows, rows⟩, .tyLe source target first.noWidth⟩

theorem safe_generate (environment : SchemeEnv α) (good : SafeEnvironment environment)
    (code : Inference.Expr) (result : CompTerm α) (type : BinderType result.ty)
    (row : PresenceSourceConstraintSupport.simpleRow result.row = true) :
    SafeFormula (generate environment code result) :=
  ⟨CommonPatternFormulaGrammar.of_old
      (PresenceGeneratedChildGrammar.good_generate code environment good.endpoints result type.upper),
    PresenceSourceConstraintSupport.good_generate code environment good.rows result ⟨type.rows, row⟩,
    PresenceGeneratedWidth.guarded_generate code environment good.widths result type.upper⟩

theorem safe_nilBindings (bindings : NamedTerms α) {formula : Formula α} (good : SafeFormula formula) :
    SafeFormula (nilBindings bindings formula) := by
  cases bindings with
  | nil => exact good
  | cons => exact .bot

theorem safe_optional (label : Nat) (source payload : TyTerm α) (first : Input source)
    (last : BinderType payload) : SafeFormula (CommonPatternDefaults.optionalConstraints label source payload) :=
  .or (.and (safe_tyLe .top payload ⟨rfl, rfl, rfl⟩ (.old last.upper) last.rows)
      (safe_tyLe source .emptyRecord first (.old rfl) rfl))
    (safe_tyLe source (.union .exactEmpty (.required label payload)) first (.optional last.upper)
      (by simp [PresenceSourceConstraintSupport.simpleTyRows, last.rows]))

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
        (.and (safe_tyLe _ _ ⟨rfl, rfl, rfl⟩ (.old rfl) rfl)
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
        (ihq _ environmentGood _ priorGood input inputGood bindings bindingsGood)
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
  generateAllocatedPattern pattern [] [] (.var none)

theorem principal_safe (pattern : Pattern Empty Inference.Expr) : SafeFormula (principalPattern pattern) := by
  refine safe_allocated pattern [] ?_ [] ?_ (.var none) ⟨rfl, rfl, rfl⟩
  · constructor <;> intro scheme member <;> cases member
  · intro binding member; cases member

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

end Yulang.CommonPatternGenerationProvenance
