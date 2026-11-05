import Yulang.ValueInference

/-!
# Actual source-core inference and rejection regressions

These examples run `solve` on existing expressions. Positive results construct
their intermediate and final value types; negative results are connected to
nonexistence of *any* original declarative typing/generated-formula solution.
The signed latent-row example checks that inference does not erase negative
hygiene debt inside a value's type.
-/

namespace Yulang.ValueInference.Examples

open Inference

abbrev TestTy := ValueType 1 Nat

def mixed : Expr := .branch (.lit .bool) (.lit .int) (.lit .str)

def mixedType : TestTy := .union (.base .int) (.union (.base .str) .bottom)

theorem mixed_solved : solve (n := 1) (Key := Nat) [] mixed = .solved mixedType := by
  decide +kernel

/-- The retained empty join has precisely the expected `int | str` meaning. -/
theorem mixed_generated_exact (result : Comp (SignedStructural.model 1 Nat)) :
    (principal ([] : SchemeEnv Empty) mixed).Holds (SignedStructural.model 1 Nat)
      (extend Empty.elim result) ↔
      SignedStructural.Subtype (.union (.base .int) (.base .str)) result.1 := by
  rw [closed_principal_solved_exact mixed mixedType mixed_solved result]
  have compact : SignedStructural.Subtype mixedType (.union (.base .int) (.base .str)) :=
    .unionElim (.unionLeft _ _) (.unionElim (.unionRight _ _) (.bottom _))
  have expand : SignedStructural.Subtype (.union (.base .int) (.base .str)) mixedType :=
    .unionElim (.unionLeft _ _) (.trans (.unionLeft _ _) (.unionRight _ _))
  constructor
  · exact fun below => .trans expand below
  · exact fun below => .trans compact below

theorem mixed_cannot_be_int :
    ¬ (principal ([] : SchemeEnv Empty) mixed).Holds (SignedStructural.model 1 Nat)
      (extend Empty.elim (.base .int, [])) := by
  rw [mixed_generated_exact]
  exact SignedStructural.int_union_str_not_int

def badCondition : Expr := .branch (.lit .int) (.lit .int) (.lit .str)

theorem bad_condition_rejected : solve (n := 1) (Key := Nat) [] badCondition = .unsat := by
  decide +kernel

theorem bad_condition_has_no_generated_solution :
    ¬ ∃ result, (principal ([] : SchemeEnv Empty) badCondition).Holds
      (SignedStructural.model 1 Nat) (extend Empty.elim result) :=
  (closed_principal_unsat_iff badCondition rfl).mp bad_condition_rejected

def constructed : Expr := .pair (.variant 0 (.lit .int)) (.variant 1 mixed)

def constructedType : TestTy := .pair (.variant 0 (.base .int)) (.variant 1 mixedType)

theorem constructor_shapes_are_inferred :
    solve (n := 1) (Key := Nat) [] constructed = .solved constructedType := by
  decide +kernel

theorem constructors_principal (result : Comp (SignedStructural.model 1 Nat)) :
    (principal ([] : SchemeEnv Empty) constructed).Holds (SignedStructural.model 1 Nat)
      (extend Empty.elim result) ↔ SignedStructural.Subtype constructedType result.1 :=
  closed_principal_solved_exact constructed constructedType constructor_shapes_are_inferred result

def valueLet : Expr := .letE (.lit .int) (.pair (.var 0) (.var 0))

theorem value_let_solved :
    solve (n := 1) (Key := Nat) [] valueLet = .solved (.pair (.base .int) (.base .int)) := by
  decide +kernel

/-- This endpoint includes the generator's disjunction for a syntactic value. -/
theorem value_let_both_rules_exact (result : Comp (SignedStructural.model 1 Nat)) :
    (principal ([] : SchemeEnv Empty) valueLet).Holds (SignedStructural.model 1 Nat)
      (extend Empty.elim result) ↔
      SignedStructural.Subtype (.pair (.base .int) (.base .int)) result.1 :=
  closed_principal_solved_exact valueLet _ value_let_solved result

def computedLet : Expr := .letE mixed (.pair (.var 0) (.lit .bool))

theorem computed_let_solved :
    solve (n := 1) (Key := Nat) [] computedLet = .solved (.pair mixedType (.base .bool)) := by
  decide +kernel

def shadowedLet : Expr :=
  .letE (.lit .int) (.letE (.lit .str) (.pair (.var 1) (.var 0)))

theorem captures_outer_binding :
    solve (n := 1) (Key := Nat) [] shadowedLet = .solved (.pair (.base .int) (.base .str)) := by
  decide +kernel

theorem unbound_variable_rejected : solve (n := 1) (Key := Nat) [] (.var 0) = .unsat := by
  decide +kernel

theorem unbound_variable_has_no_type :
    ¬ ∃ result, Typing (SignedStructural.model 1 Nat) [] (.var 0) result :=
  (source_unsat_iff [] (.var 0) rfl).mp unbound_variable_rejected

theorem lambda_is_unsupported :
    solve (n := 1) (Key := Nat) [] (.lam (.var 0)) = .unsupported := rfl

theorem application_is_unsupported :
    solve (n := 1) (Key := Nat) [] (.app (.lam (.var 0)) (.lit .int)) = .unsupported := rfl

/-- Unsupported is not a claim that the lambda has no valid type. -/
theorem unsupported_lambda_has_a_type :
    Typing (SignedStructural.model 1 Nat) [] (.lam (.var 0))
      (.arrow (.base .int) [] (.base .int) [], []) := by
  apply Typing.lam (m := SignedStructural.model 1 Nat)
    (a := (.base .int, [])) (b := (.base .int, []))
  · exact .var rfl (.mono ⟨.refl _, SignedStructural.row_refl _⟩)
  · exact ⟨.refl _, SignedStructural.row_refl _⟩

def debt : Directed.Row 1 Nat := [⟨0, fun _ => -1⟩]

def latentDebt : TestTy := .arrow (.base .unit) [] (.base .unit) debt

theorem latent_negative_debt_is_retained :
    solve [latentDebt] (.pair (.var 0) (.lit .bool)) =
      .solved (.pair latentDebt (.base .bool)) := by
  decide +kernel

/-- Ordinary code execution checks the same public entry point; the theorems
above use kernel reduction and do not depend on native proof evaluation. -/
def runRegression : IO Unit := do
  unless decide (solve (n := 1) (Key := Nat) [] mixed = .solved mixedType) do
    throw (IO.userError "mixed branch must infer the union of both branches")
  unless decide (solve (n := 1) (Key := Nat) [] badCondition = .unsat) do
    throw (IO.userError "integer condition must have no inferred solution")
  unless decide (solve (n := 1) (Key := Nat) [] constructed = .solved constructedType) do
    throw (IO.userError "pair and variant shapes must be synthesized")
  unless decide (solve (n := 1) (Key := Nat) [] computedLet = .solved (.pair mixedType (.base .bool))) do
    throw (IO.userError "computed let must preserve its inferred union")
  unless decide (solve [latentDebt] (.pair (.var 0) (.lit .bool)) =
      .solved (.pair latentDebt (.base .bool))) do
    throw (IO.userError "latent signed effect debt must survive value inference")

#eval runRegression

end Yulang.ValueInference.Examples
