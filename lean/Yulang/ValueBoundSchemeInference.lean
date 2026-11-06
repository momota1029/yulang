import Yulang.ValueBoundSchemes
import Yulang.TypeSimplification

/-!
# Computing an output scheme with mixed value-variable occurrences

The bound solver returns syntax for all assignments, rather than selecting one
extremal assignment for every output. This adapter stores that syntax together
with an ordinary `Inference.TyTerm`. The supported syntax permits arbitrary
positive and negative occurrences; only record tails require a fixed spine.

Rows are captured separately, and are never replaced by the value substitution.
The result distinguishes unsupported record syntax from an inconsistent bound
problem. Its exactness theorem compares all free-parameter instances with all
models of the original constraints and the original output type term.
-/

namespace Yulang.ValueBoundSchemeInference

open StructuralBase ValueBounds

universe u

variable {n : Nat} {RowType : Type u}

structure Principal (n : Nat) (RowType : Type u) where
  bindings : ValueBoundSchemes.Scheme n RowType
  output : Inference.TyTerm (Fin n)
  rows : Fin n → RowType

def Principal.instantiate (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (scheme : Principal n RowType)
    (parameters : Valuation n RowType) : Ty RowType :=
  TypeSimplification.evaluate empty join leRow scheme.rows scheme.output
    (ValueBoundSchemes.instantiate scheme.bindings parameters)

inductive Result (n : Nat) (RowType : Type u) where
  | unsupported
  | unsatisfiable
  | inferred (scheme : Principal n RowType)

def infer (typeCheck : Ty RowType → Ty RowType → Bool)
    (problem : Problem n RowType) (rows : Fin n → RowType)
    (output : Inference.TyTerm (Fin n)) : Result n RowType :=
  if TypeSimplification.supported output then
    match ValueBoundSchemes.solve typeCheck problem with
    | none => .unsatisfiable
    | some bindings => .inferred ⟨bindings, output, rows⟩
  else .unsupported

theorem infer_unsupported_iff (typeCheck : Ty RowType → Ty RowType → Bool)
    (problem : Problem n RowType) (rows : Fin n → RowType)
    (output : Inference.TyTerm (Fin n)) :
    infer typeCheck problem rows output = .unsupported ↔
      TypeSimplification.supported output = false := by
  simp only [infer]
  cases TypeSimplification.supported output <;>
    cases ValueBoundSchemes.solve typeCheck problem <;> simp

theorem infer_inferred_iff (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problem : Problem n RowType) (rows : Fin n → RowType)
    (output : Inference.TyTerm (Fin n)) (scheme : Principal n RowType) :
    infer typeCheck problem rows output = .inferred scheme ↔
      TypeSimplification.supported output = true ∧
      Models leRow problem (least problem) ∧
      scheme = ⟨ValueBoundSchemes.coalesce problem, output, rows⟩ := by
  simp only [infer]
  split
  · rename_i supported
    cases solved : ValueBoundSchemes.solve typeCheck problem with
    | none =>
        constructor
        · intro impossible
          cases impossible
        · rintro ⟨_, model, _⟩
          have accepted := (ValueBoundSchemes.solve_some_iff typeCheck typeExact problem
            (ValueBoundSchemes.coalesce problem)).mpr ⟨rfl, model⟩
          rw [solved] at accepted
          cases accepted
    | some bindings =>
        obtain ⟨rfl, model⟩ :=
          (ValueBoundSchemes.solve_some_iff typeCheck typeExact problem bindings).mp solved
        constructor
        · intro same
          cases same
          exact ⟨supported, model, rfl⟩
        · rintro ⟨_, _, rfl⟩
          rfl
  · rename_i unsupported
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨supported, _⟩
      exact False.elim (unsupported supported)

theorem infer_unsatisfiable_iff (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problem : Problem n RowType) (rows : Fin n → RowType)
    (output : Inference.TyTerm (Fin n)) :
    infer typeCheck problem rows output = .unsatisfiable ↔
      TypeSimplification.supported output = true ∧ ¬ ∃ value, Models leRow problem value := by
  simp only [infer]
  split
  · rename_i supported
    have failure := ValueBoundSchemes.solve_none_iff typeCheck typeExact problem
    cases solved : ValueBoundSchemes.solve typeCheck problem <;> simp_all
  · rename_i unsupported
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨supported, _⟩
      exact False.elim (unsupported supported)

theorem evaluate_congruent (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (rows : Fin n → RowType) (output : Inference.TyTerm (Fin n))
    (supported : TypeSimplification.supported output = true) :
    ValueBoundSchemes.Congruent leRow
      (TypeSimplification.evaluate empty join leRow rows output) := by
  intro left right equivalent
  exact TypeSimplification.evaluate_congruent empty join leRow rowRefl rowTrans
    rows output supported left right equivalent

/-- A source-independent but fully computed principal output: neither a
solution nor a successful run is supplied as a premise. -/
theorem infer_principal_exact (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (typeCheck : Ty RowType → Ty RowType → Bool)
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problem : Problem n RowType) (rows : Fin n → RowType)
    (output : Inference.TyTerm (Fin n))
    (supported : TypeSimplification.supported output = true) (expected : Ty RowType) :
    (∃ scheme, infer typeCheck problem rows output = .inferred scheme ∧
      ∃ parameters, Subtype leRow (scheme.instantiate empty join leRow parameters) expected) ↔
    ∃ value, Models leRow problem value ∧
      Subtype leRow (TypeSimplification.evaluate empty join leRow rows output value) expected := by
  constructor
  · rintro ⟨scheme, inferred, parameters, below⟩
    obtain ⟨_, model, rfl⟩ :=
      (infer_inferred_iff typeCheck typeExact problem rows output scheme).mp inferred
    refine ⟨ValueBoundSchemes.instantiate (ValueBoundSchemes.coalesce problem) parameters, ?_, below⟩
    rw [ValueBoundSchemes.instantiate_coalesce]
    exact ValueBoundSchemes.expand_models model parameters
  · rintro ⟨value, model, below⟩
    refine ⟨⟨ValueBoundSchemes.coalesce problem, output, rows⟩, ?_, value, ?_⟩
    · exact (infer_inferred_iff typeCheck typeExact problem rows output _).mpr
        ⟨supported, least_models_of_models model, rfl⟩
    · change Subtype leRow (TypeSimplification.evaluate empty join leRow rows output
        (ValueBoundSchemes.instantiate (ValueBoundSchemes.coalesce problem) value)) expected
      rw [ValueBoundSchemes.instantiate_coalesce]
      exact .trans (evaluate_congruent empty join leRow rowRefl rowTrans rows output supported
        _ _ (ValueBoundSchemes.expand_equivalent model)).1 below

/-- The output syntax and all captured rows are retained exactly. -/
theorem infer_retains_rows (typeCheck : Ty RowType → Ty RowType → Bool)
    (problem : Problem n RowType) (rows : Fin n → RowType)
    (output : Inference.TyTerm (Fin n)) {scheme : Principal n RowType}
    (inferred : infer typeCheck problem rows output = .inferred scheme) :
    scheme.rows = rows ∧ scheme.output = output := by
  unfold infer at inferred
  split at inferred
  · cases solved : ValueBoundSchemes.solve typeCheck problem with
    | none => rw [solved] at inferred; cases inferred
    | some bindings =>
        rw [solved] at inferred
        cases inferred
        exact ⟨rfl, rfl⟩
  · cases inferred

end Yulang.ValueBoundSchemeInference
