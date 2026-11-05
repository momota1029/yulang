import Yulang.ValueBounds

/-!
# Eliminating solved value bounds without defaulting parameters

`ValueBounds` constructs a least assignment for the local unknowns of its
finite bound problem. Such an assignment is useful for an output only when the
output is monotone in those unknowns. In particular, minimizing the argument of
an arrow reverses, rather than preserves, its subtype relation.

This module checks polarity on the existing `Inference.TyTerm` syntax. Ambient
parameters and local unknowns are different constructors of a sum: parameters
are held fixed, and only the local unknowns are minimized. Arrow inputs reverse
polarity; rows are supplied independently and remain unchanged. A record tail
must have a fixed record spine, retaining first-field-wins lookup.

The elimination theorem is exact for every parameter assignment and every
observed result type. It computes the local solution and the result type; it
does not require the caller to supply a solution. Choosing which variables to
generalize, solving constructor-nested bounds, and recursive value types remain
separate obligations.
-/

namespace Yulang.ValueBoundElimination

open StructuralBase
open Inference (TyTerm RowTerm)

universe u

variable {n : Nat} {RowType : Type u}

abbrev Pointwise (leRow : RowType → RowType → Prop)
    (left right : ValueBounds.Valuation n RowType) : Prop :=
  ∀ index, Subtype leRow (left index) (right index)

/-- Monotonicity concerns only the local unknowns, not ambient parameters. -/
def Monotone (leRow : RowType → RowType → Prop)
    (output : ValueBounds.Valuation n RowType → Ty RowType) : Prop :=
  ∀ left right, Pointwise leRow left right → Subtype leRow (output left) (output right)

/-- A successful bound solution is immediately used to construct the output. -/
def infer (typeCheck : Ty RowType → Ty RowType → Bool)
    (problem : ValueBounds.Problem n RowType)
    (output : ValueBounds.Valuation n RowType → Ty RowType) : Option (Ty RowType) :=
  (ValueBounds.solve typeCheck problem).map output

theorem infer_some_iff (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problem : ValueBounds.Problem n RowType)
    (output : ValueBounds.Valuation n RowType → Ty RowType) (result : Ty RowType) :
    infer typeCheck problem output = some result ↔
      ValueBounds.Models leRow problem (ValueBounds.least problem) ∧
        output (ValueBounds.least problem) = result := by
  simp only [infer, Option.map_eq_some_iff]
  constructor
  · rintro ⟨value, solved, found⟩
    obtain ⟨rfl, model⟩ := (ValueBounds.solve_some_iff typeCheck typeExact problem value).mp solved
    exact ⟨model, found⟩
  · rintro ⟨model, found⟩
    exact ⟨ValueBounds.least problem,
      (ValueBounds.solve_some_iff typeCheck typeExact problem _).mpr ⟨rfl, model⟩, found⟩

/-- The output of the solver describes exactly the original existential
problem whenever the output is monotone in the minimized unknowns. -/
theorem infer_exact (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problem : ValueBounds.Problem n RowType)
    (output : ValueBounds.Valuation n RowType → Ty RowType)
    (monotone : Monotone leRow output) (expected : Ty RowType) :
    (∃ result, infer typeCheck problem output = some result ∧ Subtype leRow result expected) ↔
      ∃ value, ValueBounds.Models leRow problem value ∧ Subtype leRow (output value) expected := by
  constructor
  · rintro ⟨result, inferred, below⟩
    obtain ⟨model, rfl⟩ := (infer_some_iff typeCheck typeExact problem output result).mp inferred
    exact ⟨ValueBounds.least problem, model, below⟩
  · rintro ⟨value, model, below⟩
    refine ⟨output (ValueBounds.least problem), ?_, ?_⟩
    · exact (infer_some_iff typeCheck typeExact problem output _).mpr
        ⟨ValueBounds.least_models_of_models model, rfl⟩
    · exact .trans (monotone _ _ (ValueBounds.least_below model.lower)) below

theorem infer_principal (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    {problem : ValueBounds.Problem n RowType}
    {output : ValueBounds.Valuation n RowType → Ty RowType}
    (monotone : Monotone leRow output) {result : Ty RowType}
    (inferred : infer typeCheck problem output = some result)
    {value : ValueBounds.Valuation n RowType} (model : ValueBounds.Models leRow problem value) :
    Subtype leRow result (output value) := by
  obtain ⟨_, rfl⟩ := (infer_some_iff typeCheck typeExact problem output result).mp inferred
  exact monotone _ _ (ValueBounds.least_below model.lower)

/-- Local inference fails exactly when its bounds are inconsistent. It does
not choose values for the parameters of a polymorphic scheme. -/
theorem infer_none_iff (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problem : ValueBounds.Problem n RowType)
    (output : ValueBounds.Valuation n RowType → Ty RowType) :
    infer typeCheck problem output = none ↔ ¬ ∃ value, ValueBounds.Models leRow problem value := by
  simp only [infer, Option.map_eq_none_iff, ValueBounds.solve_none_iff typeCheck typeExact]

/-! ## A polarity check on the existing type syntax -/

variable {Parameter : Type}

/-- Record structure is fixed; local unknowns may occur in field values. -/
def recordSpine : TyTerm α → Bool
  | .emptyRecord => true
  | .record _ _ rest => recordSpine rest
  | _ => false

/-- `positive = true` checks covariance in local unknowns. `false` checks
contravariance. Parameters pass both checks because they are not minimized. -/
def polarity (positive : Bool) : TyTerm (Parameter ⊕ Fin n) → Bool
  | .var (.inl _) => true
  | .var (.inr _) => positive
  | .base _ | .bottom | .top | .emptyRecord => true
  | .union left right | .inter left right | .pair left right =>
      polarity positive left && polarity positive right
  | .record _ value rest =>
      recordSpine rest && polarity positive value && polarity positive rest
  | .variant _ value => polarity positive value
  | .arrow input _ output _ => polarity (!positive) input && polarity positive output

/-- Value unknowns and parameter types share no slot. All row assignments are
fixed independently of the value unknowns in this solver layer. -/
def environment (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (parameters : Parameter → Ty RowType)
    (rows : Parameter ⊕ Fin n → RowType) (value : ValueBounds.Valuation n RowType) :
    Parameter ⊕ Fin n → Inference.Comp (model RowType empty join leRow)
  | .inl parameter => (parameters parameter, rows (.inl parameter))
  | .inr index => (value index, rows (.inr index))

def evaluate (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (parameters : Parameter → Ty RowType)
    (rows : Parameter ⊕ Fin n → RowType) (term : TyTerm (Parameter ⊕ Fin n))
    (value : ValueBounds.Valuation n RowType) : Ty RowType :=
  term.eval (model RowType empty join leRow) (environment empty join leRow parameters rows value)

theorem row_eval_independent (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (parameters : Parameter → Ty RowType)
    (rows : Parameter ⊕ Fin n → RowType) (term : RowTerm (Parameter ⊕ Fin n))
    (left right : ValueBounds.Valuation n RowType) :
    term.eval (model RowType empty join leRow) (environment empty join leRow parameters rows left) =
      term.eval (model RowType empty join leRow)
        (environment empty join leRow parameters rows right) := by
  induction term with
  | var index => cases index <;> rfl
  | empty => rfl
  | join a b iha ihb => simp only [RowTerm.eval, iha, ihb]

theorem evaluate_recordSpine (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (parameters : Parameter → Ty RowType)
    (rows : Parameter ⊕ Fin n → RowType) (term : TyTerm (Parameter ⊕ Fin n))
    (value : ValueBounds.Valuation n RowType) (shape : recordSpine term = true) :
    IsRecord (evaluate empty join leRow parameters rows term value) := by
  induction term with
  | emptyRecord => exact .empty
  | record label head rest _ ih => exact .field (ih shape)
  | _ => cases shape

/-- A subtype between records has exactly the ordinary first-field lookup
obligations. Cut elimination removes the possible intervening types. -/
theorem record_subtype_fields {leRow : RowType → RowType → Prop}
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    {source target : Ty RowType} (sourceShape : IsRecord source) (targetShape : IsRecord target)
    (subtype : Subtype leRow source target) :
    (∀ label expected, target.lookup label = some expected →
      ∃ actual, source.lookup label = some actual) ∧
    (∀ label actual expected, source.lookup label = some actual →
      target.lookup label = some expected → Subtype leRow actual expected) := by
  have comparison := StructuralDecisions.Comparison.complete (leRow := leRow) rowTrans subtype
  cases comparison with
  | refl =>
      exact ⟨fun _ expected found => ⟨expected, found⟩,
        fun _ _ _ found expectedFound => by
          have same := Option.some.inj (found.symm.trans expectedFound)
          cases same
          exact .refl _⟩
  | record _ _ fields comparisons =>
      exact ⟨fields, fun label actual expected found expectedFound =>
        (comparisons label actual expected found expectedFound).sound⟩
  | bottom | unionElim | interLeft | interRight | pair | variant | arrow => cases sourceShape
  | top | interIntro | unionLeft | unionRight => cases targetShape

theorem record_cons_mono {leRow : RowType → RowType → Prop}
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (label : Nat) {head head' rest rest' : Ty RowType}
    (restShape : IsRecord rest) (restShape' : IsRecord rest')
    (heads : Subtype leRow head head') (tails : Subtype leRow rest rest') :
    Subtype leRow (.record label head rest) (.record label head' rest') := by
  obtain ⟨fields, comparisons⟩ := record_subtype_fields (leRow := leRow) rowTrans restShape restShape' tails
  apply Subtype.record (.field restShape) (.field restShape')
  · intro key expected found
    by_cases equal : key = label
    · exact ⟨head, by simp [Ty.lookup, equal]⟩
    · obtain ⟨actual, actualFound⟩ := fields key expected (by simpa [Ty.lookup, equal] using found)
      exact ⟨actual, by simpa [Ty.lookup, equal] using actualFound⟩
  · intro key actual expected found expectedFound
    by_cases equal : key = label
    · have actualSame : head = actual := by simpa [Ty.lookup, equal] using found
      have expectedSame : head' = expected := by simpa [Ty.lookup, equal] using expectedFound
      simpa [← actualSame, ← expectedSame] using heads
    · exact comparisons key actual expected (by simpa [Ty.lookup, equal] using found)
        (by simpa [Ty.lookup, equal] using expectedFound)

/-- Direction of the subtype relation certified by a polarity check. -/
def Ordered (leRow : RowType → RowType → Prop) (positive : Bool)
    (left right : Ty RowType) : Prop :=
  if positive then Subtype leRow left right else Subtype leRow right left

theorem polarity_sound (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (parameters : Parameter → Ty RowType) (rows : Parameter ⊕ Fin n → RowType)
    (term : TyTerm (Parameter ⊕ Fin n)) (positive : Bool)
    (checked : polarity positive term = true)
    (left right : ValueBounds.Valuation n RowType) (below : Pointwise leRow left right) :
    Ordered leRow positive (evaluate empty join leRow parameters rows term left)
      (evaluate empty join leRow parameters rows term right) := by
  induction term generalizing positive with
  | var index =>
      cases index with
      | inl parameter => cases positive <;> exact .refl _
      | inr index =>
          have direction : positive = true := checked
          subst positive
          exact below index
  | base | bottom | top | emptyRecord => cases positive <;> exact .refl _
  | union a b iha ihb =>
      have checks : polarity positive a = true ∧ polarity positive b = true := by
        simpa only [polarity, Bool.and_eq_true] using checked
      obtain ⟨ha, hb⟩ := checks
      cases positive <;> exact union_mono (iha _ ha) (ihb _ hb)
  | inter a b iha ihb =>
      have checks : polarity positive a = true ∧ polarity positive b = true := by
        simpa only [polarity, Bool.and_eq_true] using checked
      obtain ⟨ha, hb⟩ := checks
      cases positive <;> exact inter_mono (iha _ ha) (ihb _ hb)
  | pair a b iha ihb =>
      have checks : polarity positive a = true ∧ polarity positive b = true := by
        simpa only [polarity, Bool.and_eq_true] using checked
      obtain ⟨ha, hb⟩ := checks
      cases positive <;> exact .pair (iha _ ha) (ihb _ hb)
  | variant label value ih =>
      cases positive <;> exact .variant (ih _ checked)
  | record label head rest ihh ihr =>
      have checks : (recordSpine rest = true ∧ polarity positive head = true) ∧
          polarity positive rest = true := by
        simpa only [polarity, Bool.and_eq_true] using checked
      obtain ⟨⟨shape, headChecked⟩, restChecked⟩ := checks
      have leftShape := evaluate_recordSpine empty join leRow parameters rows rest left shape
      have rightShape := evaluate_recordSpine empty join leRow parameters rows rest right shape
      cases positive
      · exact record_cons_mono (leRow := leRow) rowTrans label rightShape leftShape (ihh _ headChecked) (ihr _ restChecked)
      · exact record_cons_mono (leRow := leRow) rowTrans label leftShape rightShape (ihh _ headChecked) (ihr _ restChecked)
  | arrow input inputRow output outputRow ihi iho =>
      have checks : polarity (!positive) input = true ∧ polarity positive output = true := by
        simpa only [polarity, Bool.and_eq_true] using checked
      obtain ⟨hi, ho⟩ := checks
      have inputRows := row_eval_independent empty join leRow parameters rows inputRow left right
      have outputRows := row_eval_independent empty join leRow parameters rows outputRow left right
      cases positive
      · exact .arrow (ihi _ hi) (inputRows ▸ rowRefl _) (iho _ ho) (outputRows ▸ rowRefl _)
      · exact .arrow (ihi _ hi) (inputRows ▸ rowRefl _) (iho _ ho) (outputRows ▸ rowRefl _)

theorem evaluate_monotone (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (parameters : Parameter → Ty RowType) (rows : Parameter ⊕ Fin n → RowType)
    (term : TyTerm (Parameter ⊕ Fin n)) (checked : polarity true term = true) :
    Monotone leRow (evaluate empty join leRow parameters rows term) := by
  intro left right below
  exact polarity_sound empty join leRow rowRefl rowTrans parameters rows term true checked left right below

/-! ## Checked elimination and parameterized instance families -/

inductive Result (RowType : Type u) where
  | unsupported
  | inconsistent
  | inferred (type : Ty RowType)

/-- Unsupported output variance is kept distinct from inconsistent bounds.
Only the latter is a type-error result of this fragment's exact solver. -/
def inferTerm (typeCheck : Ty RowType → Ty RowType → Bool)
    (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (problem : ValueBounds.Problem n RowType)
    (parameters : Parameter → Ty RowType) (rows : Parameter ⊕ Fin n → RowType)
    (term : TyTerm (Parameter ⊕ Fin n)) : Result RowType :=
  if polarity true term then
    match infer typeCheck problem (evaluate empty join leRow parameters rows term) with
    | none => .inconsistent
    | some type => .inferred type
  else .unsupported

theorem inferTerm_inferred_iff (typeCheck : Ty RowType → Ty RowType → Bool)
    (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (problem : ValueBounds.Problem n RowType)
    (parameters : Parameter → Ty RowType) (rows : Parameter ⊕ Fin n → RowType)
    (term : TyTerm (Parameter ⊕ Fin n)) (result : Ty RowType) :
    inferTerm typeCheck empty join leRow problem parameters rows term = .inferred result ↔
      polarity true term = true ∧
        infer typeCheck problem (evaluate empty join leRow parameters rows term) = some result := by
  unfold inferTerm
  split
  · rename_i checked
    cases found : infer typeCheck problem (evaluate empty join leRow parameters rows term) <;>
      simp [checked]
  · rename_i unsupported
    simp [unsupported]

theorem inferTerm_unsupported_iff (typeCheck : Ty RowType → Ty RowType → Bool)
    (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (problem : ValueBounds.Problem n RowType)
    (parameters : Parameter → Ty RowType) (rows : Parameter ⊕ Fin n → RowType)
    (term : TyTerm (Parameter ⊕ Fin n)) :
    inferTerm typeCheck empty join leRow problem parameters rows term = .unsupported ↔
      polarity true term = false := by
  unfold inferTerm
  cases checked : polarity true term <;> simp
  cases infer typeCheck problem (evaluate empty join leRow parameters rows term) <;> simp

theorem inferTerm_inconsistent_iff (typeCheck : Ty RowType → Ty RowType → Bool)
    (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop)
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problem : ValueBounds.Problem n RowType)
    (parameters : Parameter → Ty RowType) (rows : Parameter ⊕ Fin n → RowType)
    (term : TyTerm (Parameter ⊕ Fin n)) :
    inferTerm typeCheck empty join leRow problem parameters rows term = .inconsistent ↔
      polarity true term = true ∧ ¬ ∃ value, ValueBounds.Models leRow problem value := by
  rw [← infer_none_iff typeCheck typeExact problem
    (evaluate empty join leRow parameters rows term)]
  unfold inferTerm
  split
  · rename_i checked
    cases found : infer typeCheck problem (evaluate empty join leRow parameters rows term) <;>
      simp [checked]
  · rename_i unsupported
    simp [unsupported]

/-- The checked entry point combines polarity verification, construction of
the local assignment, and construction of the resulting type. -/
theorem inferTerm_exact (typeCheck : Ty RowType → Ty RowType → Bool)
    (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problem : ValueBounds.Problem n RowType)
    (parameters : Parameter → Ty RowType) (rows : Parameter ⊕ Fin n → RowType)
    (term : TyTerm (Parameter ⊕ Fin n)) (expected : Ty RowType) :
    (∃ result, inferTerm typeCheck empty join leRow problem parameters rows term = .inferred result ∧
      Subtype leRow result expected) ↔
      polarity true term = true ∧
        ∃ value, ValueBounds.Models leRow problem value ∧
          Subtype leRow (evaluate empty join leRow parameters rows term value) expected := by
  constructor
  · rintro ⟨result, inferred, below⟩
    obtain ⟨checked, computed⟩ :=
      (inferTerm_inferred_iff typeCheck empty join leRow problem parameters rows term result).mp inferred
    exact ⟨checked,
      (infer_exact typeCheck typeExact problem _
        (evaluate_monotone empty join leRow rowRefl rowTrans parameters rows term checked) expected).mp
        ⟨result, computed, below⟩⟩
  · rintro ⟨checked, possible⟩
    obtain ⟨result, computed, below⟩ :=
      (infer_exact typeCheck typeExact problem _
        (evaluate_monotone empty join leRow rowRefl rowTrans parameters rows term checked) expected).mpr possible
    exact ⟨result,
      (inferTerm_inferred_iff typeCheck empty join leRow problem parameters rows term result).mpr
        ⟨checked, computed⟩, below⟩

/-- Parameter assignments are quantified independently of the local solver.
This is preservation of an instance family, not a procedure for deciding which
variables a source binding may generalize. -/
theorem parameterized_exact (typeCheck : Ty RowType → Ty RowType → Bool)
    (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : RowType}, leRow a b → leRow b c → leRow a c)
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problems : (Parameter → Ty RowType) → ValueBounds.Problem n RowType)
    (rows : Parameter ⊕ Fin n → RowType)
    (term : TyTerm (Parameter ⊕ Fin n)) (checked : polarity true term = true)
    (expected : Ty RowType) :
    (∃ parameters result,
      inferTerm typeCheck empty join leRow (problems parameters) parameters rows term = .inferred result ∧
        Subtype leRow result expected) ↔
      ∃ parameters value, ValueBounds.Models leRow (problems parameters) value ∧
        Subtype leRow (evaluate empty join leRow parameters rows term value) expected := by
  apply exists_congr
  intro parameters
  rw [inferTerm_exact typeCheck empty join leRow rowRefl rowTrans typeExact]
  exact and_iff_right checked

end Yulang.ValueBoundElimination
