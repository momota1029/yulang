import Yulang.ValueBoundElimination

/-!
# Solved identity inference and the necessity of output polarity

The identity example is quantified over arbitrary argument types, arbitrary
argument rows, and arbitrary observed computation types. Its final theorem is
an equivalence with the actual `Inference.principal [] (lam (var 0))` formula.
The output slot is solved by the executable value-bound solver; the argument
type and its row remain parameters of the inferred scheme.

The counterexample shows why the same minimization cannot be applied to a
local unknown occurring in an arrow argument. It exhibits a satisfying
assignment that a blind bottom substitution would incorrectly reject.
-/

namespace Yulang.ValueBoundEliminationExamples

open StructuralBase
open ValueBoundElimination

universe u

variable {RowType : Type u}

def identityProblem (argument : Ty RowType) : ValueBounds.Problem 1 RowType :=
  [.lower argument 0]

def identityOutput (argument : Ty RowType) (argumentRow : RowType)
    (value : ValueBounds.Valuation 1 RowType) : Ty RowType :=
  .arrow argument argumentRow (value 0) argumentRow

/-- The function accepts and returns the same computation parameter. The
result value is a separate local unknown which the solver may eliminate. -/
def identityTerm : Inference.TyTerm (Unit ⊕ Fin 1) :=
  .arrow (.var (.inl ())) (.var (.inl ())) (.var (.inr 0)) (.var (.inl ()))

theorem identity_polarity : polarity true identityTerm = true := rfl

theorem identity_evaluate (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (argument : Ty RowType) (argumentRow : RowType) :
    evaluate empty join leRow (fun _ : Unit => argument) (fun _ => argumentRow) identityTerm =
      identityOutput argument argumentRow := rfl

def inferIdentity (typeCheck : Ty RowType → Ty RowType → Bool)
    (argument : Ty RowType) (argumentRow : RowType) : Option (Ty RowType) :=
  infer typeCheck (identityProblem argument) (identityOutput argument argumentRow)

theorem identity_least (argument : Ty RowType) :
    ValueBounds.least (identityProblem argument) 0 = .union argument .bottom := rfl

theorem identity_models_iff (leRow : RowType → RowType → Prop)
    (argument : Ty RowType) (value : ValueBounds.Valuation 1 RowType) :
    ValueBounds.Models leRow (identityProblem argument) value ↔ Subtype leRow argument (value 0) := by
  simp [ValueBounds.Models, identityProblem, ValueBounds.Constraint.Holds]

/-- This computes successfully for every argument parameter. There is no
assumed solution, subtype-depth bound, or chosen concrete argument type. -/
theorem identity_inferred (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (argument : Ty RowType) (argumentRow : RowType) :
    inferIdentity typeCheck argument argumentRow =
      some (.arrow argument argumentRow (.union argument .bottom) argumentRow) := by
  apply (infer_some_iff typeCheck typeExact (identityProblem argument)
    (identityOutput argument argumentRow) _).mpr
  constructor
  · apply (identity_models_iff leRow argument _).mpr
    rw [identity_least]
    exact .unionLeft _ _
  · rfl

theorem checked_identity_inferred (typeCheck : Ty RowType → Ty RowType → Bool)
    (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop)
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (argument : Ty RowType) (argumentRow : RowType) :
    inferTerm typeCheck empty join leRow (identityProblem argument)
      (fun _ : Unit => argument) (fun _ => argumentRow) identityTerm =
        .inferred (.arrow argument argumentRow (.union argument .bottom) argumentRow) := by
  apply (inferTerm_inferred_iff typeCheck empty join leRow (identityProblem argument)
    (fun _ : Unit => argument) (fun _ => argumentRow) identityTerm _).mpr
  exact ⟨identity_polarity, identity_inferred typeCheck typeExact argument argumentRow⟩

/-- The redundant bottom from the executable finite union does not alter
the identity type. No display-normalization assumption is used. -/
theorem identity_result_equivalent (leRow : RowType → RowType → Prop)
    (rowRefl : ∀ row, leRow row row) (argument : Ty RowType) (argumentRow : RowType) :
    Subtype leRow (.arrow argument argumentRow (.union argument .bottom) argumentRow)
      (.arrow argument argumentRow argument argumentRow) ∧
    Subtype leRow (.arrow argument argumentRow argument argumentRow)
      (.arrow argument argumentRow (.union argument .bottom) argumentRow) :=
  ⟨.arrow (.refl _) (rowRefl _) (.unionElim (.refl _) (.bottom _)) (rowRefl _),
    .arrow (.refl _) (rowRefl _) (.unionLeft _ _) (rowRefl _)⟩

/-- Actual source-core principal inference, with every local result bound
solved and the argument value/row correlation retained as a parameter family.

The left side is the existing generated principal formula, not a replacement
declarative relation invented for the solver. The right side calls the actual
solver for each independent argument type and argument row. -/
theorem identity_principal_exact (typeCheck : Ty RowType → Ty RowType → Bool)
    (empty : RowType) (join : RowType → RowType → RowType)
    (leRow : RowType → RowType → Prop) (rowRefl : ∀ row, leRow row row)
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (expected : Inference.Comp (model RowType empty join leRow)) :
    (Inference.principal (α := Empty) [] (.lam (.var 0))).Holds
      (model RowType empty join leRow) (Inference.extend Empty.elim expected) ↔
      ∃ argument argumentRow result,
        inferIdentity typeCheck argument argumentRow = some result ∧
        Inference.Comp.le (model RowType empty join leRow)
          (Inference.Comp.pure (model RowType empty join leRow) result) expected := by
  let m := model RowType empty join leRow
  rw [Inference.principal_exact m (.lam (.var 0)) [] [] Empty.elim
    (Inference.EnvRel.nil m Empty.elim) expected]
  constructor
  · intro typed
    obtain ⟨input, output, body, outer⟩ := (Inference.Typing.lam_iff m [] (.var 0) expected).mp typed
    have compatible : Inference.Comp.le m input output := by
      simpa [Inference.Typing.var_iff, Inference.BindingLookup] using body
    refine ⟨input.1, input.2, .arrow input.1 input.2 (.union input.1 .bottom) input.2,
      identity_inferred typeCheck typeExact input.1 input.2, ?_⟩
    exact ⟨.trans
      (.arrow (.refl _) (rowRefl _)
        (.unionElim compatible.1 (.bottom _)) compatible.2) outer.1, outer.2⟩
  · rintro ⟨argument, argumentRow, result, computed, outer⟩
    have same : result = .arrow argument argumentRow (.union argument .bottom) argumentRow :=
      Option.some.inj (computed.symm.trans (identity_inferred typeCheck typeExact argument argumentRow))
    subst result
    apply Inference.Typing.lam (m := m) (a := (argument, argumentRow))
      (b := (Ty.union argument .bottom, argumentRow)) (c := expected) ?_ outer
    exact Inference.Typing.var rfl (Inference.BindingTyping.mono ⟨.unionLeft _ _, rowRefl _⟩)

/-! ## A negative occurrence cannot be minimized -/

def negativeTerm : Inference.TyTerm (Empty ⊕ Fin 1) :=
  .arrow (.var (.inr 0)) .empty (.base .int) .empty

theorem negative_polarity_rejected : polarity true negativeTerm = false := rfl

def negativeOutput (value : ValueBounds.Valuation 1 Unit) : Ty Unit :=
  .arrow (value 0) () (.base .int) ()

def trivialRow (_ _ : Unit) : Prop := True
def trivialRowCheck (_ _ : Unit) : Bool := true

private theorem trivialRowCheck_exact (left right : Unit) :
    trivialRowCheck left right = true ↔ trivialRow left right := by
  simp [trivialRowCheck, trivialRow]

private theorem negative_bottom_rejected :
    ¬ Subtype trivialRow (.arrow .bottom () (.base .int) ())
      (.arrow (.base .int) () (.base .int) ()) := by
  intro comparison
  have checked := (StructuralDecisions.check_exact trivialRowCheck trivialRowCheck_exact
    (fun _ _ => True.intro) _ _).mpr comparison
  have rejected : StructuralDecisions.check trivialRowCheck
      (.arrow .bottom () (.base .int) ()) (.arrow (.base .int) () (.base .int) ()) = false := by decide +kernel
  simp only [rejected, Bool.false_eq_true] at checked

/-- The original problem has a valid result instance, while blindly using its
least assignment in a negative output position loses that instance. -/
theorem negative_minimization_loses_instance :
    (∃ value : ValueBounds.Valuation 1 Unit, ValueBounds.Models trivialRow [] value ∧
      Subtype trivialRow (negativeOutput value) (.arrow (.base .int) () (.base .int) ())) ∧
    ¬ Subtype trivialRow (negativeOutput (ValueBounds.least ([] : ValueBounds.Problem 1 Unit)))
      (.arrow (.base .int) () (.base .int) ()) := by
  constructor
  · refine ⟨fun _ => .base .int, ?_, .refl _⟩
    intro constraint impossible
    cases impossible
  · exact negative_bottom_rejected

/-- Two contravariant arrow positions restore a positive occurrence. The
checker distinguishes this higher-order case from a single negative one. -/
theorem double_negative_polarity_accepted :
    polarity true (Parameter := Empty) (n := 1)
      (.arrow (.arrow (.var (.inr 0)) .empty (.base .int) .empty) .empty (.base .int) .empty) = true := rfl

end Yulang.ValueBoundEliminationExamples
