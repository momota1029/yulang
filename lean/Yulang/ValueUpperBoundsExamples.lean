import Yulang.ValueUpperBounds
import Yulang.ValueBoundEliminationExamples

/-!
# Executed upper-bound propagation and negative principal types

These examples use the same negative output that witnesses the failure of
blind lower-bound minimization. Greatest solving recovers every result
instance, including `int -> int`, from the principal type `any -> int`.
-/

namespace Yulang.ValueUpperBoundsExamples

open StructuralBase ValueBounds ValueUpperBounds
open ValueBoundEliminationExamples

def typeCheck : Ty Unit → Ty Unit → Bool :=
  StructuralDecisions.check trivialRowCheck

theorem typeCheck_exact (left right : Ty Unit) :
    typeCheck left right = true ↔ Subtype trivialRow left right := by
  apply StructuralDecisions.check_exact
  · intro _ _
    simp [trivialRowCheck, trivialRow]
  · exact fun _ _ => True.intro

theorem negative_polarity_accepted :
    ValueBoundElimination.polarity false negativeTerm = true := rfl

theorem negative_inferred_any :
    infer typeCheck ([] : Problem 1 Unit) negativeOutput =
      some (.arrow .top () (.base .int) ()) := rfl

theorem checked_negative_inferred_any :
    inferTerm typeCheck () (fun _ _ => ()) trivialRow ([] : Problem 1 Unit)
      Empty.elim (fun _ => ()) negativeTerm =
        .inferred (.arrow .top () (.base .int) ()) := rfl

theorem negativeOutput_antitone : Antitone trivialRow negativeOutput := by
  intro left right below
  exact .arrow (below 0) True.intro (.refl _) True.intro

/-- The greatest solution repairs all lost instances, not just the chosen
`int -> int` witness of the earlier minimization counterexample. -/
theorem negative_principal_exact (expected : Ty Unit) :
    Subtype trivialRow (.arrow .top () (.base .int) ()) expected ↔
      ∃ value : Valuation 1 Unit, Models trivialRow [] value ∧
        Subtype trivialRow (negativeOutput value) expected := by
  have exactness := infer_exact typeCheck typeCheck_exact ([] : Problem 1 Unit)
    negativeOutput negativeOutput_antitone expected
  constructor
  · intro below
    exact exactness.mp ⟨_, negative_inferred_any, below⟩
  · intro possible
    obtain ⟨result, inferred, below⟩ := exactness.mpr possible
    rw [negative_inferred_any] at inferred
    cases Option.some.inj inferred
    exact below

theorem negative_minimization_counterexample_repaired :
    Subtype trivialRow (.arrow .top () (.base .int) ())
      (.arrow (.base .int) () (.base .int) ()) := by
  exact (negative_principal_exact _).mpr negative_minimization_loses_instance.1

/-- A flow cycle carries a structural upper bound back to every predecessor. -/
def cyclicUpper : Problem 3 Unit :=
  [.flow 0 1, .flow 1 0, .flow 1 2,
    .upper 2 (.pair (.base .int) (.base .str))]

theorem cyclic_greatest_computed :
    (greatest cyclicUpper 0, greatest cyclicUpper 1, greatest cyclicUpper 2) =
      (.inter (.pair (.base .int) (.base .str)) .top,
        .inter (.pair (.base .int) (.base .str)) .top,
        .inter (.pair (.base .int) (.base .str)) .top) := by decide +kernel

theorem cyclic_upper_accepted :
    (solveGreatest typeCheck cyclicUpper).isSome = true := by decide +kernel

/-- Distinct upper bounds are retained as an intersection. They are not
unified or replaced by one selected bound. -/
def intersectedUpper : Problem 1 Unit :=
  [.upper 0 (.base .int), .upper 0 (.base .str)]

theorem intersected_upper_output :
    infer typeCheck intersectedUpper negativeOutput =
      some (.arrow (.inter (.base .int) (.inter (.base .str) .top)) () (.base .int) ()) := by
  decide +kernel

def inconsistentUpper : Problem 2 Unit :=
  [.lower (.base .int) 0, .flow 0 1, .upper 1 (.base .str)]

theorem inconsistent_upper_rejected :
    solveGreatest typeCheck inconsistentUpper = none := by decide +kernel

theorem inconsistent_upper_has_no_assignment :
    ¬ ∃ value, Models trivialRow inconsistentUpper value :=
  (solveGreatest_none_iff typeCheck typeCheck_exact inconsistentUpper).mp
    inconsistent_upper_rejected

end Yulang.ValueUpperBoundsExamples
