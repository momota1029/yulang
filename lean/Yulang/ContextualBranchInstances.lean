import Yulang.ContextualBranchSolver
import Yulang.ContextualRegularInference

/-!
# Complete free-parameter families for computed constructor branches

This joins executable formula branching, actual saturation and the concrete
regular solution blocks. Both sides of the principal equality use the same
`RegularInferenceModel.Ty` carrier. Every input formula is covered, including
rejected formulas; no solver success, supplied model, fuel or closed-cache
premise appears in the all-input theorems.
-/

namespace Yulang.ContextualBranchInstances

open ContextualBranchSolver (Formula Branch solve)
open RegularInferenceModel (Ty State graph solution)
open ContextualRegularInference (Le Equivalent)

universe u
variable {n : Nat} {Row : Type u}

abbrev Models (leRow : Row → Row → Prop) (source : NestedValueSolver.Graph n Row)
    (formula : Formula n) (value : Fin n → Ty Row) : Prop :=
  ContextualBranchSolver.Models leRow source formula (graph Row) (fun index => State.node (value index))

/-- Every independent assignment is represented by an actual accepted branch
and unrestricted shared parameters of its actual regular solution block. -/
theorem models_exact (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (source : NestedValueSolver.Graph n Row) (formula : Formula n) (value : Fin n → Ty Row) :
    Models leRow source formula value ↔
      ∃ branch ∈ solve rowCheck source formula, ∃ parameter : Fin n → Ty Row,
        ∀ index, Equivalent leRow (solution source branch.cache parameter index) (value index) := by
  constructor
  · rintro ⟨realizes, formulaValid⟩
    obtain ⟨input, member, inputValid⟩ := (ContextualBranchSolver.branches_exact _ formula).mp formulaValid
    have model : ContextualRegularInference.Models source input leRow value := ⟨realizes, inputValid⟩
    obtain ⟨cache, solved, parameter, equivalent⟩ :=
      (ContextualRegularInference.models_exact rowCheck leRow rowRefl rowTrans rowExact
        source input value).mp model
    exact ⟨⟨input, cache⟩, (ContextualBranchSolver.mem_solve rowCheck source formula _).mpr
      ⟨member, solved⟩, parameter, equivalent⟩
  · rintro ⟨branch, member, parameter, equivalent⟩
    obtain ⟨inputMember, solved⟩ := (ContextualBranchSolver.mem_solve rowCheck source formula branch).mp member
    have model := (ContextualRegularInference.solve_models_exact rowCheck leRow rowRefl rowTrans rowExact
      source branch.input branch.cache solved value).mpr ⟨parameter, equivalent⟩
    exact ⟨model.1, (ContextualBranchSolver.branches_exact _ formula).mpr
      ⟨branch.input, inputMember, model.2⟩⟩

def ConstrainedInstance (leRow : Row → Row → Prop) (source : NestedValueSolver.Graph n Row)
    (formula : Formula n) (root : Fin n) (target : Ty Row) : Prop :=
  ∃ value : Fin n → Ty Row, Models leRow source formula value ∧ Le leRow (value root) target

/-- Full principal output-instance equality for the declared branching
constructor fragment. All source inputs and target types are quantified. -/
theorem instances_exact (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (source : NestedValueSolver.Graph n Row) (formula : Formula n) (root : Fin n) (target : Ty Row) :
    ConstrainedInstance leRow source formula root target ↔
      ∃ branch ∈ solve rowCheck source formula, ∃ parameter : Fin n → Ty Row,
        Le leRow (solution source branch.cache parameter root) target := by
  constructor
  · rintro ⟨value, model, below⟩
    obtain ⟨branch, member, parameter, equivalent⟩ :=
      (models_exact rowCheck leRow rowRefl rowTrans rowExact source formula value).mp model
    exact ⟨branch, member, parameter,
      ProducerContextualRegular.producerLe_trans (equivalent root).1 below⟩
  · rintro ⟨branch, member, parameter, below⟩
    refine ⟨solution source branch.cache parameter, ?_, below⟩
    exact (models_exact rowCheck leRow rowRefl rowTrans rowExact source formula _).mpr
      ⟨branch, member, parameter, fun _ => ProducerContextualRegular.producerEq_refl _⟩

/-- Empty output is exactly unsatisfiability in the single concrete inference
carrier, not merely in some separately chosen regular graph universe. -/
theorem solve_nil_iff (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (source : NestedValueSolver.Graph n Row) (formula : Formula n) :
    solve rowCheck source formula = [] ↔ ¬ ∃ value : Fin n → Ty Row, Models leRow source formula value := by
  constructor
  · rintro rejected ⟨value, model⟩
    obtain ⟨branch, member, _⟩ :=
      (models_exact rowCheck leRow rowRefl rowTrans rowExact source formula value).mp model
    simp [rejected] at member
  · intro impossible
    cases result : solve rowCheck source formula with
    | nil => rfl
    | cons branch rest =>
        have member : branch ∈ solve rowCheck source formula := by simp [result]
        let parameter : Fin n → Ty Row := fun _ => .bottom
        have model := (models_exact rowCheck leRow rowRefl rowTrans rowExact source formula
          (solution source branch.cache parameter)).mpr
          ⟨branch, member, parameter, fun _ => ProducerContextualRegular.producerEq_refl _⟩
        exact False.elim (impossible ⟨_, model⟩)

end Yulang.ContextualBranchInstances
