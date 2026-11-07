import Yulang.CommonEffectUniversalArms
import Yulang.CommonEffectPresence
import Yulang.CommonBoundCoalescing

/-! Canonical finite witnesses below rigid operation-local type binders.
The input is a finite bound graph whose endpoints contain only captured and
rigid names. Flexible nodes may flow cyclically, but are absent from endpoint
syntax. Elimination produces real finite comparisons, retaining any outer
universal binder. Constructor equations between flexible nodes are separate. -/
namespace Yulang.CommonEffectScopedBounds
open Core.PresenceGeneration (CompTerm TyTerm)
open CommonEffectRequestGeneration (Computation localEnv)
open CommonEffectFormula
open LayerBoundTemplates (Constraint Problem lowerBounds)
open CommonBoundCoalescing (Models lower rigidComparisons Consistent)

variable {scopes : Nat}

def constraintFormula : Constraint n (TyTerm α) → Formula scopes (α ⊕ Fin n)
  | .lower bound target => .tyLe (bound.rename Sum.inl) (.var (.inr target))
  | .flow source target => .tyLe (.var (.inr source)) (.var (.inr target))
  | .upper source bound => .tyLe (.var (.inr source)) (bound.rename Sum.inl)
  | .check source target => .tyLe (source.rename Sum.inl) (target.rename Sum.inl)

def matrix (problem : Problem n (TyTerm α)) : Formula scopes (α ⊕ Fin n) :=
  CommonEffectUniversalArms.andAll (problem.map constraintFormula)

theorem matrix_exact (problem : Problem n (TyTerm α)) (assignment : α → Computation) (values : Fin n → Common.Ty) :
    (matrix (scopes := scopes) problem).Holds (localEnv assignment values) ↔
      Models (fun bound => bound.eval Common.model assignment) problem values := by
  simp only [matrix, CommonEffectUniversalArms.andAll_exact, List.forall_mem_map, Models]
  apply forall_congr'; intro constraint
  apply forall_congr'; intro _
  cases constraint <;> simp only [constraintFormula, Formula.holds_tyLe, TyTerm.eval_rename,
    TyTerm.eval, localEnv, CommonBoundCoalescing.Holds]
  all_goals rfl

def eliminate (problem : Problem n (TyTerm α)) : Formula scopes α :=
  CommonEffectUniversalArms.andAll ((rigidComparisons problem).map (fun pair => .tyLe pair.1 pair.2))

theorem eliminate_consistent (problem : Problem n (TyTerm α)) (assignment : α → Computation) :
    (eliminate (scopes := scopes) problem).Holds assignment ↔
      Consistent (fun bound => bound.eval Common.model assignment) problem := by
  simp only [eliminate, CommonEffectUniversalArms.andAll_exact, List.forall_mem_map, Formula.holds_tyLe, Consistent]

/-- Removes all flexible type witnesses, retaining the captured assignment
literally and emitting only the actual finite rigid comparisons. -/
theorem eliminate_exact (problem : Problem n (TyTerm α)) (assignment : α → Computation) :
    (eliminate (scopes := scopes) problem).Holds assignment ↔
      (Formula.existsTypes n (matrix (scopes := scopes) problem)).Holds assignment := by
  exact (eliminate_consistent problem assignment).trans
    ((CommonBoundCoalescing.consistent_iff_satisfiable (fun bound => bound.eval Common.model assignment) problem).trans
      (exists_congr (fun values => (matrix_exact problem assignment values).symm)))

def joinTerms : List (TyTerm α) → TyTerm α
  | [] => .bottom
  | term :: rest => .union term (joinTerms rest)

theorem joinTerms_eval (terms : List (TyTerm α)) (assignment : α → Computation) :
    (joinTerms terms).eval Common.model assignment =
      CommonBoundCoalescing.joinTypes (terms.map (fun term => term.eval Common.model assignment)) := by
  induction terms with
  | nil => rfl
  | cons term rest ih =>
    change CommonSyntax.Layer.union _ _ = CommonSyntax.Layer.union _ _
    rw [ih]

/-- A computed finite tuple; it is not an arbitrary Skolem function input. -/
def witnesses (problem : Problem n (TyTerm α)) (index : Fin n) : TyTerm α := joinTerms (lowerBounds problem index)

theorem witnesses_eval (problem : Problem n (TyTerm α)) (assignment : α → Computation) :
    (fun index => (witnesses problem index).eval Common.model assignment) =
      lower (fun bound => bound.eval Common.model assignment) problem := by
  funext index
  exact joinTerms_eval _ assignment

theorem canonical_witness_exact (problem : Problem n (TyTerm α)) (assignment : α → Computation) :
    (∃ values, Models (fun bound => bound.eval Common.model assignment) problem values) ↔
      Models (fun bound => bound.eval Common.model assignment) problem
        (fun index => (witnesses problem index).eval Common.model assignment) := by
  rw [witnesses_eval]
  exact ⟨fun ⟨_, model⟩ => CommonBoundCoalescing.lower_models_of_models model, fun model => ⟨_, model⟩⟩

/-- Pointwise existential witnesses yield ONE actual finite syntax tuple.
All ambient computations/rows remain fixed before the rigid local binder. -/
theorem uniform_witness_exact (problem : Problem n (TyTerm (α ⊕ Fin count))) (assignment : α → Computation) :
    (∀ locals : Fin count → Common.Ty,
      ∃ values, Models (fun bound => bound.eval Common.model (localEnv assignment locals)) problem values) ↔
      ∀ locals : Fin count → Common.Ty,
        Models (fun bound => bound.eval Common.model (localEnv assignment locals)) problem
          (fun index => (witnesses problem index).eval Common.model (localEnv assignment locals)) :=
  forall_congr' (fun locals => canonical_witness_exact problem (localEnv assignment locals))

/-- Exact finite matrix transformation under the original quantifier order;
the outer universal remains in syntax for the next rigid-check phase. -/
theorem universal_elimination_exact (problem : Problem n (TyTerm (α ⊕ Fin count))) (assignment : α → Computation) :
    (Formula.forallTypes count (eliminate (scopes := scopes) problem)).Holds assignment ↔
      (Formula.forallTypes count (.existsTypes n (matrix (scopes := scopes) problem))).Holds assignment :=
  forall_congr' (fun locals => eliminate_exact problem (localEnv assignment locals))
end Yulang.CommonEffectScopedBounds
