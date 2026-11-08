import Yulang.CommonRoleClosedResidualSlots
import Yulang.CommonDeclaredNominalSourceFamily

/-!
# Solved source families with actual closed record remainders

The inspector subtracts the written labels from the original closed spine,
then emits the four interval comparisons at the original shared slots. The
existing Common worklist solves those atoms together with the original
source clause. Its value and row parameters remain unrestricted.

`none` preserves failure of the finite same-spine preparation; `some []` is
ordinary unsatisfiability after successful preparation. This component does
not resolve unknown spines, provide pending wakeup, or implement full role
candidate selection.
-/
namespace Yulang.CommonRoleClosedResidualSourceFamily

open Common (Ty Row)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (Atom All Clause normalise)
open CommonRoleClosedResidualSlots (Comparison inspectAll)
open CommonDeclaredNominalSourceFamily (Scheme AssignmentEquivalent)

variable {slots : Nat}

def compile (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) : Option (List (Atom (Fin slots))) :=
  (inspectAll comparisons).map (original ++ ·)

def Models (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) (assignment : Fin slots → Comp Common.model) : Prop :=
  All Common.model assignment original ∧ CommonRoleClosedResidualSlots.Models comparisons assignment

theorem compile_models_exact (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) (assignment : Fin slots → Comp Common.model) :
    CommonNominalConstraints.Satisfied assignment (compile original comparisons) ↔
      Models original comparisons assignment := by
  have exactInspection := CommonRoleClosedResidualSlots.inspect_all_exact comparisons assignment
  cases found : inspectAll comparisons <;>
    simp_all [compile, Models, CommonNominalConstraints.Satisfied, PresenceNormalForm.all_append]

theorem compiled_grammar (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots)))
    (child : PresenceGeneratedChildGrammar.GoodAtoms original)
    (width : PresenceGeneratedWidth.WidthAtoms original)
    (rows : PresenceSourceConstraintSupport.GoodAtoms original)
    (atoms : List (Atom (Fin slots))) (compiled : compile original comparisons = some atoms) :
    PresenceGeneratedChildGrammar.GoodAtoms atoms ∧ PresenceGeneratedWidth.WidthAtoms atoms ∧
      PresenceSourceConstraintSupport.GoodAtoms atoms := by
  obtain ⟨added, returned, rfl⟩ := Option.map_eq_some_iff.mp compiled
  obtain ⟨newChild, newWidth, newRows⟩ :=
    CommonRoleClosedResidualSlots.inspect_all_grammar comparisons added returned
  exact ⟨child.append newChild, width.append newWidth, rows.append newRows⟩

def solve (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) : Option (List (Scheme slots)) :=
  (compile original comparisons).map fun atoms =>
    CommonDeclaredNominalSourceFamily.solve [] atoms []

theorem solve_eq_some (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) (family : List (Scheme slots)) :
    solve original comparisons = some family ↔
      ∃ atoms, compile original comparisons = some atoms ∧
        CommonDeclaredNominalSourceFamily.solve [] atoms [] = family :=
  Option.map_eq_some_iff

/-- Every returned scheme and every unrestricted value/row parameter satisfies
the original clause and all four comparisons of the actual record remainders.
No grammar, supportedness, or residual-model premise is put on parameters. -/
theorem all_parameters_models (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) (family : List (Scheme slots))
    (generated : solve original comparisons = some family) (scheme : Scheme slots)
    (member : scheme ∈ family) (rowParameters : Fin slots → Row)
    (parameters : scheme.Parameters) :
    Models original comparisons (scheme.instantiate rowParameters parameters) := by
  obtain ⟨atoms, compiled, rfl⟩ := (solve_eq_some original comparisons family).mp generated
  have model := CommonDeclaredNominalSourceFamily.all_parameters_models [] atoms []
    scheme member rowParameters parameters
  exact (compile_models_exact original comparisons _).mp ⟨atoms, compiled, model.1⟩

theorem models_congr (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots))) (first last : Fin slots → Comp Common.model)
    (same : AssignmentEquivalent first last) :
    Models original comparisons first ↔ Models original comparisons last := by
  rw [← compile_models_exact, ← compile_models_exact]
  unfold CommonNominalConstraints.Satisfied
  exact exists_congr fun atoms => and_congr Iff.rfl
    (CommonDeclaredNominalSourceFamily.atoms_congr atoms first last same)

/-- Every independent original assignment is recovered simultaneously at all
value and row slots. The only grammar premises concern the original clause;
the actual residual inspector establishes its own premises internally. -/
theorem solve_all_instances_exact (original : List (Atom (Fin slots)))
    (comparisons : List (Comparison (Fin slots)))
    (child : PresenceGeneratedChildGrammar.GoodAtoms original)
    (width : PresenceGeneratedWidth.WidthAtoms original)
    (rows : PresenceSourceConstraintSupport.GoodAtoms original)
    (assignment : Fin slots → Comp Common.model) :
    Models original comparisons assignment ↔
      ∃ family, solve original comparisons = some family ∧
        ∃ scheme ∈ family, ∃ rowParameters : Fin slots → Row,
          ∃ parameters : scheme.Parameters,
            AssignmentEquivalent (scheme.instantiate rowParameters parameters) assignment := by
  constructor
  · intro model
    obtain ⟨atoms, compiled, accepted⟩ :=
      (compile_models_exact original comparisons assignment).mpr model
    obtain ⟨newChild, newWidth, newRows⟩ :=
      compiled_grammar original comparisons child width rows atoms compiled
    have emptyComparisons : CommonDeclaredNominalSlots.Models [] [] assignment := by
      simp [CommonDeclaredNominalSlots.Models]
    obtain ⟨scheme, member, rowParameters, parameters, same⟩ :=
      (CommonDeclaredNominalSourceFamily.solve_all_instances_exact [] atoms []
        newChild newWidth newRows assignment).mp ⟨accepted, emptyComparisons⟩
    exact ⟨_, (solve_eq_some original comparisons _).mpr ⟨atoms, compiled, rfl⟩,
      scheme, member, rowParameters, parameters, same⟩
  · rintro ⟨family, generated, scheme, member, rowParameters, parameters, same⟩
    exact (models_congr original comparisons _ assignment same).mp
      (all_parameters_models original comparisons family generated scheme member rowParameters parameters)

/-- All grammar premises are obtained from the actual original source
generator. Arbitrary comparisons use its original slots, and every arbitrary
assignment is recovered with all original rows literally equal. -/
theorem generated_models_exact (expression : Inference.Expr) (clause : Clause (Option Empty))
    (generated : clause ∈ normalise (Core.PresenceGeneration.principal
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (comparisons : List (Comparison (Fin (clause.locals + 1))))
    (assignment : Fin (clause.locals + 1) → Comp Common.model) :
    Models clause.pack comparisons assignment ↔
      ∃ family, solve clause.pack comparisons = some family ∧
        ∃ scheme ∈ family, ∃ rowParameters : Fin (clause.locals + 1) → Row,
          ∃ parameters : scheme.Parameters,
            AssignmentEquivalent (scheme.instantiate rowParameters parameters) assignment :=
  solve_all_instances_exact clause.pack comparisons
    (PresenceGeneratedChildGrammar.generated_child_grammar expression clause generated)
    (PresenceGeneratedWidth.generated_width_atoms expression clause generated)
    (PresenceSourceConstraintSupport.generated_row_shapes expression clause generated) assignment

theorem generated_core_models_exact (expression : Core.Required.Term) (clause : Clause (Option Empty))
    (generated : clause ∈ normalise (Core.PresenceGeneration.CoreRules.principalCore
      ([] : Core.PresenceGeneration.SchemeEnv Empty) expression))
    (comparisons : List (Comparison (Fin (clause.locals + 1))))
    (assignment : Fin (clause.locals + 1) → Comp Common.model) :
    Models clause.pack comparisons assignment ↔
      ∃ family, solve clause.pack comparisons = some family ∧
        ∃ scheme ∈ family, ∃ rowParameters : Fin (clause.locals + 1) → Row,
          ∃ parameters : scheme.Parameters,
            AssignmentEquivalent (scheme.instantiate rowParameters parameters) assignment :=
  solve_all_instances_exact clause.pack comparisons
    (PresenceGeneratedChildGrammar.generated_core_child_grammar expression clause generated)
    (PresenceGeneratedWidth.generated_core_width_atoms expression clause generated)
    (CommonPresenceSourceFamily.generated_core_row_shapes expression clause generated) assignment

end Yulang.CommonRoleClosedResidualSourceFamily
