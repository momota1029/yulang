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

end Yulang.CommonRoleClosedResidualSourceFamily
