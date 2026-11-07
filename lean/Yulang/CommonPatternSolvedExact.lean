import Yulang.CommonPatternSolvedConstraints
import Yulang.CommonPatternBoundRows
import Yulang.CommonPatternConstraintGrammar

/-!
# Every model of pattern-compatible finite constraints is a solved instance

The syntax premises describe input atoms only. Every assigned Common value
and every independent row is quantified. Recovered parameters have the
ordinary unrestricted product; row equality is literal and every original
compiled value is recovered up to Common demand equivalence.
-/

namespace Yulang.CommonPatternSolvedConstraints

open Common (Ty Row Equivalent)
open Core.PresenceGeneration
open CommonPresenceConstraintGraph (compile splitAtoms)
open CommonBoundRefSolver (Scheme ofState ofState_retract models_congr)

variable {m : Nat}

/-- Completeness for these finite syntax invariants. Actual pattern/case
generation must supply the three syntax premises in its own provenance
theorem; no premise is imposed on the recovered parameters. -/
theorem compiled_models_complete (atoms : List (PresenceNormalForm.Atom (Fin m)))
    (rowGrammar : PresenceSourceConstraintSupport.GoodAtoms atoms)
    (childGrammar : CommonPatternConstraintGrammar.GoodAtoms atoms)
    (widths : PresenceGeneratedWidth.WidthAtoms atoms)
    (rows : Fin m → Row) (values : Fin (compile atoms).size → Ty)
    (models : (compile atoms).Models rows values) :
    ∃ scheme ∈ solveAll (compile atoms), ∃ rowParameters : Fin m → Row,
      ∃ parameters : scheme.Parameters,
        scheme.instantiateRows rowParameters = rows ∧
          ∀ index, Equivalent (scheme.instantiateValues rowParameters parameters index) (values index) := by
  obtain ⟨originalRows, declaredOriginal⟩ := CommonRowDeclarations.declare_split_rows_some atoms rowGrammar
  obtain ⟨state, returned, selected⟩ :=
    (CommonPatternConstraintGrammar.compiled_run_models_exact atoms childGrammar widths rows values models.1).mp models.2.1
  obtain ⟨auxRows, declaredAux⟩ := CommonPatternBoundRows.run_declare_checks_some
    (splitAtoms atoms).pool (CommonGeneratedPoolRows.compiled_pool_rows atoms rowGrammar) _ state returned
  let scheme := ofState (splitAtoms atoms).pool originalRows state auxRows
  have member : scheme ∈ solveAll (compile atoms) := by
    rw [solveAll_compile]
    exact (mem_solveProblem (splitAtoms atoms) scheme).mpr
      ⟨originalRows, declaredOriginal, state, returned, auxRows, declaredAux, rfl⟩
  obtain ⟨parameters, sameRows, sameValues⟩ := ofState_retract (splitAtoms atoms) originalRows
    declaredOriginal state auxRows declaredAux rows values models selected
  exact ⟨scheme, member, rows, parameters, sameRows, sameValues⟩

theorem compiled_models_exact (atoms : List (PresenceNormalForm.Atom (Fin m)))
    (rowGrammar : PresenceSourceConstraintSupport.GoodAtoms atoms)
    (childGrammar : CommonPatternConstraintGrammar.GoodAtoms atoms)
    (widths : PresenceGeneratedWidth.WidthAtoms atoms)
    (rows : Fin m → Row) (values : Fin (compile atoms).size → Ty) :
    (compile atoms).Models rows values ↔
      ∃ scheme ∈ solveAll (compile atoms), ∃ rowParameters : Fin m → Row,
        ∃ parameters : scheme.Parameters,
          scheme.instantiateRows rowParameters = rows ∧
            ∀ index, Equivalent (scheme.instantiateValues rowParameters parameters index) (values index) := by
  constructor
  · exact compiled_models_complete atoms rowGrammar childGrammar widths rows values
  · rintro ⟨scheme, member, rowParameters, parameters, sameRows, sameValues⟩
    have model := all_parameter_sound atoms scheme member rowParameters parameters
    rw [sameRows] at model
    exact (models_congr (compile atoms) rows _ values sameValues).mp model

end Yulang.CommonPatternSolvedConstraints
