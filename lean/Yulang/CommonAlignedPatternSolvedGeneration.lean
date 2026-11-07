import Yulang.CommonPatternSolvedExact
import Yulang.CommonAlignedPatternGenerationProvenance

/-!
# All independent models of actual checked, aligned structural-pattern constraints

The actual Q7/name-set gate, aligned pattern allocator, default-expression generator, normalization,
and packing supply every syntax premise of the new solver internally.
This is the environment/value-type fragment of B2, not ordered case typing
with presence metadata, match/default effects, coverage, or nominal/list data.
-/

namespace Yulang.CommonAlignedPatternSolvedGeneration

open Common (Row Ty Equivalent)
open PresenceNormalForm (Clause normalise)
open CommonPresenceConstraintGraph (compile)
open CommonAlignedPatternGenerationProvenance (principalPattern)
open CasePatterns (Pattern)

/-- Literal equality of all original rows and demand equivalence at every
compiled node, for every independent model of every actually generated clause.
No syntax certificate or residual condition is imposed on the parameters. -/
theorem generated_models_exact (pattern : Pattern Empty Inference.Expr)
    (clause : Clause (Option Empty)) (generated : clause ∈ normalise (principalPattern pattern))
    (rows : Fin (clause.locals + 1) → Row) (values : Fin (compile clause.pack).size → Ty) :
    (compile clause.pack).Models rows values ↔
      ∃ scheme ∈ CommonPatternSolvedConstraints.solveAll (compile clause.pack),
        ∃ rowParameters : Fin (clause.locals + 1) → Row, ∃ parameters : scheme.Parameters,
          scheme.instantiateRows rowParameters = rows ∧
            ∀ index, Equivalent (scheme.instantiateValues rowParameters parameters index) (values index) := by
  obtain ⟨endpoints, rowGrammar, widths⟩ :=
    CommonAlignedPatternGenerationProvenance.generated_invariants pattern clause generated
  exact CommonPatternSolvedConstraints.compiled_models_exact clause.pack rowGrammar endpoints widths rows values

end Yulang.CommonAlignedPatternSolvedGeneration
