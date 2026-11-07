import Yulang.CommonEffectClauseSplit
import Yulang.CommonEffectPolarityElimination
import Yulang.CommonEffectRecursiveExact
import Yulang.CommonEffectLatticeUniversals

/-! Integration of the actual recursive effect generator with exact finite
constructor, joint-witness, extremal and lattice-universal preprocessing. Unsupported
binders remain syntax; this module supplies no falsely solved output family. -/
namespace Yulang.CommonEffectPreparedGeneration
open Core.PresenceGeneration (CompTerm)
open CommonEffectRequestGeneration (Computation Declarations)
open CommonEffectFormula (Formula SchemeEnv)
open CommonEffectRecursiveSource (Expr Binding SemanticSignature Typing)
open CommonEffectRecursiveGeneration (ContextRel)

variable {scopes : Nat}

def prepare (formula : Formula scopes α) : Formula scopes α :=
  CommonEffectLatticeUniversals.eliminate
    (CommonEffectPolarityElimination.eliminate
      (CommonEffectConstructorNormalisation.normalise
        (CommonEffectClauseSplit.prepare (CommonEffectConstructorNormalisation.normalise formula))))

theorem prepare_exact (formula : Formula scopes α) (assignment : α → Computation) :
    (prepare formula).Holds assignment ↔ formula.Holds assignment :=
  (CommonEffectLatticeUniversals.eliminate_exact _ assignment).trans
    ((CommonEffectPolarityElimination.eliminate_exact _ assignment).trans
      ((CommonEffectConstructorNormalisation.normalise_exact _ assignment).trans
        ((CommonEffectClauseSplit.prepare_exact _ assignment).trans
          (CommonEffectConstructorNormalisation.normalise_exact formula assignment))))

def generate (declarations : Declarations α) (environment : SchemeEnv scopes α)
    (expression : Expr scopes) (output : CompTerm α) : Formula scopes α :=
  prepare (CommonEffectRecursiveGeneration.generate declarations environment expression output)

/-- Arbitrary declarations, all current recursive constructors, captured
polymorphic schemes and independent assignments; the original context
relation is the sole semantic premise. This is not the complete B3 theorem
because source annotation/SCC boundaries and pattern elaboration remain. -/
theorem generate_prepared_recursive_exact (signatures : List SemanticSignature) (expression : Expr scopes)
    {declarations : Declarations α} (symbolic : SchemeEnv scopes α) (environment : List (Binding scopes))
    (assignment : α → Computation) (output : CompTerm α)
    (context : ContextRel signatures declarations assignment symbolic environment) :
    (generate declarations symbolic expression output).Holds assignment ↔
      Typing signatures environment expression (output.eval Common.model assignment) :=
  (prepare_exact _ assignment).trans
    (CommonEffectRecursiveExact.generate_recursive_effect_exact signatures expression symbolic environment assignment output context)

end Yulang.CommonEffectPreparedGeneration
