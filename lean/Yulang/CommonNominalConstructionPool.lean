import Yulang.CommonNominalCoreFieldGeneration
import Yulang.CommonNominalFormulaPool

/-!
# Original field/source typing iff actual finite mixed pool models

The original body registry, fields, shared invariant arguments and all source
sites feed the actual generator, normalizer, packed allocator and full mixed
pool compiler. The same original lexical environments verify every body and
site. Ambient computations are fixed literally in independent problem models.

This connects the complete finite graph-generation route for the displayed
resolved construction judgment. It does not assert a full all-parameter
solver, source declaration validation, runtime site evaluation or weak EOF.
-/

namespace Yulang.CommonNominalConstructionPool

open CommonNominalCarrier
open Core.PresenceGeneration (Comp TyTerm RowTerm CompTerm SchemeEnv Binding EnvRel)
open CommonNominalFormulaPool (Problem)

def presence (registry : CommonNominalSourceRegistry.Registry vertices (Fin ambient)) (symbolic : SchemeEnv (Fin ambient))
    (declaration : CommonNominalFieldGeneration.Declaration types rows) (sources : List CommonNominalFieldGeneration.SourceSite)
    (arguments : Fin types → TyTerm (Fin ambient)) (rowArguments : Fin rows → RowTerm (Fin ambient))
    (output : CompTerm (Fin ambient)) : List (Problem ambient) :=
  CommonNominalFormulaPool.compile (CommonNominalFieldGeneration.generate registry symbolic declaration sources arguments rowArguments output)

theorem presence_generation_pool_exact
    (registry : CommonNominalSourceRegistry.Registry vertices (Fin ambient)) (symbolic : SchemeEnv (Fin ambient))
    (environment : List (Binding model)) (assignment : Fin ambient → Comp model)
    (declaration : CommonNominalFieldGeneration.Declaration types rows) (sources : List CommonNominalFieldGeneration.SourceSite)
    (arguments : Fin types → TyTerm (Fin ambient)) (rowArguments : Fin rows → RowTerm (Fin ambient))
    (output : CompTerm (Fin ambient)) (related : EnvRel model assignment symbolic environment) :
    CommonNominalFieldGeneration.ConstructionTyping registry assignment environment declaration sources
      (fun index => (arguments index).eval model assignment)
      (fun index => (rowArguments index).eval model assignment) (output.eval model assignment) ↔
      ∃ problem ∈ presence registry symbolic declaration sources arguments rowArguments output,
        ∃ rowValues nodeValues, problem.Models assignment rowValues nodeValues :=
  (CommonNominalFieldGeneration.generate_fields_exact registry symbolic environment assignment
    declaration sources arguments rowArguments output related).symm.trans
      (CommonNominalFormulaPool.compile_exact _ assignment)

def core (registry : CommonNominalCoreCastRegistry.Registry vertices (Fin ambient)) (symbolic : SchemeEnv (Fin ambient))
    (declaration : CommonNominalCoreFieldGeneration.Declaration types rows) (sources : List CommonNominalCoreFieldGeneration.SourceSite)
    (arguments : Fin types → TyTerm (Fin ambient)) (rowArguments : Fin rows → RowTerm (Fin ambient))
    (output : CompTerm (Fin ambient)) : List (Problem ambient) :=
  CommonNominalFormulaPool.compile (CommonNominalCoreFieldGeneration.generate registry symbolic declaration sources arguments rowArguments output)

/-- Every original literal-bearing Core body/site typing obligation and
every original field/argument feeds the actual finite generation. Graph data
contains constraints; source ASTs stay at the original source interface.
All models use the new carrier and fix every original ambient Comp literally. -/
theorem core_generation_pool_exact
    (registry : CommonNominalCoreCastRegistry.Registry vertices (Fin ambient)) (symbolic : SchemeEnv (Fin ambient))
    (environment : List (Core.CommonSyntax.Binding model)) (assignment : Fin ambient → Comp model)
    (declaration : CommonNominalCoreFieldGeneration.Declaration types rows) (sources : List CommonNominalCoreFieldGeneration.SourceSite)
    (arguments : Fin types → TyTerm (Fin ambient)) (rowArguments : Fin rows → RowTerm (Fin ambient))
    (output : CompTerm (Fin ambient)) (sourceEnvironment : List (Binding model))
    (actualRelated : Core.CommonSyntax.EnvRel model environment sourceEnvironment)
    (related : EnvRel model assignment symbolic sourceEnvironment) :
    CommonNominalCoreFieldGeneration.ConstructionTyping registry assignment environment declaration sources
      (fun index => (arguments index).eval model assignment)
      (fun index => (rowArguments index).eval model assignment) (output.eval model assignment) ↔
      ∃ problem ∈ core registry symbolic declaration sources arguments rowArguments output,
        ∃ rowValues nodeValues, problem.Models assignment rowValues nodeValues :=
  (CommonNominalCoreFieldGeneration.generate_fields_exact registry symbolic environment assignment
    declaration sources arguments rowArguments output sourceEnvironment actualRelated related).symm.trans
      (CommonNominalFormulaPool.compile_exact _ assignment)

end Yulang.CommonNominalConstructionPool
