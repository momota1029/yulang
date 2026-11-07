import Yulang.CommonNominalSourceRegistry
import Yulang.CorePresenceGenerationCore

/-!
# Actual Common source code compiled from checked cast bodies

Finite route search produces real nested source lets, retaining each original
cast body and its captured lexical environment. The body's pure source typing
is obtained from actual registry generation. Composition preserves an arbitrary
input computation row; at a pure input the compiled conversion has empty row.

The result is executable source syntax, not an externally supplied Plan or
body bound. Common source evaluation/typed PureCasts.Plan interpretation and
all parametric/structural keep-search-failure still need their separate bridge.
-/

namespace Yulang.CommonNominalCastSourceCode

open CommonNominalCarrier
open Core.PresenceGeneration (Comp TyTerm Binding SchemeEnv EnvRel)
open CommonNominalSourceRegistry (Registry)

def compileSteps (registry : Registry vertices α) :
    Fin vertices → List (Fin vertices) → Inference.Expr → Inference.Expr
  | _, [], input => input
  | source, next :: rest, input =>
      compileSteps registry next rest (.letE input (registry.body source next))

def compile (registry : Registry vertices α) (source target : Fin vertices) (input : Inference.Expr) :
    Option Inference.Expr :=
  (CommonCastRoutes.search registry.adjacency source target).map fun route =>
    compileSteps registry source route.steps input

theorem compile_exact (registry : Registry vertices α) (source target : Fin vertices) (input : Inference.Expr) :
    (compile registry source target input).isSome = true ↔
      FiniteReachability.Reach registry.adjacency [source] target := by
  simp only [compile, Option.isSome_map]
  exact CommonCastRoutes.search_exact registry.adjacency source target

private theorem let_body_typed (registry : Registry vertices α) (assignment : α → Comp model)
    (environment : List (Binding model)) (valid : registry.Valid environment assignment)
    (source target : Fin vertices) (edge : target ∈ registry.adjacency source) (input : Inference.Expr) (row : Row)
    (typed : Core.PresenceGeneration.Typing model environment input ((registry.endpoint source).eval model assignment, row)) :
    Core.PresenceGeneration.Typing model environment (.letE input (registry.body source target))
      ((registry.endpoint target).eval model assignment, row) := by
  apply Core.PresenceGeneration.Typing.letComputed typed (valid source target edge)
  refine ⟨subtype_refl _, ?_⟩
  intro occurrence present
  exact present.elim id False.elim

/-- No purity or value restriction is imposed on the original input row.
Only the conversion bodies have pure immediate rows. -/
theorem steps_typed (registry : Registry vertices α) (assignment : α → Comp model)
    (environment : List (Binding model)) (valid : registry.Valid environment assignment)
    (source target : Fin vertices) (steps : List (Fin vertices))
    (path : CommonCastRoutes.Edges registry.adjacency source steps target) (input : Inference.Expr) (row : Row)
    (typed : Core.PresenceGeneration.Typing model environment input ((registry.endpoint source).eval model assignment, row)) :
    Core.PresenceGeneration.Typing model environment (compileSteps registry source steps input)
      ((registry.endpoint target).eval model assignment, row) := by
  induction path generalizing input with
  | nil => exact typed
  | cons edge path ih => exact ih _ (let_body_typed registry assignment environment valid _ _ edge input row typed)

/-- The actual source generation discharges every original body obligation;
the returned actual route code preserves the input's whole row. -/
theorem generated_compile_typed (registry : Registry vertices α) (symbolic : SchemeEnv α)
    (environment : List (Binding model)) (assignment : α → Comp model)
    (related : EnvRel model assignment symbolic environment)
    (checked : (registry.generate symbolic).Models assignment)
    (source target : Fin vertices) (input code : Inference.Expr) (row : Row)
    (compiled : compile registry source target input = some code)
    (typed : Core.PresenceGeneration.Typing model environment input ((registry.endpoint source).eval model assignment, row)) :
    Core.PresenceGeneration.Typing model environment code ((registry.endpoint target).eval model assignment, row) := by
  have valid := (registry.generate_exact symbolic environment assignment related).mp checked
  obtain ⟨route, _, same⟩ := Option.map_eq_some_iff.mp compiled
  subst code
  exact steps_typed registry assignment environment valid source target route.steps route.valid input row typed

theorem generated_compile_pure (registry : Registry vertices α) (symbolic : SchemeEnv α)
    (environment : List (Binding model)) (assignment : α → Comp model)
    (related : EnvRel model assignment symbolic environment)
    (checked : (registry.generate symbolic).Models assignment)
    (source target : Fin vertices) (input code : Inference.Expr)
    (compiled : compile registry source target input = some code)
    (typed : Core.PresenceGeneration.Typing model environment input
      (Core.PresenceGeneration.Comp.pure model ((registry.endpoint source).eval model assignment))) :
    Core.PresenceGeneration.Typing model environment code
      (Core.PresenceGeneration.Comp.pure model ((registry.endpoint target).eval model assignment)) :=
  generated_compile_typed registry symbolic environment assignment related checked source target input code
    Common.rowEmpty compiled typed

/-- The compiled code is a real Core expression at the existing independent
presence Core interface. No public source entry is changed. -/
theorem generated_compile_core_typed (registry : Registry vertices α) (symbolic : SchemeEnv α)
    (environment : List (Binding model)) (assignment : α → Comp model)
    (related : EnvRel model assignment symbolic environment)
    (checked : (registry.generate symbolic).Models assignment)
    (source target : Fin vertices) (input code : Inference.Expr) (row : Row)
    (compiled : compile registry source target input = some code)
    (typed : Core.PresenceGeneration.Typing model environment input ((registry.endpoint source).eval model assignment, row)) :
    Core.Typing (Core.PresenceGeneration.CoreRules.model model)
      (environment.map Core.PresenceGeneration.CoreRules.binding) (Core.Required.embed code)
      ((registry.endpoint target).eval model assignment, row) :=
  Core.PresenceGeneration.CoreRules.preserved
    (generated_compile_typed registry symbolic environment assignment related checked source target input code row compiled typed)

end Yulang.CommonNominalCastSourceCode
