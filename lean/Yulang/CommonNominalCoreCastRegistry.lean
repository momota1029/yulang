import Yulang.CommonNominalCoreSource
import Yulang.CommonNominalCastSourceCode

/-!
# Original literal-bearing Core cast bodies and compiled Core source plans

Every original common Core body is retained, including literal payloads and
strict/named-case syntax. Its actual independent Common typing at pure
endpoints is equivalent to generated finite constraints. Route compilation
then emits actual Core lets, with the same captured environment and input row.
No external Plan, body bound or compatibility oracle is an input.

This concerns the original common Core judgment at Signature.empty and fixed
finite endpoint graphs. The feature extensions, full keep/parametric/structural
search and Common operational typed-plan interpretation remain separate.
-/

namespace Yulang.CommonNominalCoreCastRegistry

open CommonNominalCarrier
open Core.PresenceGeneration (Comp TyTerm CompTerm SchemeEnv Binding EnvRel)
open CommonNominalFieldTemplates (Formula)

structure Registry (vertices : Nat) (α : Type) where
  endpoint : Fin vertices → TyTerm α
  adjacency : FiniteReachability.Adj vertices
  body : Fin vertices → Fin vertices → Core.CommonSyntax.Term

def Registry.rename (registry : Registry vertices α) (rename : α → β) : Registry vertices β :=
  ⟨fun vertex => (registry.endpoint vertex).rename rename, registry.adjacency, registry.body⟩

def Registry.edges (registry : Registry vertices α) : List (Fin vertices × Fin vertices) :=
  (List.finRange vertices).flatMap fun first => (registry.adjacency first).map fun last => (first, last)

@[simp] theorem Registry.mem_edges (registry : Registry vertices α) (first last : Fin vertices) :
    (first, last) ∈ registry.edges ↔ last ∈ registry.adjacency first := by
  simp [Registry.edges]

def Registry.Valid (registry : Registry vertices α) (environment : List (Core.CommonSyntax.Binding model))
    (assignment : α → Comp model) : Prop :=
  ∀ first last, last ∈ registry.adjacency first →
    Core.CommonSyntax.Typing model
      (.mono (Core.PresenceGeneration.Comp.pure model ((registry.endpoint first).eval model assignment)) :: environment)
      (registry.body first last)
      (Core.PresenceGeneration.Comp.pure model ((registry.endpoint last).eval model assignment))

def Registry.bodyConstraint (registry : Registry vertices α) (environment : SchemeEnv α)
    (first last : Fin vertices) : Formula α :=
  .ordinary (Core.CommonSyntax.generateNominalCore
    (Core.PresenceGeneration.Scheme.mono (CompTerm.pure (registry.endpoint first)) :: environment)
    (registry.body first last) (CompTerm.pure (registry.endpoint last)))

def Registry.generate (registry : Registry vertices α) (environment : SchemeEnv α) : Formula α :=
  Formula.all (registry.edges.map fun edge => registry.bodyConstraint environment edge.1 edge.2)

/-- Every actual direct source body is checked at its original endpoints and
under the same captured environment. The result row is literally empty. -/
theorem Registry.generate_exact (registry : Registry vertices α) (symbolic : SchemeEnv α)
    (environment : List (Core.CommonSyntax.Binding model)) (source : List (Binding model))
    (assignment : α → Comp model)
    (actualRelated : Core.CommonSyntax.EnvRel model environment source)
    (symbolicRelated : EnvRel model assignment symbolic source) :
    (registry.generate symbolic).Models assignment ↔ registry.Valid environment assignment := by
  have bodyExact (first last : Fin vertices) :
      (registry.bodyConstraint symbolic first last).Models assignment ↔
      Core.CommonSyntax.Typing model
        (.mono (Core.PresenceGeneration.Comp.pure model ((registry.endpoint first).eval model assignment)) :: environment)
        (registry.body first last)
        (Core.PresenceGeneration.Comp.pure model ((registry.endpoint last).eval model assignment)) := by
    exact Core.CommonSyntax.generate_nominal_core_exact _ _ _ assignment _ _
      (actualRelated.mono _) (symbolicRelated.mono (CompTerm.pure (registry.endpoint first)))
  rw [Registry.generate, Formula.models_all]
  constructor
  · intro held first last edge
    exact (bodyExact first last).mp (held _ (List.mem_map.mpr
      ⟨(first, last), (registry.mem_edges first last).mpr edge, rfl⟩))
  · intro valid formula present
    obtain ⟨edge, edgePresent, rfl⟩ := List.mem_map.mp present
    exact (bodyExact edge.1 edge.2).mpr (valid _ _ ((registry.mem_edges _ _).mp edgePresent))

def Registry.lowered (registry : Registry vertices α) : CommonNominalSourceRegistry.Registry vertices α :=
  ⟨registry.endpoint, registry.adjacency, fun first last => Core.CommonSyntax.lower (registry.body first last)⟩

theorem Registry.valid_lowered (registry : Registry vertices α)
    (environment : List (Core.CommonSyntax.Binding model)) (source : List (Binding model))
    (assignment : α → Comp model) (related : Core.CommonSyntax.EnvRel model environment source)
    (valid : registry.Valid environment assignment) : registry.lowered.Valid source assignment := by
  intro first last edge
  have typed := valid first last edge
  exact (Core.CommonSyntax.nominal_lowering_exact _ (Core.CommonSyntax.typing_covered typed)
    (related.mono _) _).mp typed

def compileSteps (registry : Registry vertices α) : Fin vertices → List (Fin vertices) → Core.CommonSyntax.Term → Core.CommonSyntax.Term
  | _, [], input => input
  | source, next :: rest, input => compileSteps registry next rest (.letE none input (registry.body source next))

def compile (registry : Registry vertices α) (source target : Fin vertices) (input : Core.CommonSyntax.Term) :
    Option Core.CommonSyntax.Term :=
  (CommonCastRoutes.search registry.adjacency source target).map fun route => compileSteps registry source route.steps input

theorem compile_exact (registry : Registry vertices α) (source target : Fin vertices) (input : Core.CommonSyntax.Term) :
    (compile registry source target input).isSome = true ↔ FiniteReachability.Reach registry.adjacency [source] target := by
  simp only [compile, Option.isSome_map]
  exact CommonCastRoutes.search_exact registry.adjacency source target

/-- The original Core bodies, literal contents and lexical contexts are
unchanged; lowering the actual generated code commutes with route compilation. -/
theorem compile_steps_lowering (registry : Registry vertices α) (source : Fin vertices)
    (steps : List (Fin vertices)) (input : Core.CommonSyntax.Term) :
    Core.CommonSyntax.lower (compileSteps registry source steps input) =
      CommonNominalCastSourceCode.compileSteps registry.lowered source steps (Core.CommonSyntax.lower input) := by
  induction steps generalizing source input with
  | nil => rfl
  | cons next rest ih =>
      simpa only [compileSteps, CommonNominalCastSourceCode.compileSteps, Registry.lowered, Core.CommonSyntax.lower] using
        ih next (.letE none input (registry.body source next))

private theorem let_body_typed (registry : Registry vertices α) (assignment : α → Comp model)
    (environment : List (Core.CommonSyntax.Binding model)) (valid : registry.Valid environment assignment)
    (source target : Fin vertices) (edge : target ∈ registry.adjacency source)
    (input : Core.CommonSyntax.Term) (row : Row)
    (typed : Core.CommonSyntax.Typing model environment input ((registry.endpoint source).eval model assignment, row)) :
    Core.CommonSyntax.Typing model environment (.letE none input (registry.body source target))
      ((registry.endpoint target).eval model assignment, row) := by
  apply Core.CommonSyntax.Typing.letComputed typed (valid source target edge)
  refine ⟨subtype_refl _, ?_⟩
  intro occurrence present
  exact present.elim id False.elim

theorem steps_typed (registry : Registry vertices α) (assignment : α → Comp model)
    (environment : List (Core.CommonSyntax.Binding model)) (valid : registry.Valid environment assignment)
    (source target : Fin vertices) (steps : List (Fin vertices))
    (path : CommonCastRoutes.Edges registry.adjacency source steps target) (input : Core.CommonSyntax.Term) (row : Row)
    (typed : Core.CommonSyntax.Typing model environment input ((registry.endpoint source).eval model assignment, row)) :
    Core.CommonSyntax.Typing model environment (compileSteps registry source steps input)
      ((registry.endpoint target).eval model assignment, row) := by
  induction path generalizing input with
  | nil => exact typed
  | cons edge path ih => exact ih _ (let_body_typed registry assignment environment valid _ _ edge input row typed)

theorem generated_compile_typed (registry : Registry vertices α) (symbolic : SchemeEnv α)
    (environment : List (Core.CommonSyntax.Binding model)) (sourceEnvironment : List (Binding model))
    (assignment : α → Comp model)
    (actualRelated : Core.CommonSyntax.EnvRel model environment sourceEnvironment)
    (symbolicRelated : EnvRel model assignment symbolic sourceEnvironment)
    (checked : (registry.generate symbolic).Models assignment)
    (source target : Fin vertices) (input code : Core.CommonSyntax.Term) (row : Row)
    (compiled : compile registry source target input = some code)
    (typed : Core.CommonSyntax.Typing model environment input ((registry.endpoint source).eval model assignment, row)) :
    Core.CommonSyntax.Typing model environment code ((registry.endpoint target).eval model assignment, row) := by
  have valid := (registry.generate_exact symbolic environment sourceEnvironment assignment actualRelated symbolicRelated).mp checked
  obtain ⟨route, _, same⟩ := Option.map_eq_some_iff.mp compiled
  subst code
  exact steps_typed registry assignment environment valid source target route.steps route.valid input row typed

theorem generated_compile_pure (registry : Registry vertices α) (symbolic : SchemeEnv α)
    (environment : List (Core.CommonSyntax.Binding model)) (sourceEnvironment : List (Binding model))
    (assignment : α → Comp model)
    (actualRelated : Core.CommonSyntax.EnvRel model environment sourceEnvironment)
    (symbolicRelated : EnvRel model assignment symbolic sourceEnvironment)
    (checked : (registry.generate symbolic).Models assignment)
    (source target : Fin vertices) (input code : Core.CommonSyntax.Term)
    (compiled : compile registry source target input = some code)
    (typed : Core.CommonSyntax.Typing model environment input
      (Core.PresenceGeneration.Comp.pure model ((registry.endpoint source).eval model assignment))) :
    Core.CommonSyntax.Typing model environment code
      (Core.PresenceGeneration.Comp.pure model ((registry.endpoint target).eval model assignment)) :=
  generated_compile_typed registry symbolic environment sourceEnvironment assignment actualRelated symbolicRelated
    checked source target input code Common.rowEmpty compiled typed

end Yulang.CommonNominalCoreCastRegistry
