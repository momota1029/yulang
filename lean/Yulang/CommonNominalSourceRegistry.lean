import Yulang.CommonNominalFieldTemplates
import Yulang.CommonCastRoutes

/-!
# Finite constraints for actual Common source cast bodies

Registry vertices are symbolic endpoints in the full new Common carrier.
Every direct edge stores an actual source expression. Its generated formula
checks that expression, in the captured lexical environment plus the original
input binding, at the declared output with an empty immediate row.

Deferred boundaries generate finite disjunctions of actual subtype atoms and
computed finite-graph routes. No compatibility or body-typing oracle is an
input. This is the fixed-endpoint registry constraint bridge, not an algorithm
for all parametric/structural casts or an executable Common source evaluator.
-/

namespace Yulang.CommonNominalSourceRegistry

open CommonNominalCarrier
open Core.PresenceGeneration (Comp TyTerm CompTerm SchemeEnv Binding EnvRel)
open CommonNominalFieldTemplates (Term Formula)

structure Registry (vertices : Nat) (α : Type) where
  endpoint : Fin vertices → TyTerm α
  adjacency : FiniteReachability.Adj vertices
  body : Fin vertices → Fin vertices → Inference.Expr

def Registry.rename (registry : Registry vertices α) (rename : α → β) : Registry vertices β :=
  ⟨fun vertex => (registry.endpoint vertex).rename rename, registry.adjacency, registry.body⟩

def Registry.edges (registry : Registry vertices α) : List (Fin vertices × Fin vertices) :=
  (List.finRange vertices).flatMap fun first => (registry.adjacency first).map fun last => (first, last)

@[simp] theorem Registry.mem_edges (registry : Registry vertices α) (first last : Fin vertices) :
    (first, last) ∈ registry.edges ↔ last ∈ registry.adjacency first := by
  simp [Registry.edges]

def Registry.Valid (registry : Registry vertices α) (environment : List (Binding model))
    (assignment : α → Comp model) : Prop :=
  ∀ first last, last ∈ registry.adjacency first →
    Core.PresenceGeneration.Typing model
      (.mono (Core.PresenceGeneration.Comp.pure model ((registry.endpoint first).eval model assignment)) :: environment)
      (registry.body first last)
      (Core.PresenceGeneration.Comp.pure model ((registry.endpoint last).eval model assignment))

def Registry.bodyConstraint (registry : Registry vertices α) (environment : SchemeEnv α)
    (first last : Fin vertices) : Formula α :=
  .ordinary (Core.PresenceGeneration.generate
    (Core.PresenceGeneration.Scheme.mono (CompTerm.pure (registry.endpoint first)) :: environment)
    (registry.body first last) (CompTerm.pure (registry.endpoint last)))

def Registry.generate (registry : Registry vertices α) (environment : SchemeEnv α) : Formula α :=
  Formula.all (registry.edges.map fun edge => registry.bodyConstraint environment edge.1 edge.2)

/-- Every actual direct source body is checked at its original endpoints and
under the same captured environment. The result row is literally empty. -/
theorem Registry.generate_exact (registry : Registry vertices α) (symbolic : SchemeEnv α)
    (environment : List (Binding model)) (assignment : α → Comp model)
    (related : EnvRel model assignment symbolic environment) :
    (registry.generate symbolic).Models assignment ↔ registry.Valid environment assignment := by
  have bodyExact (first last : Fin vertices) :
      (registry.bodyConstraint symbolic first last).Models assignment ↔
      Core.PresenceGeneration.Typing model
        (.mono (Core.PresenceGeneration.Comp.pure model ((registry.endpoint first).eval model assignment)) :: environment)
        (registry.body first last)
        (Core.PresenceGeneration.Comp.pure model ((registry.endpoint last).eval model assignment)) := by
    exact Core.PresenceGeneration.generate_models_iff_typing model _ _ _ assignment _
      (related.mono (CompTerm.pure (registry.endpoint first)))
  rw [Registry.generate, Formula.models_all]
  constructor
  · intro held first last edge
    exact (bodyExact first last).mp (held _ (List.mem_map.mpr
      ⟨(first, last), (registry.mem_edges first last).mpr edge, rfl⟩))
  · intro valid formula present
    obtain ⟨edge, edgePresent, rfl⟩ := List.mem_map.mp present
    exact (bodyExact edge.1 edge.2).mpr (valid _ _ ((registry.mem_edges _ _).mp edgePresent))

/-- The independent boundary rule mentions the actual Common order and the
original registry graph. It does not mention generated constraints. -/
inductive Boundary (registry : Registry vertices α) (assignment : α → Comp model) : Ty → Ty → Prop where
  | keep : CommonNominalCarrier.Subtype source target → Boundary registry assignment source target
  | route (first last : Fin vertices) :
      Equivalent source ((registry.endpoint first).eval model assignment) →
      FiniteReachability.Reach registry.adjacency [first] last →
      Equivalent ((registry.endpoint last).eval model assignment) target →
      Boundary registry assignment source target

private def candidate (registry : Registry vertices α) (source target : Term α)
    (first last : Fin vertices) : Formula α :=
  if FiniteReachability.closure registry.adjacency [first] last then
    .and (Formula.tyEq source (.ordinary (registry.endpoint first)))
      (Formula.tyEq (.ordinary (registry.endpoint last)) target)
  else .ordinary .bot

private theorem candidate_exact (registry : Registry vertices α) (assignment : α → Comp model)
    (source target : Term α) (first last : Fin vertices) :
    (candidate registry source target first last).Models assignment ↔
      Equivalent (source.eval assignment) ((registry.endpoint first).eval model assignment) ∧
      FiniteReachability.Reach registry.adjacency [first] last ∧
      Equivalent ((registry.endpoint last).eval model assignment) (target.eval assignment) := by
  cases reached : FiniteReachability.closure registry.adjacency [first] last with
  | false =>
      have absent : ¬ FiniteReachability.Reach registry.adjacency [first] last := by
        intro path
        have accepted := (FiniteReachability.closure_exact registry.adjacency [first] last).mpr path
        simp [reached] at accepted
      simp [candidate, reached, absent, Formula.Models, Core.PresenceGeneration.Formula.Holds]
  | true =>
      have path := (FiniteReachability.closure_exact registry.adjacency [first] last).mp reached
      simp only [candidate, reached, ↓reduceIte, Formula.Models, Formula.models_tyEq, Term.eval]
      exact ⟨fun same => ⟨same.1, path, same.2⟩, fun same => ⟨same.1, same.2.2⟩⟩

def generateBoundary (registry : Registry vertices α) (source target : Term α) : Formula α :=
  .or (.tyLe source target)
    (Formula.any ((List.finRange vertices).flatMap fun first =>
      (List.finRange vertices).map fun last => candidate registry source target first last))

/-- Arbitrary unknown source and field templates, arbitrary endpoint values
of the full nominal/regular carrier, and computed finite routes. -/
theorem generate_boundary_exact (registry : Registry vertices α) (assignment : α → Comp model)
    (source target : Term α) :
    (generateBoundary registry source target).Models assignment ↔
      Boundary registry assignment (source.eval assignment) (target.eval assignment) := by
  have alternatives :
      (Formula.any ((List.finRange vertices).flatMap fun first =>
        (List.finRange vertices).map fun last => candidate registry source target first last)).Models assignment ↔
      ∃ first last,
        Equivalent (source.eval assignment) ((registry.endpoint first).eval model assignment) ∧
        FiniteReachability.Reach registry.adjacency [first] last ∧
        Equivalent ((registry.endpoint last).eval model assignment) (target.eval assignment) := by
    rw [Formula.models_any]
    constructor
    · rintro ⟨formula, present, held⟩
      obtain ⟨first, _, present⟩ := List.mem_flatMap.mp present
      obtain ⟨last, _, rfl⟩ := List.mem_map.mp present
      exact ⟨first, last, (candidate_exact registry assignment source target first last).mp held⟩
    · rintro ⟨first, last, valid⟩
      exact ⟨_, List.mem_flatMap.mpr ⟨first, List.mem_finRange first,
        List.mem_map.mpr ⟨last, List.mem_finRange last, rfl⟩⟩,
        (candidate_exact registry assignment source target first last).mpr valid⟩
  simp only [generateBoundary, Formula.Models, alternatives]
  constructor
  · rintro (keep | ⟨first, last, before, path, after⟩)
    · exact .keep keep
    · exact .route first last before path after
  · intro boundary
    cases boundary with
    | keep below => exact Or.inl below
    | route first last before path after => exact Or.inr ⟨first, last, before, path, after⟩

theorem boundary_rename (registry : Registry vertices α) (rename : α → β)
    (assignment : β → Comp model) (source target : Ty) :
    Boundary (registry.rename rename) assignment source target ↔
      Boundary registry (assignment ∘ rename) source target := by
  constructor
  · intro boundary
    cases boundary with
    | keep below => exact .keep below
    | route first last before path after =>
        exact .route first last
          (by simpa only [Registry.rename, TyTerm.eval_rename] using before) path
          (by simpa only [Registry.rename, TyTerm.eval_rename] using after)
  · intro boundary
    cases boundary with
    | keep below => exact .keep below
    | route first last before path after =>
        exact .route first last
          (by simpa only [Registry.rename, TyTerm.eval_rename] using before) path
          (by simpa only [Registry.rename, TyTerm.eval_rename] using after)

theorem Registry.valid_rename (registry : Registry vertices α) (rename : α → β)
    (environment : List (Binding model)) (assignment : β → Comp model) :
    (registry.rename rename).Valid environment assignment ↔ registry.Valid environment (assignment ∘ rename) := by
  simp only [Registry.Valid, Registry.rename, TyTerm.eval_rename]

end Yulang.CommonNominalSourceRegistry
