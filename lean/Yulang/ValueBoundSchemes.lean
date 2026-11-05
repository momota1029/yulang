import Yulang.ValueUpperBounds

/-!
# Constraint-free schemes for every solution of a value-bound graph

Minimizing every unknown loses instances when an output has negative
occurrences. Maximizing every unknown has the dual problem. This module
instead constructs a finite, unconstrained type expression for each unknown,
retaining shared parameters in mixed positions.

Write `L i` for the propagated lower union and `U i` for the propagated upper
intersection. For arbitrary free parameters `p`, the constructed assignment is

    L i | union { p j & U j | j reaches i }.

If the problem is satisfiable, every such assignment is a model. Conversely,
substituting any original model for `p` reproduces that model up to mutual
subtyping. Consequently the construction preserves the entire instance family
of any output that respects mutual subtyping, with no polarity restriction.

This is a constructive elimination of the existing flat bound constraints,
not an enumeration of candidate types. Bounds can be arbitrary finite
structural types. Unknowns nested inside bounds and recursive value types are
handled by separate solver layers.
-/

namespace Yulang.ValueBoundSchemes

open StructuralBase ValueBounds

universe u

variable {n : Nat} {RowType : Type u}

/-- The result contains free parameters and type syntax, with no residual
inequality constraints or predicates to be discharged at instantiation. -/
inductive Term (n : Nat) (RowType : Type u) where
  | ground (type : Ty RowType)
  | parameter (index : Fin n)
  | union (left right : Term n RowType)
  | inter (left right : Term n RowType)

def Term.eval (parameters : Valuation n RowType) : Term n RowType → Ty RowType
  | .ground type => type
  | .parameter index => parameters index
  | .union left right => .union (left.eval parameters) (right.eval parameters)
  | .inter left right => .inter (left.eval parameters) (right.eval parameters)

abbrev Scheme (n : Nat) (RowType : Type u) := Fin n → Term n RowType

def instantiate (scheme : Scheme n RowType) (parameters : Valuation n RowType) :
    Valuation n RowType := fun index => (scheme index).eval parameters

def ancestors (problem : Problem n RowType) (target : Fin n) : List (Fin n) :=
  (List.finRange n).filter fun source => target ∈ reachable problem source

theorem mem_ancestors (problem : Problem n RowType) (source target : Fin n) :
    source ∈ ancestors problem target ↔ Reaches problem source target := by
  simp only [ancestors, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq, reachable_exact]

def variablePart (problem : Problem n RowType) (parameters : Valuation n RowType)
    (target : Fin n) : Ty RowType :=
  joinTypes ((ancestors problem target).map fun source =>
    .inter (parameters source) (ValueUpperBounds.greatest problem source))

def expand (problem : Problem n RowType) (parameters : Valuation n RowType) :
    Valuation n RowType :=
  fun target => .union (least problem target) (variablePart problem parameters target)

def joinTerms : List (Term n RowType) → Term n RowType
  | [] => .ground .bottom
  | term :: rest => .union term (joinTerms rest)

theorem joinTerms_eval (parameters : Valuation n RowType) (terms : List (Term n RowType)) :
    (joinTerms terms).eval parameters = joinTypes (terms.map (Term.eval parameters)) := by
  induction terms with
  | nil => rfl
  | cons term rest ih => simp only [joinTerms, Term.eval, List.map, joinTypes, ih]

/-- Executable construction of the unconstrained shared-parameter scheme. -/
def coalesce (problem : Problem n RowType) : Scheme n RowType :=
  fun target => .union (.ground (least problem target))
    (joinTerms ((ancestors problem target).map fun source =>
      .inter (.parameter source) (.ground (ValueUpperBounds.greatest problem source))))

theorem instantiate_coalesce (problem : Problem n RowType)
    (parameters : Valuation n RowType) :
    instantiate (coalesce problem) parameters = expand problem parameters := by
  funext target
  simp only [instantiate, coalesce, Term.eval, joinTerms_eval, List.map_map,
    Function.comp_def, expand, variablePart]

theorem variablePart_le_iff (leRow : RowType → RowType → Prop)
    (problem : Problem n RowType) (parameters : Valuation n RowType)
    (target : Fin n) (upper : Ty RowType) :
    Subtype leRow (variablePart problem parameters target) upper ↔
      ∀ source, Reaches problem source target →
        Subtype leRow (.inter (parameters source) (ValueUpperBounds.greatest problem source))
          upper := by
  simp only [variablePart, joinTypes_le_iff, List.forall_mem_map, mem_ancestors]

theorem contribution_below (leRow : RowType → RowType → Prop)
    (problem : Problem n RowType) (parameters : Valuation n RowType)
    (source target : Fin n) (path : Reaches problem source target) :
    Subtype leRow (.inter (parameters source) (ValueUpperBounds.greatest problem source))
      (variablePart problem parameters target) :=
  (variablePart_le_iff leRow problem parameters target _).mp (.refl _) source path

theorem variablePart_flow (leRow : RowType → RowType → Prop)
    (problem : Problem n RowType) (parameters : Valuation n RowType)
    (source target : Fin n) (edge : .flow source target ∈ problem) :
    Subtype leRow (variablePart problem parameters source) (variablePart problem parameters target) := by
  apply (variablePart_le_iff leRow problem parameters source _).mpr
  intro start path
  exact contribution_below leRow problem parameters start target
    (path.append (.cons ((mem_successors problem source target).mpr edge) (.nil target)))

theorem expand_lower (leRow : RowType → RowType → Prop)
    (problem : Problem n RowType) (parameters : Valuation n RowType)
    (type : Ty RowType) (target : Fin n) (bound : .lower type target ∈ problem) :
    Subtype leRow type (expand problem parameters target) :=
  .trans (least_lower leRow problem type target bound) (.unionLeft _ _)

theorem expand_flow (leRow : RowType → RowType → Prop)
    (problem : Problem n RowType) (parameters : Valuation n RowType)
    (source target : Fin n) (edge : .flow source target ∈ problem) :
    Subtype leRow (expand problem parameters source) (expand problem parameters target) :=
  union_mono (least_flow leRow problem source target edge)
    (variablePart_flow leRow problem parameters source target edge)

/-- Every free-parameter assignment is a solution as soon as the finite
ground consistency check succeeds. No bound is rechecked at instantiation. -/
theorem expand_models {leRow : RowType → RowType → Prop}
    {problem : Problem n RowType} (consistent : Models leRow problem (least problem))
    (parameters : Valuation n RowType) : Models leRow problem (expand problem parameters) := by
  intro constraint member
  cases constraint with
  | lower type target => exact expand_lower leRow problem parameters type target member
  | flow source target => exact expand_flow leRow problem parameters source target member
  | upper source type =>
      apply Subtype.unionElim (consistent (.upper source type) member)
      apply (variablePart_le_iff leRow problem parameters source type).mpr
      intro start path
      exact .trans (.interRight _ _)
        (.trans (ValueUpperBounds.reaches_subtype
          (ValueUpperBounds.greatest_upperModels leRow problem) path)
          (ValueUpperBounds.greatest_upper leRow problem source type member))
  | check source target => exact consistent _ member

def Equivalent (leRow : RowType → RowType → Prop) (left right : Ty RowType) : Prop :=
  Subtype leRow left right ∧ Subtype leRow right left

def PointwiseEquivalent (leRow : RowType → RowType → Prop)
    (left right : Valuation n RowType) : Prop :=
  ∀ index, Equivalent leRow (left index) (right index)

/-- Choosing an existing model as the free parameters recovers it. This is
the constructive surjectivity needed for all-instance completeness. -/
theorem expand_equivalent {leRow : RowType → RowType → Prop}
    {problem : Problem n RowType} {value : Valuation n RowType}
    (model : Models leRow problem value) :
    PointwiseEquivalent leRow (expand problem value) value := by
  intro target
  constructor
  · apply Subtype.unionElim (least_below model.lower target)
    apply (variablePart_le_iff leRow problem value target _).mpr
    intro source path
    exact .trans (.interLeft _ _) (ValueBounds.reaches_subtype model.lower path)
  · exact .trans (.interIntro (.refl _) (ValueUpperBounds.greatest_above
        (ValueUpperBounds.models_upper model) target))
      (.trans (contribution_below leRow problem value target target (.nil target))
        (.unionRight _ _))

theorem models_equivalent {leRow : RowType → RowType → Prop}
    {problem : Problem n RowType} {left right : Valuation n RowType}
    (model : Models leRow problem left) (equivalent : PointwiseEquivalent leRow left right) :
    Models leRow problem right := by
  intro constraint member
  cases constraint with
  | lower type target => exact .trans (model _ member) (equivalent target).1
  | flow source target =>
      exact .trans (equivalent source).2 (.trans (model _ member) (equivalent target).1)
  | upper source type => exact .trans (equivalent source).2 (model _ member)
  | check source target => exact model _ member

/-- The check computes satisfiability; the result is syntax with shared free
parameters. The choice of parameters never influences this check. -/
def solve (typeCheck : Ty RowType → Ty RowType → Bool) (problem : Problem n RowType) :
    Option (Scheme n RowType) :=
  (ValueBounds.solve typeCheck problem).map fun _ => coalesce problem

theorem solve_some_iff (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problem : Problem n RowType) (scheme : Scheme n RowType) :
    solve typeCheck problem = some scheme ↔
      scheme = coalesce problem ∧ Models leRow problem (least problem) := by
  simp only [solve, Option.map_eq_some_iff]
  constructor
  · rintro ⟨value, solved, same⟩
    obtain ⟨rfl, model⟩ := (ValueBounds.solve_some_iff typeCheck typeExact problem value).mp solved
    exact ⟨same.symm, model⟩
  · rintro ⟨rfl, model⟩
    exact ⟨least problem,
      (ValueBounds.solve_some_iff typeCheck typeExact problem _).mpr ⟨rfl, model⟩, rfl⟩

theorem solve_none_iff (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problem : Problem n RowType) :
    solve typeCheck problem = none ↔ ¬ ∃ value, Models leRow problem value := by
  simp only [solve, Option.map_eq_none_iff, ValueBounds.solve_none_iff typeCheck typeExact]

theorem solve_instantiates_model (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    {problem : Problem n RowType} {scheme : Scheme n RowType}
    (solved : solve typeCheck problem = some scheme) (parameters : Valuation n RowType) :
    Models leRow problem (instantiate scheme parameters) := by
  obtain ⟨rfl, model⟩ := (solve_some_iff typeCheck typeExact problem scheme).mp solved
  rw [instantiate_coalesce]
  exact expand_models model parameters

/-- The computed scheme represents exactly all models, up to the existing
structural equivalence. The right side has no remaining constraint predicate. -/
theorem solve_models_exact (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problem : Problem n RowType) (value : Valuation n RowType) :
    Models leRow problem value ↔
      ∃ scheme, solve typeCheck problem = some scheme ∧
        ∃ parameters, PointwiseEquivalent leRow (instantiate scheme parameters) value := by
  constructor
  · intro model
    refine ⟨coalesce problem, ?_, value, ?_⟩
    · exact (solve_some_iff typeCheck typeExact problem _).mpr
        ⟨rfl, least_models_of_models model⟩
    · rw [instantiate_coalesce]
      exact expand_equivalent model
  · rintro ⟨scheme, solved, parameters, equivalent⟩
    exact models_equivalent (solve_instantiates_model typeCheck typeExact solved parameters) equivalent

def Congruent (leRow : RowType → RowType → Prop)
    (output : Valuation n RowType → Ty RowType) : Prop :=
  ∀ left right, PointwiseEquivalent leRow left right →
    Equivalent leRow (output left) (output right)

/-- Principal instance equality for arbitrary mixed positive/negative
outputs. Shared parameters preserve input/output correlations. -/
theorem principal_exact (typeCheck : Ty RowType → Ty RowType → Bool)
    {leRow : RowType → RowType → Prop}
    (typeExact : ∀ left right, typeCheck left right = true ↔ Subtype leRow left right)
    (problem : Problem n RowType) (output : Valuation n RowType → Ty RowType)
    (congruent : Congruent leRow output) (expected : Ty RowType) :
    (∃ scheme, solve typeCheck problem = some scheme ∧
      ∃ parameters, Subtype leRow (output (instantiate scheme parameters)) expected) ↔
    ∃ value, Models leRow problem value ∧ Subtype leRow (output value) expected := by
  constructor
  · rintro ⟨scheme, solved, parameters, below⟩
    exact ⟨instantiate scheme parameters,
      solve_instantiates_model typeCheck typeExact solved parameters, below⟩
  · rintro ⟨value, model, below⟩
    refine ⟨coalesce problem, ?_, value, ?_⟩
    · exact (solve_some_iff typeCheck typeExact problem _).mpr
        ⟨rfl, least_models_of_models model⟩
    · rw [instantiate_coalesce]
      exact .trans (congruent _ _ (expand_equivalent model)).1 below

end Yulang.ValueBoundSchemes
