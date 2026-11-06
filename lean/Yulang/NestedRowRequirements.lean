import Yulang.NestedValueSolver
import Yulang.RowFlowSchemes

/-!
# Separating nested constructor saturation from symbolic row requirements

Changing the row representation of a nested graph preserves its constructor
rules, variable rules, and exact saturated cache. Rows affect only the final
arrow-obligation checks. The finite emitted row list contains every such
obligation of every saturated edge, including reversed arrow input rows.

A shape-only successful cache and a model of the emitted row constraints are
therefore exactly a successful run at that row assignment. Composing this
fact with the shared-parameter row-flow solver yields successful nested runs
for arbitrary free row parameters; parameters retain their shared identities.
Unsupported row syntax remains distinct from a rigid constructor mismatch.
-/

namespace Yulang.NestedRowRequirements

open NestedValueSolver

universe u v w

variable {n m : Nat} {Row : Type u} {Target : Type v} {Final : Type w}

def mapPair (map : Row → Target) (pair : Row × Row) : Target × Target :=
  (map pair.1, map pair.2)

def nodeMapRows (map : Row → Target) : Node n Row → Node n Target
  | .var => .var
  | .bottom => .bottom
  | .top => .top
  | .base scalar => .base scalar
  | .pair left right => .pair left right
  | .arrow input inputRow output outputRow => .arrow input (map inputRow) output (map outputRow)
  | .record fields => .record fields
  | .variant label payload => .variant label payload

def mapRows (map : Row → Target) (graph : Graph n Row) : Graph n Target :=
  fun index => nodeMapRows map (graph index)

@[simp] theorem nodeMapRows_id (node : Node n Row) : nodeMapRows id node = node := by
  cases node <;> rfl

@[simp] theorem nodeMapRows_comp (first : Row → Target) (last : Target → Final) (node : Node n Row) :
    nodeMapRows last (nodeMapRows first node) = nodeMapRows (last ∘ first) node := by
  cases node <;> rfl

@[simp] theorem mapRows_id (graph : Graph n Row) : mapRows id graph = graph := by
  funext index
  exact nodeMapRows_id _

@[simp] theorem mapRows_comp (first : Row → Target) (last : Target → Final) (graph : Graph n Row) :
    mapRows last (mapRows first graph) = mapRows (last ∘ first) graph := by
  funext index
  exact nodeMapRows_comp first last _

@[simp] theorem nodeMapRows_isVariable (map : Row → Target) (node : Node n Row) :
    nodeMapRows map node = .var ↔ node = .var := by
  cases node <;> simp [nodeMapRows]

def mapRequirements (map : Row → Target) (requirements : Requirements n Row) : Requirements n Target :=
  { types := requirements.types, rows := requirements.rows.map (mapPair map) }

/-- All child type obligations are identical; only the two arrow rows are mapped. -/
theorem inspect_mapRows (map : Row → Target) (source target : Node n Row) :
    inspect (nodeMapRows map source) (nodeMapRows map target) =
      (inspect source target).map (mapRequirements map) := by
  cases source <;> cases target <;>
    simp [nodeMapRows, inspect, mapRequirements, mapPair]

theorem constructorRules_mapRows (map : Row → Target) (graph : Graph n Row) (edge : Edge n) :
    constructorRules (mapRows map graph) edge = constructorRules graph edge := by
  simp only [constructorRules, mapRows, inspect_mapRows]
  cases inspect (graph edge.1) (graph edge.2) <;> rfl

theorem variableRules_mapRows (map : Row → Target) (graph : Graph n Row) (pivot : Fin n) :
    variableRules (mapRows map graph) pivot = variableRules graph pivot := by
  simp only [variableRules, mapRows]
  cases graph pivot <;> rfl

theorem rules_mapRows (map : Row → Target) (graph : Graph n Row) (constraints : List (Edge n)) :
    rules (mapRows map graph) constraints = rules graph constraints := by
  have constructors : constructorRules (mapRows map graph) = constructorRules graph :=
    funext (constructorRules_mapRows map graph)
  have variables : variableRules (mapRows map graph) = variableRules graph :=
    funext (variableRules_mapRows map graph)
  simp only [rules, constructors, variables]

/-- Row instantiation preserves the actual cache data and its order. -/
theorem saturate_mapRows (map : Row → Target) (graph : Graph n Row) (constraints : List (Edge n)) :
    saturate (mapRows map graph) constraints = saturate graph constraints := by
  simp only [saturate, rules_mapRows]

theorem closed_mapRows_iff (map : Row → Target) (graph : Graph n Row) (constraints cache : List (Edge n)) :
    Closed (mapRows map graph) constraints cache ↔ Closed graph constraints cache := by
  constructor
  · rintro ⟨seeds, constructors, variables⟩
    refine ⟨seeds, ?_, ?_⟩
    · intro edge present requirements inspected child member
      apply constructors edge present (mapRequirements map requirements) _ child member
      simp only [mapRows, inspect_mapRows, inspected, Option.map_some]
    · intro pivot isVariable source target lower upper
      apply variables pivot _ source target lower upper
      exact (nodeMapRows_isVariable map (graph pivot)).mpr isVariable
  · rintro ⟨seeds, constructors, variables⟩
    refine ⟨seeds, ?_, ?_⟩
    · intro edge present requirements inspected child member
      simp only [mapRows, inspect_mapRows] at inspected
      cases found : inspect (graph edge.1) (graph edge.2) with
      | none => simp [found] at inspected
      | some original =>
          rw [found] at inspected
          have same : mapRequirements map original = requirements := Option.some.inj inspected
          subst requirements
          exact constructors edge present original found child member
    · intro pivot isVariable source target lower upper
      exact variables pivot ((nodeMapRows_isVariable map (graph pivot)).mp isVariable) source target lower upper

def rowsOf : Option (Requirements n Row) → List (Row × Row)
  | none => []
  | some requirements => requirements.rows

def rowRequirements (graph : Graph n Row) (cache : List (Edge n)) : List (Row × Row) :=
  cache.flatMap fun edge => rowsOf (inspect (graph edge.1) (graph edge.2))

theorem mem_rowRequirements (graph : Graph n Row) (cache : List (Edge n)) (row : Row × Row) :
    row ∈ rowRequirements graph cache ↔
      ∃ edge ∈ cache, ∃ requirements,
        inspect (graph edge.1) (graph edge.2) = some requirements ∧ row ∈ requirements.rows := by
  simp only [rowRequirements, List.mem_flatMap]
  constructor
  · rintro ⟨edge, present, member⟩
    cases inspected : inspect (graph edge.1) (graph edge.2) with
    | none => simp [inspected, rowsOf] at member
    | some requirements =>
        exact ⟨edge, present, requirements, inspected, by simpa only [inspected, rowsOf] using member⟩
  · rintro ⟨edge, present, requirements, inspected, member⟩
    exact ⟨edge, present, by simpa only [inspected, rowsOf] using member⟩

theorem rowsOf_map (map : Row → Target) (inspection : Option (Requirements n Row)) :
    rowsOf (inspection.map (mapRequirements map)) = (rowsOf inspection).map (mapPair map) := by
  cases inspection <;> rfl

theorem rowRequirements_mapRows (map : Row → Target) (graph : Graph n Row) (cache : List (Edge n)) :
    rowRequirements (mapRows map graph) cache = (rowRequirements graph cache).map (mapPair map) := by
  simp only [rowRequirements, mapRows, inspect_mapRows, rowsOf_map, List.map_flatMap]

def shapeCheck (_ _ : Row) : Bool := true

theorem inspectionAccepted_map_iff (map : Row → Target) (rowCheck : Target → Target → Bool)
    (inspection : Option (Requirements n Row)) :
    inspectionAccepted rowCheck (inspection.map (mapRequirements map)) = true ↔
      inspectionAccepted shapeCheck inspection = true ∧
        ∀ row ∈ rowsOf inspection, rowCheck (map row.1) (map row.2) = true := by
  cases inspection <;> simp [inspectionAccepted, mapRequirements, rowsOf, shapeCheck, mapPair, List.all_map]

/-- Constructor mismatch checking and all emitted row obligations together
are exactly the original nested consistency test at a row assignment. -/
theorem consistent_mapRows_iff (map : Row → Target) (rowCheck : Target → Target → Bool)
    (graph : Graph n Row) (cache : List (Edge n)) :
    consistent rowCheck (mapRows map graph) cache = true ↔
      consistent shapeCheck graph cache = true ∧
        ∀ row ∈ rowRequirements graph cache, rowCheck (map row.1) (map row.2) = true := by
  simp only [consistent, List.all_eq_true, mapRows, inspect_mapRows, inspectionAccepted_map_iff]
  constructor
  · intro accepted
    refine ⟨fun edge member => (accepted edge member).1, ?_⟩
    intro row member
    obtain ⟨edge, present, member⟩ := List.mem_flatMap.mp member
    exact (accepted edge present).2 row member
  · rintro ⟨shape, rows⟩ edge member
    refine ⟨shape edge member, ?_⟩
    intro row present
    exact rows row (List.mem_flatMap.mpr ⟨edge, member, present⟩)

theorem shape_consistent_mapRows_iff (map : Row → Target) (graph : Graph n Row) (cache : List (Edge n)) :
    consistent shapeCheck (mapRows map graph) cache = true ↔ consistent shapeCheck graph cache = true := by
  simpa only [shapeCheck, implies_true, and_true] using consistent_mapRows_iff map shapeCheck graph cache

/-- Shape saturation is reusable verbatim for each row parameter assignment. -/
theorem solve_mapRows_iff (map : Row → Target) (rowCheck : Target → Target → Bool)
    (graph : Graph n Row) (constraints cache : List (Edge n)) :
    solve rowCheck (mapRows map graph) constraints = some cache ↔
      solve shapeCheck graph constraints = some cache ∧
        ∀ row ∈ rowRequirements graph cache, rowCheck (map row.1) (map row.2) = true := by
  rw [solve_some_iff, saturate_mapRows, consistent_mapRows_iff, solve_some_iff]
  exact and_assoc.symm

theorem shape_rejection_preserved (map : Row → Target) (rowCheck : Target → Target → Bool)
    (graph : Graph n Row) (constraints : List (Edge n))
    (rejected : solve shapeCheck graph constraints = none) :
    solve rowCheck (mapRows map graph) constraints = none := by
  cases found : solve rowCheck (mapRows map graph) constraints with
  | none => rfl
  | some cache =>
      have accepted := ((solve_mapRows_iff map rowCheck graph constraints cache).mp found).1
      rw [rejected] at accepted
      cases accepted

/-! ## Joint row generation and shared-parameter row solving -/

abbrev SymbolicGraph (n m : Nat) := Graph n (Inference.RowTerm (Fin m))

def instantiateGraph (algebra : RowFlowSchemes.Algebra Row) (rows : Fin m → Row)
    (graph : SymbolicGraph n m) : Graph n Row :=
  mapRows (RowFlowSchemes.eval algebra rows) graph

def jointProblem (explicitRows : RowFlowSchemes.Problem m) (graph : SymbolicGraph n m)
    (cache : List (Edge n)) : RowFlowSchemes.Problem m :=
  explicitRows ++ rowRequirements graph cache

theorem rowModels_append (algebra : RowFlowSchemes.Algebra Row) (rows : Fin m → Row)
    (left right : RowFlowSchemes.Problem m) :
    RowFlowSchemes.Models algebra (left ++ right) rows ↔
      RowFlowSchemes.Models algebra left rows ∧ RowFlowSchemes.Models algebra right rows := by
  simp only [RowFlowSchemes.Models, List.mem_append, or_imp, forall_and]

theorem solve_at_rows_iff (algebra : RowFlowSchemes.Algebra Row)
    (rowCheck : Row → Row → Bool)
    (rowExact : ∀ left right, rowCheck left right = true ↔ algebra.le left right)
    (graph : SymbolicGraph n m) (constraints cache : List (Edge n))
    (shapeSolved : solve shapeCheck graph constraints = some cache) (rows : Fin m → Row) :
    solve rowCheck (instantiateGraph algebra rows graph) constraints = some cache ↔
      RowFlowSchemes.Models algebra (rowRequirements graph cache) rows := by
  rw [instantiateGraph, solve_mapRows_iff]
  simp only [shapeSolved, true_and, RowFlowSchemes.Models, RowFlowSchemes.Constraint.Holds, rowExact]

/-- The emitted constraints are necessary and sufficient at every original
row assignment. This statement also applies before checking supported syntax. -/
theorem joint_models_iff (algebra : RowFlowSchemes.Algebra Row)
    (rowCheck : Row → Row → Bool)
    (rowExact : ∀ left right, rowCheck left right = true ↔ algebra.le left right)
    (graph : SymbolicGraph n m) (constraints cache : List (Edge n))
    (shapeSolved : solve shapeCheck graph constraints = some cache)
    (explicitRows : RowFlowSchemes.Problem m) (rows : Fin m → Row) :
    RowFlowSchemes.Models algebra (jointProblem explicitRows graph cache) rows ↔
      RowFlowSchemes.Models algebra explicitRows rows ∧
        solve rowCheck (instantiateGraph algebra rows graph) constraints = some cache := by
  rw [jointProblem, rowModels_append, solve_at_rows_iff algebra rowCheck rowExact graph constraints cache shapeSolved]

/-- Every free row-parameter assignment gives the same successful nested
cache and satisfies the explicit source-row constraints. -/
theorem rowScheme_solves (algebra : RowFlowSchemes.Algebra Row)
    (rowCheck : Row → Row → Bool)
    (rowExact : ∀ left right, rowCheck left right = true ↔ algebra.le left right)
    (graph : SymbolicGraph n m) (constraints cache : List (Edge n))
    (shapeSolved : solve shapeCheck graph constraints = some cache)
    (explicitRows : RowFlowSchemes.Problem m) (scheme : RowFlowSchemes.Scheme m)
    (rowSolved : RowFlowSchemes.solve (jointProblem explicitRows graph cache) = .solved scheme)
    (parameter : Fin m → Row) :
    RowFlowSchemes.Models algebra explicitRows (RowFlowSchemes.instantiate algebra scheme parameter) ∧
      solve rowCheck (instantiateGraph algebra (RowFlowSchemes.instantiate algebra scheme parameter) graph)
        constraints = some cache :=
  (joint_models_iff algebra rowCheck rowExact graph constraints cache shapeSolved explicitRows _).mp
    (RowFlowSchemes.solve_instantiates_model algebra _ scheme rowSolved parameter)

/-- When the row order is antisymmetric, model recovery is literal equality.
This optional law avoids changing row representations in later value proofs. -/
theorem rowScheme_retraction (algebra : RowFlowSchemes.Algebra Row)
    (antisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (problem : RowFlowSchemes.Problem m) (scheme : RowFlowSchemes.Scheme m)
    (solved : RowFlowSchemes.solve problem = .solved scheme) (rows : Fin m → Row)
    (model : RowFlowSchemes.Models algebra problem rows) :
    RowFlowSchemes.instantiate algebra scheme rows = rows := by
  obtain ⟨rfl, supported⟩ := (RowFlowSchemes.solve_solved_iff problem scheme).mp solved
  rw [RowFlowSchemes.instantiate_coalesce]
  have equivalent := RowFlowSchemes.expand_equivalent algebra
    ((RowFlowSchemes.flatten_models_iff algebra problem supported rows).mpr model)
  funext index
  exact antisymm (equivalent index).1 (equivalent index).2

theorem rowScheme_models_exact_eq (algebra : RowFlowSchemes.Algebra Row)
    (antisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (problem : RowFlowSchemes.Problem m) (scheme : RowFlowSchemes.Scheme m)
    (solved : RowFlowSchemes.solve problem = .solved scheme) (rows : Fin m → Row) :
    RowFlowSchemes.Models algebra problem rows ↔
      ∃ parameter, RowFlowSchemes.instantiate algebra scheme parameter = rows := by
  constructor
  · intro model
    exact ⟨rows, rowScheme_retraction algebra antisymm problem scheme solved rows model⟩
  · rintro ⟨parameter, rfl⟩
    exact RowFlowSchemes.solve_instantiates_model algebra problem scheme solved parameter

inductive Result (n m : Nat) where
  | unsupported
  | rejected
  | solved (cache : List (Edge n)) (rowScheme : RowFlowSchemes.Scheme m)

/-- Run constructor saturation once, collect every generated arrow-row
obligation, then construct a finite shared-parameter row scheme. -/
def solveRows (graph : SymbolicGraph n m) (constraints : List (Edge n))
    (explicitRows : RowFlowSchemes.Problem m) : Result n m :=
  match solve shapeCheck graph constraints with
  | none => .rejected
  | some cache =>
      match RowFlowSchemes.solve (jointProblem explicitRows graph cache) with
      | .unsupported => .unsupported
      | .solved scheme => .solved cache scheme

theorem solveRows_solved_iff (graph : SymbolicGraph n m) (constraints cache : List (Edge n))
    (explicitRows : RowFlowSchemes.Problem m) (scheme : RowFlowSchemes.Scheme m) :
    solveRows graph constraints explicitRows = .solved cache scheme ↔
      solve shapeCheck graph constraints = some cache ∧
        RowFlowSchemes.solve (jointProblem explicitRows graph cache) = .solved scheme := by
  unfold solveRows
  cases shapeFound : solve shapeCheck graph constraints with
  | none => simp
  | some actual =>
      simp only
      cases rowsFound : RowFlowSchemes.solve (jointProblem explicitRows graph actual) with
      | unsupported =>
          constructor
          · intro impossible; cases impossible
          · rintro ⟨same, found⟩
            have equal := Option.some.inj same
            subst actual
            rw [rowsFound] at found
            cases found
      | solved actualScheme =>
          constructor
          · intro same
            cases same
            exact ⟨rfl, rowsFound⟩
          · rintro ⟨same, found⟩
            have equal := Option.some.inj same
            subst actual
            rw [rowsFound] at found
            cases found
            rfl

theorem solveRows_rejected_iff (graph : SymbolicGraph n m) (constraints : List (Edge n))
    (explicitRows : RowFlowSchemes.Problem m) :
    solveRows graph constraints explicitRows = .rejected ↔ solve shapeCheck graph constraints = none := by
  unfold solveRows
  cases shapeFound : solve shapeCheck graph constraints with
  | none => simp
  | some cache =>
      simp only
      cases RowFlowSchemes.solve (jointProblem explicitRows graph cache) <;> simp

theorem solveRows_unsupported_iff (graph : SymbolicGraph n m) (constraints : List (Edge n))
    (explicitRows : RowFlowSchemes.Problem m) :
    solveRows graph constraints explicitRows = .unsupported ↔
      ∃ cache, solve shapeCheck graph constraints = some cache ∧
        RowFlowSchemes.solve (jointProblem explicitRows graph cache) = .unsupported := by
  unfold solveRows
  cases shapeFound : solve shapeCheck graph constraints with
  | none => simp
  | some cache =>
      simp only
      cases found : RowFlowSchemes.solve (jointProblem explicitRows graph cache) <;> simp [found]

theorem solveRows_instantiates (algebra : RowFlowSchemes.Algebra Row)
    (rowCheck : Row → Row → Bool)
    (rowExact : ∀ left right, rowCheck left right = true ↔ algebra.le left right)
    (graph : SymbolicGraph n m) (constraints cache : List (Edge n))
    (explicitRows : RowFlowSchemes.Problem m) (scheme : RowFlowSchemes.Scheme m)
    (solved : solveRows graph constraints explicitRows = .solved cache scheme) (parameter : Fin m → Row) :
    RowFlowSchemes.Models algebra explicitRows (RowFlowSchemes.instantiate algebra scheme parameter) ∧
      solve rowCheck (instantiateGraph algebra (RowFlowSchemes.instantiate algebra scheme parameter) graph)
        constraints = some cache := by
  obtain ⟨shapeSolved, rowSolved⟩ := (solveRows_solved_iff graph constraints cache explicitRows scheme).mp solved
  exact rowScheme_solves algebra rowCheck rowExact graph constraints cache shapeSolved explicitRows scheme rowSolved parameter

/-- Accepted joint row schemes represent all original row assignments which
satisfy the explicit rows and return the same nested constructor cache. -/
theorem solveRows_models_exact_eq (algebra : RowFlowSchemes.Algebra Row)
    (antisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (rowCheck : Row → Row → Bool)
    (rowExact : ∀ left right, rowCheck left right = true ↔ algebra.le left right)
    (graph : SymbolicGraph n m) (constraints cache : List (Edge n))
    (explicitRows : RowFlowSchemes.Problem m) (scheme : RowFlowSchemes.Scheme m)
    (solved : solveRows graph constraints explicitRows = .solved cache scheme) (rows : Fin m → Row) :
    (RowFlowSchemes.Models algebra explicitRows rows ∧
      solve rowCheck (instantiateGraph algebra rows graph) constraints = some cache) ↔
      ∃ parameter, RowFlowSchemes.instantiate algebra scheme parameter = rows := by
  obtain ⟨shapeSolved, rowSolved⟩ := (solveRows_solved_iff graph constraints cache explicitRows scheme).mp solved
  exact (joint_models_iff algebra rowCheck rowExact graph constraints cache shapeSolved explicitRows rows).symm.trans
    (rowScheme_models_exact_eq algebra antisymm _ scheme rowSolved rows)

end Yulang.NestedRowRequirements
