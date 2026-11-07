import Yulang.CommonSignedExpressionGraph

/-!
# Compiling and solving finite signed-expression lower bounds

Every lower expression may contain all finite signed row constructors. Upper
bounds are original row variables or empty rows. All original row variables
are shared. The public solver constructs the graph and returns only finite
syntax; every unrestricted parameter assignment is sound and every original
row model is recovered literally. Arbitrary union upper bounds and the source
formula/type/universal compilation remain separate.
-/
namespace Yulang.CommonSignedConstraintCompilation
open Common (Row Occurrence rowLe)
open CommonEffectRequestGeneration (RowExpr)
open CommonSignedFlowFamily (Edge Action)
open CommonSignedExpressionPool (Pool collect collect_covers evaluate extend restrict)
open CommonSignedExpressionGraph (lowerScheme LowerHolds EdgesHold)

variable {scopes inputs : Nat}

inductive Upper (inputs : Nat) where
  | var : Fin inputs → Upper inputs
  | empty : Upper inputs

def Upper.eval (rows : Fin inputs → Row) : Upper inputs → Row
  | .var index => rows index
  | .empty => Common.rowEmpty

structure Constraint (scopes inputs : Nat) where
  lower : RowExpr scopes (Fin inputs)
  upper : Upper inputs

abbrev Problem (scopes inputs : Nat) := List (Constraint scopes inputs)

def Models (problem : Problem scopes inputs) (rows : Fin inputs → Row) : Prop :=
  ∀ constraint ∈ problem, rowLe (evaluate rows constraint.lower) (constraint.upper.eval rows)

def pool (problem : Problem scopes inputs) : Pool scopes inputs := collect (problem.map Constraint.lower)

def root (problem : Problem scopes inputs) (constraint : Constraint scopes inputs)
    (member : constraint ∈ problem) : Fin (pool problem).size :=
  (pool problem).reference constraint.lower (collect_covers _ _ (List.mem_map.mpr ⟨constraint, member, rfl⟩))

def extraEdges (problem : Problem scopes inputs) (constraint : Constraint scopes inputs)
    (member : constraint ∈ problem) : List (Edge (pool problem).size) :=
  match constraint.upper with
  | .var index => [⟨root problem constraint member, (pool problem).input index, .identity⟩]
  | .empty => []

def extraPure (problem : Problem scopes inputs) (constraint : Constraint scopes inputs)
    (member : constraint ∈ problem) : List (Fin (pool problem).size) :=
  match constraint.upper with
  | .var _ => []
  | .empty => [root problem constraint member]

def compile (problem : Problem scopes inputs) : CommonSignedGraphSolver.Scheme (pool problem).size :=
  ⟨⟨(lowerScheme (pool problem)).graph.edges ++
      problem.attach.flatMap (fun item => extraEdges problem item.val item.property),
    problem.attach.flatMap (fun item => extraPure problem item.val item.property)⟩,
    (lowerScheme (pool problem)).heads⟩

def UpperHolds (problem : Problem scopes inputs) (rows : Fin (pool problem).size → Row) : Prop :=
  ∀ constraint, ∀ member : constraint ∈ problem,
    rowLe (rows (root problem constraint member)) (constraint.upper.eval (restrict (pool problem) rows))

theorem compile_models (problem : Problem scopes inputs) (rows : Fin (pool problem).size → Row) :
    CommonSignedGraphSolver.Models (compile problem) rows ↔ LowerHolds (pool problem) rows ∧ UpperHolds problem rows := by
  constructor
  · rintro ⟨⟨edges, pure⟩, heads⟩
    have bodyModel : CommonSignedGraphSolver.Models (lowerScheme (pool problem)) rows :=
      ⟨⟨fun edge member => edges edge (List.mem_append_left _ member), by simp [lowerScheme]⟩, heads⟩
    refine ⟨(CommonSignedExpressionGraph.lowerScheme_exact _ _).mp bodyModel, ?_⟩
    intro constraint member
    cases found : constraint.upper with
    | var index =>
      intro occurrence present
      apply edges ⟨root problem constraint member, (pool problem).input index, .identity⟩ _ occurrence occurrence present rfl
      apply List.mem_append_right
      exact List.mem_flatMap.mpr ⟨⟨constraint, member⟩, by simp, by simp [extraEdges, found]⟩
    | empty =>
      intro occurrence present
      exact pure (root problem constraint member)
        (List.mem_flatMap.mpr ⟨⟨constraint, member⟩, by simp, by simp [extraPure, found]⟩) occurrence present
  · rintro ⟨lower, upper⟩
    have bodyModel := (CommonSignedExpressionGraph.lowerScheme_exact _ _).mpr lower
    refine ⟨⟨?_, ?_⟩, bodyModel.2⟩
    · intro edge member a b present runs
      rcases List.mem_append.mp member with bodyMember | upperMember
      · exact bodyModel.1.1 edge bodyMember a b present runs
      · obtain ⟨item, _, included⟩ := List.mem_flatMap.mp upperMember
        cases found : item.val.upper with
        | empty => simp [extraEdges, found] at included
        | var index =>
          have same : edge = ⟨root problem item.val item.property, (pool problem).input index, .identity⟩ := by
            simpa [extraEdges, found] using included
          subst edge
          have equal : a = b := Option.some.inj runs
          subst b
          simpa only [found, Upper.eval, restrict, Function.comp_apply] using upper item.val item.property a present
    · intro slot member occurrence present
      obtain ⟨item, _, included⟩ := List.mem_flatMap.mp member
      cases found : item.val.upper with
      | var => simp [extraPure, found] at included
      | empty =>
        have same : slot = root problem item.val item.property := by simpa [extraPure, found] using included
        subst slot
        simpa only [found, Upper.eval, Common.rowEmpty] using upper item.val item.property occurrence present

theorem compile_reflects (problem : Problem scopes inputs) (rows : Fin (pool problem).size → Row)
    (model : CommonSignedGraphSolver.Models (compile problem) rows) : Models problem (restrict (pool problem) rows) := by
  obtain ⟨lower, upper⟩ := (compile_models problem rows).mp model
  intro constraint member
  exact Common.rowLe_trans
    (CommonSignedExpressionGraph.evaluate_below_node (pool problem) rows lower constraint.lower
      (collect_covers _ _ (List.mem_map.mpr ⟨constraint, member, rfl⟩)))
    (upper constraint member)

theorem compile_extends (problem : Problem scopes inputs) (rows : Fin inputs → Row) (model : Models problem rows) :
    CommonSignedGraphSolver.Models (compile problem) (extend (pool problem) rows) := by
  apply (compile_models problem _).mpr
  refine ⟨CommonSignedExpressionGraph.extend_lower _ rows, ?_⟩
  intro constraint member
  have evaluation : extend (pool problem) rows (root problem constraint member) = evaluate rows constraint.lower :=
    CommonSignedExpressionPool.extend_reference (pool problem) rows constraint.lower
      (collect_covers _ _ (List.mem_map.mpr ⟨constraint, member, rfl⟩))
  rw [evaluation, CommonSignedExpressionPool.restrict_extend]
  exact model constraint member

/-- Real compilation exactness with a conservative extension of every original
independent row model and no assumptions about internal node rows. -/
theorem compile_exact (problem : Problem scopes inputs) (rows : Fin inputs → Row) :
    Models problem rows ↔ ∃ nodes : Fin (pool problem).size → Row,
      CommonSignedGraphSolver.Models (compile problem) nodes ∧ restrict (pool problem) nodes = rows := by
  constructor
  · intro model
    exact ⟨extend (pool problem) rows, compile_extends problem rows model,
      CommonSignedExpressionPool.restrict_extend _ rows⟩
  · rintro ⟨nodes, model, same⟩
    rw [← same]
    exact compile_reflects problem nodes model

/-- Finite returned syntax, original references, and independent parameters. -/
structure Scheme (inputs : Nat) where
  slots : Nat
  input : Fin inputs → Fin slots
  rows : CommonSignedGraphSolver.Scheme slots

def Scheme.instantiate (scheme : Scheme inputs) (parameters : Fin scheme.slots → Row) : Fin inputs → Row :=
  CommonSignedGraphSolver.instantiate scheme.rows parameters ∘ scheme.input

def ofSolution (problem : Problem scopes inputs) (solution : CommonSignedGraphSolver.Scheme (pool problem).size) : Scheme inputs :=
  ⟨(pool problem).size, (pool problem).input, solution⟩

def solve (problem : Problem scopes inputs) : List (Scheme inputs) :=
  (CommonSignedGraphSolver.solve (compile problem)).map (ofSolution problem)

/-- Every actual returned scheme and every arbitrary, possibly infinite row
assignment. Membership is the sole semantic premise. -/
theorem all_parameters_models (problem : Problem scopes inputs) (scheme : Scheme inputs)
    (returned : scheme ∈ solve problem) (parameters : Fin scheme.slots → Row) : Models problem (scheme.instantiate parameters) := by
  obtain ⟨solution, member, rfl⟩ := List.mem_map.mp returned
  exact compile_reflects problem _ (CommonSignedGraphSolver.all_parameters_models (compile problem) solution member parameters)

/-- Every lower expression, every finite problem, all independent original
rows: exact recovery with no residual condition on parameters. -/
theorem solve_all_instances_exact (problem : Problem scopes inputs) (rows : Fin inputs → Row) :
    Models problem rows ↔ ∃ scheme ∈ solve problem, ∃ parameters : Fin scheme.slots → Row,
      scheme.instantiate parameters = rows := by
  constructor
  · intro model
    let nodes := extend (pool problem) rows
    have recovered := CommonSignedGraphSolver.model_retraction (compile problem) nodes (compile_extends problem rows model)
    refine ⟨ofSolution problem (compile problem), List.mem_map.mpr ⟨compile problem, recovered.1, rfl⟩, nodes, ?_⟩
    change restrict (pool problem) (CommonSignedGraphSolver.instantiate (compile problem) nodes) = rows
    rw [recovered.2]
    exact CommonSignedExpressionPool.restrict_extend _ rows
  · rintro ⟨scheme, returned, parameters, same⟩
    rw [← same]
    exact all_parameters_models problem scheme returned parameters
theorem rejected_iff (problem : Problem scopes inputs) :
    solve problem = [] ↔ ¬ ∃ rows, Models problem rows := by
  constructor
  · intro rejected ⟨rows, model⟩
    obtain ⟨scheme, returned, _, _⟩ := (solve_all_instances_exact problem rows).mp model
    rw [rejected] at returned
    cases returned
  · intro absent
    cases returned : solve problem with
    | nil => rfl
    | cons scheme rest =>
      have member : scheme ∈ solve problem := by simp [returned]
      exact False.elim (absent ⟨scheme.instantiate (fun _ => Common.rowEmpty),
        all_parameters_models problem scheme member _⟩)
end Yulang.CommonSignedConstraintCompilation
