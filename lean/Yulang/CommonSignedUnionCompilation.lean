import Yulang.CommonSignedChoiceSolver
import Yulang.CommonSignedExpressionGraph

/-! Full signed lower expressions and ordinary (possibly union) upper row
terms, compiled through the real shared allocator into disjunctive signed
clauses. The returned finite schemes accept all independent row parameters. -/
namespace Yulang.CommonSignedUnionCompilation
open Common (Row Occurrence rowLe)
open Core.PresenceGeneration (RowTerm)
open CommonEffectRequestGeneration (RowExpr)
open CommonSignedFlowFamily (Edge Action)
open CommonSignedExpressionPool (Pool collect collect_covers evaluate extend restrict)
open CommonSignedExpressionGraph (lowerScheme LowerHolds EdgesHold)

variable {scopes inputs : Nat}

def upperVariables : RowTerm (Fin inputs) → List (Fin inputs)
  | .var index => [index]
  | .empty => []
  | .join first last => upperVariables first ++ upperVariables last

def upperEval (rows : Fin inputs → Row) (term : RowTerm (Fin inputs)) : Row :=
  term.eval Common.model (fun index => (.base .unit, rows index))

theorem upper_member (rows : Fin inputs → Row) (term : RowTerm (Fin inputs)) (occurrence : Occurrence) :
    upperEval rows term occurrence ↔ ∃ index ∈ upperVariables term, rows index occurrence := by
  induction term with
  | var index => simp [upperEval, upperVariables, RowTerm.eval]
  | empty =>
    change False ↔ _
    simp [upperVariables]
  | join first last ihf ihl =>
    change (upperEval rows first occurrence ∨ upperEval rows last occurrence) ↔ _
    simp only [ihf, ihl, upperVariables, List.mem_append, or_and_right, exists_or]

structure Constraint (scopes inputs : Nat) where
  lower : RowExpr scopes (Fin inputs)
  upper : RowTerm (Fin inputs)

abbrev Problem (scopes inputs : Nat) := List (Constraint scopes inputs)

def Models (problem : Problem scopes inputs) (rows : Fin inputs → Row) : Prop :=
  ∀ constraint ∈ problem, rowLe (evaluate rows constraint.lower) (upperEval rows constraint.upper)

def pool (problem : Problem scopes inputs) : Pool scopes inputs := collect (problem.map Constraint.lower)

def root (problem : Problem scopes inputs) (constraint : Constraint scopes inputs) (member : constraint ∈ problem) :
    Fin (pool problem).size :=
  (pool problem).reference constraint.lower (collect_covers _ _ (List.mem_map.mpr ⟨constraint, member, rfl⟩))

def edgesClauses (edges : List (Edge slots)) : CommonSignedChoicePreparation.Graph slots :=
  edges.map (fun edge => ⟨edge.source, edge.action, [edge.target]⟩)

theorem edgesClauses_exact (edges : List (Edge slots)) (rows : Fin slots → Row) :
    CommonSignedChoicePreparation.Models (edgesClauses edges) rows ↔ EdgesHold edges rows := by
  constructor
  · intro model edge member source target present runs
    obtain ⟨slot, listed, next⟩ := model ⟨edge.source, edge.action, [edge.target]⟩
      (List.mem_map.mpr ⟨edge, member, rfl⟩) source target present runs
    have same : slot = edge.target := by simpa using listed
    exact same ▸ next
  · intro model clause member source target present runs
    obtain ⟨edge, listed, same⟩ := List.mem_map.mp member
    subst clause
    exact ⟨edge.target, by simp, model edge listed source target present runs⟩

def lowerProblem (pool : Pool scopes inputs) : CommonSignedChoiceSolver.Problem pool.size :=
  ⟨edgesClauses (lowerScheme pool).graph.edges, (lowerScheme pool).heads⟩

theorem lowerProblem_exact (pool : Pool scopes inputs) (rows : Fin pool.size → Row) :
    (lowerProblem pool).Models rows ↔ LowerHolds pool rows := by
  rw [← CommonSignedExpressionGraph.lowerScheme_exact]
  change (_ ∧ _) ↔ ((_ ∧ _) ∧ _)
  simp only [lowerProblem]
  rw [edgesClauses_exact]
  constructor
  · intro model
    exact ⟨⟨model.1, by simp [lowerScheme]⟩, model.2⟩
  · intro model
    exact ⟨model.1.1, model.2⟩

def upperClause (problem : Problem scopes inputs) (constraint : Constraint scopes inputs) (member : constraint ∈ problem) :
    CommonSignedChoicePreparation.Clause (pool problem).size :=
  ⟨root problem constraint member, .identity, (upperVariables constraint.upper).map (pool problem).input⟩

def compile (problem : Problem scopes inputs) : CommonSignedChoiceSolver.Problem (pool problem).size :=
  ⟨(lowerProblem (pool problem)).clauses ++ problem.attach.map (fun item => upperClause problem item.val item.property),
    (lowerProblem (pool problem)).heads⟩

def UpperHolds (problem : Problem scopes inputs) (rows : Fin (pool problem).size → Row) : Prop :=
  ∀ constraint, ∀ member : constraint ∈ problem,
    rowLe (rows (root problem constraint member)) (upperEval (restrict (pool problem) rows) constraint.upper)

theorem compile_models (problem : Problem scopes inputs) (rows : Fin (pool problem).size → Row) :
    (compile problem).Models rows ↔ LowerHolds (pool problem) rows ∧ UpperHolds problem rows := by
  constructor
  · rintro ⟨clauses, heads⟩
    have lowerModel : (lowerProblem (pool problem)).Models rows :=
      ⟨fun clause member => clauses clause (List.mem_append_left _ member), heads⟩
    refine ⟨(lowerProblem_exact _ rows).mp lowerModel, ?_⟩
    intro constraint member occurrence present
    obtain ⟨slot, listed, next⟩ := clauses (upperClause problem constraint member)
      (List.mem_append_right _ (List.mem_map.mpr ⟨⟨constraint, member⟩, by simp, rfl⟩)) occurrence occurrence present rfl
    obtain ⟨index, included, same⟩ := List.mem_map.mp listed
    apply (upper_member (restrict (pool problem) rows) constraint.upper occurrence).mpr
    refine ⟨index, included, ?_⟩
    simpa only [restrict, Function.comp_apply, same] using next
  · rintro ⟨lower, upper⟩
    have lowerModel := (lowerProblem_exact _ rows).mpr lower
    refine ⟨?_, lowerModel.2⟩
    intro clause member source target present runs
    rcases List.mem_append.mp member with lowerMember | upperMember
    · exact lowerModel.1 clause lowerMember source target present runs
    · obtain ⟨item, _, same⟩ := List.mem_map.mp upperMember
      subst clause
      have sameOccurrence : source = target := Option.some.inj runs
      subst target
      obtain ⟨index, included, next⟩ := (upper_member (restrict (pool problem) rows) item.val.upper source).mp
        (upper item.val item.property source present)
      exact ⟨(pool problem).input index, List.mem_map.mpr ⟨index, included, rfl⟩, next⟩

theorem compile_reflects (problem : Problem scopes inputs) (rows : Fin (pool problem).size → Row)
    (model : (compile problem).Models rows) : Models problem (restrict (pool problem) rows) := by
  obtain ⟨lower, upper⟩ := (compile_models problem rows).mp model
  intro constraint member
  exact Common.rowLe_trans
    (CommonSignedExpressionGraph.evaluate_below_node (pool problem) rows lower constraint.lower
      (collect_covers _ _ (List.mem_map.mpr ⟨constraint, member, rfl⟩))) (upper constraint member)

theorem compile_extends (problem : Problem scopes inputs) (rows : Fin inputs → Row) (model : Models problem rows) :
    (compile problem).Models (extend (pool problem) rows) := by
  apply (compile_models problem _).mpr
  refine ⟨CommonSignedExpressionGraph.extend_lower _ rows, ?_⟩
  intro constraint member
  have evaluation : extend (pool problem) rows (root problem constraint member) = evaluate rows constraint.lower :=
    CommonSignedExpressionPool.extend_reference (pool problem) rows constraint.lower
      (collect_covers _ _ (List.mem_map.mpr ⟨constraint, member, rfl⟩))
  rw [evaluation, CommonSignedExpressionPool.restrict_extend]
  exact model constraint member

theorem compile_exact (problem : Problem scopes inputs) (rows : Fin inputs → Row) :
    Models problem rows ↔ ∃ nodes : Fin (pool problem).size → Row,
      (compile problem).Models nodes ∧ restrict (pool problem) nodes = rows := by
  constructor
  · intro model
    exact ⟨extend (pool problem) rows, compile_extends problem rows model,
      CommonSignedExpressionPool.restrict_extend _ rows⟩
  · rintro ⟨nodes, model, same⟩
    rw [← same]
    exact compile_reflects problem nodes model

structure Scheme (inputs : Nat) where
  slots : Nat
  input : Fin inputs → Fin slots
  rows : CommonSignedChoiceSolver.Problem slots

def Scheme.instantiate (scheme : Scheme inputs) (parameters : Fin scheme.slots → Row) : Fin inputs → Row :=
  CommonSignedChoiceSolver.instantiateRows scheme.rows parameters ∘ scheme.input

def ofSolution (problem : Problem scopes inputs) (solution : CommonSignedChoiceSolver.Problem (pool problem).size) : Scheme inputs :=
  ⟨(pool problem).size, (pool problem).input, solution⟩

def solve (problem : Problem scopes inputs) : List (Scheme inputs) :=
  (CommonSignedChoiceSolver.solve (compile problem)).map (ofSolution problem)

theorem all_parameters_models (problem : Problem scopes inputs) (scheme : Scheme inputs)
    (returned : scheme ∈ solve problem) (parameters : Fin scheme.slots → Row) : Models problem (scheme.instantiate parameters) := by
  obtain ⟨solution, member, rfl⟩ := List.mem_map.mp returned
  exact compile_reflects problem _ (CommonSignedChoiceSolver.all_parameters_models (compile problem) solution member parameters)

theorem solve_all_instances_exact (problem : Problem scopes inputs) (rows : Fin inputs → Row) :
    Models problem rows ↔ ∃ scheme ∈ solve problem, ∃ parameters : Fin scheme.slots → Row, scheme.instantiate parameters = rows := by
  constructor
  · intro model
    let nodes := extend (pool problem) rows
    have extended := compile_extends problem rows model
    have returned := (CommonSignedChoiceSolver.mem_solve (compile problem) (compile problem)).mpr
      ⟨rfl, CommonSignedChoiceSolver.models_checkHeads (compile problem) nodes extended⟩
    refine ⟨ofSolution problem (compile problem), List.mem_map.mpr ⟨compile problem, returned, rfl⟩, nodes, ?_⟩
    change restrict (pool problem) (CommonSignedChoiceSolver.instantiateRows (compile problem) nodes) = rows
    rw [CommonSignedChoiceSolver.model_retraction (compile problem) nodes extended]
    exact CommonSignedExpressionPool.restrict_extend _ rows
  · rintro ⟨scheme, returned, parameters, same⟩
    rw [← same]
    exact all_parameters_models problem scheme returned parameters
end Yulang.CommonSignedUnionCompilation
