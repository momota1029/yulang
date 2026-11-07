import Yulang.CommonDemandSolver

/-!
# Finite demand roots of the currently covered Core generation

Roots are extracted from the actual finite generated clauses and from each
current worklist snapshot. An upper bound asks for the lower bounds of its
shared variable; a fixed comparison asks directly for its two bound references.
Lower seeds and directed variable edges produce no comparison by themselves.
Rows remain separate roots with their original variable IDs.

The collector does not infer a source-to-runtime call graph, nor does it
schedule SCCs. Source syntax is gated by exactly `Core.CommonSyntax.covered`.
Thus methods, dictionaries, casts, handlers, junction and indexing are not
claimed as supported roots. The completed solver still checks every root;
queries of a partial snapshot have no execution authorization meaning.
-/

namespace Yulang.CommonDemandRoots

open LayerBoundTemplates (Constraint Problem)

universe u
variable {m : Nat} {Bound : Type u}

inductive Root (m : Nat) (Bound : Type u) where
  | upper (node : Fin m) (bound : Bound)
  | fixed (source target : Bound)

def roots (problem : Problem m Bound) : List (Root m Bound) :=
  problem.filterMap fun
    | .upper node bound => some (.upper node bound)
    | .check source target => some (.fixed source target)
    | .lower _ _ | .flow _ _ => none

/-- The variable-flow part of this request. Bound references themselves keep
their shared constructor children; inspecting them may create more roots. -/
def Root.variables (problem : Problem m Bound) : Root m Bound → List (Fin m)
  | .upper node _ => DemandBoundPropagation.ancestors problem node
  | .fixed _ _ => []

theorem upper_variables_exact (problem : Problem m Bound) (node source : Fin m) (bound : Bound) :
    source ∈ (Root.upper node bound).variables problem ↔
      LayerBoundTemplates.Reaches problem source node :=
  DemandBoundPropagation.ancestors_exact problem source node

def ask (problem : Problem m Bound) : Root m Bound → List (Bound × Bound)
  | .upper node bound =>
      (DemandBoundPropagation.lowerBounds problem node).map fun lowerBound => (lowerBound, bound)
  | .fixed source target => [(source, target)]

private theorem roots_flatMap (problem selected : Problem m Bound) :
    (roots selected).flatMap (ask problem) = selected.flatMap (fun
      | .lower _ _ | .flow _ _ => []
      | .upper node bound =>
          (DemandBoundPropagation.lowerBounds problem node).map fun lowerBound => (lowerBound, bound)
      | .check source target => [(source, target)]) := by
  induction selected with
  | nil => rfl
  | cons constraint rest ih =>
      cases constraint <;> simp_all [roots, ask]

/-- Requesting all current roots reconstructs exactly the finite comparisons
that the reference rigid-discovery stage would produce, in the same order. -/
theorem all_roots_exact (problem : Problem m Bound) :
    (roots problem).flatMap (ask problem) = CommonBoundCoalescing.rigidComparisons problem := by
  rw [roots_flatMap]
  simp only [CommonBoundCoalescing.rigidComparisons, DemandBoundPropagation.lowerBounds_exact]
  rfl

open PresenceOpenTailGenerationLowering (Pool)
open CommonOptionalPoolQueries (queries)
open CommonBoundRefWorklist (Index Edge)

def atSnapshot (pool : Pool m) (edges : List (Edge pool)) : List (Root m (Index pool)) :=
  roots (CommonBoundRefCoalescing.template pool (queries pool) edges)

theorem snapshot_roots_exact (pool : Pool m) (edges : List (Edge pool)) :
    (atSnapshot pool edges).flatMap
      (ask (CommonBoundRefCoalescing.template pool (queries pool) edges)) =
        CommonBoundRefWorklist.rigid pool edges :=
  all_roots_exact _

/-- Rows are finite syntax. These are the exact original IDs read by a row
term, before any future effect-specific operation is added. -/
def rowVariables : Core.PresenceGeneration.RowTerm (Fin m) → List (Fin m)
  | .var node => [node]
  | .empty => []
  | .join first last => rowVariables first ++ rowVariables last

def rowRootVariables (root : CommonRowDeclarations.RowPair m) : List (Fin m) :=
  rowVariables root.1 ++ rowVariables root.2

theorem rowVariables_eval (term : Core.PresenceGeneration.RowTerm (Fin m))
    (first last : Fin m → Common.Row)
    (agree : ∀ node ∈ rowVariables term, first node = last node) :
    CommonPresenceConstraintGraph.rowEval first term =
      CommonPresenceConstraintGraph.rowEval last term := by
  induction term with
  | var node => exact agree node (by simp [rowVariables])
  | empty => rfl
  | join left right ihl ihr =>
      change Common.rowJoin (CommonPresenceConstraintGraph.rowEval first left)
        (CommonPresenceConstraintGraph.rowEval first right) =
          Common.rowJoin (CommonPresenceConstraintGraph.rowEval last left)
            (CommonPresenceConstraintGraph.rowEval last right)
      rw [ihl (fun node member => agree node (List.mem_append_left _ member)),
        ihr (fun node member => agree node (List.mem_append_right _ member))]

/-- A row root reads only the two finite row terms' original variables. -/
theorem rowRootVariables_exact (root : CommonRowDeclarations.RowPair m)
    (first last : Fin m → Common.Row)
    (agree : ∀ node ∈ rowRootVariables root, first node = last node) :
    Common.rowLe (CommonPresenceConstraintGraph.rowEval first root.1)
        (CommonPresenceConstraintGraph.rowEval first root.2) ↔
      Common.rowLe (CommonPresenceConstraintGraph.rowEval last root.1)
        (CommonPresenceConstraintGraph.rowEval last root.2) := by
  rw [rowVariables_eval root.1 first last
      (fun node member => agree node (List.mem_append_left _ member)),
    rowVariables_eval root.2 first last
      (fun node member => agree node (List.mem_append_right _ member))]

/-- Current clauses are generated once, retaining all original shared IDs.
This prepares requests; it does not run the bound worklist or a solver. -/
def clauses (expression : Core.Required.Term) : List (PresenceNormalForm.Clause (Option Empty)) :=
  if Core.CommonSyntax.covered expression then
    PresenceNormalForm.normalise
      (Core.PresenceGeneration.principal ([] : Core.PresenceGeneration.SchemeEnv Empty)
        (Core.CommonSyntax.lower expression))
  else []

def clauseProblem (clause : PresenceNormalForm.Clause (Option Empty)) :=
  CommonPresenceConstraintGraph.splitAtoms clause.pack

def clauseValueRoots (clause : PresenceNormalForm.Clause (Option Empty)) :
    List (Root (clause.locals + 1) (Index (clauseProblem clause).pool)) :=
  atSnapshot (clauseProblem clause).pool
    (CommonBoundRefWorklist.originalEdges (clauseProblem clause).pool (clauseProblem clause).edges)

def clauseRowRoots (clause : PresenceNormalForm.Clause (Option Empty)) :
    List (CommonRowDeclarations.RowPair (clause.locals + 1)) :=
  (clauseProblem clause).rows

/-- A finite plan can be prepared for every Core input without proof fields
or a successful-solver premise. The gate is the current public one. -/
structure Plan where
  clause : PresenceNormalForm.Clause (Option Empty)

def corePlans (expression : Core.Required.Term) : List Plan :=
  (clauses expression).map Plan.mk

def Plan.valueRoots (plan : Plan) := clauseValueRoots plan.clause
def Plan.rowRoots (plan : Plan) := clauseRowRoots plan.clause

theorem finish_clauses_exact (expression : Core.Required.Term) :
    (clauses expression).flatMap CommonDemandSolver.finishClause =
      CommonDemandSolver.finishCoreSchemes expression := by
  cases within : Core.CommonSyntax.covered expression <;>
    simp only [clauses, CommonDemandSolver.finishCoreSchemes, within,
      Bool.false_eq_true, ↓reduceIte, List.flatMap_nil, CommonDemandSolver.finishSource]

end Yulang.CommonDemandRoots
