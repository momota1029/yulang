import Yulang.TypeConstraintGraph
import Yulang.NestedRowRequirements

/-!
# Compile type constraints once with shared symbolic rows

The existing type-constraint compiler can retain its rows as the original
core row terms. Instantiating those rows commutes with the complete compiler,
including exact front decomposition, collection, node sharing, and indices.
The constructed graph therefore serves every row assignment and can be used
by the joint row-requirement solver without recompilation or fresh unknowns.
-/

namespace Yulang.TypeConstraintRowInstantiation

open Inference TypeConstraintGraph
open NestedRowRequirements (nodeMapRows mapRows)

universe u

variable {m : Nat} {Row : Type u}

def symbolicCompile (problem : Problem m) : Option (Compiled m (RowTerm (Fin m))) :=
  compile RowTerm.empty RowTerm.join RowTerm.var problem

def instantiateCompiled (empty : Row) (join : Row → Row → Row) (rows : Fin m → Row)
    (symbolic : Compiled m (RowTerm (Fin m))) : Compiled m Row where
  size := symbolic.size
  graph := mapRows (rowEval empty join rows) symbolic.graph
  constraints := symbolic.constraints
  input := symbolic.input
  source := symbolic.source

@[simp] theorem rowEval_symbolic (term : RowTerm (Fin m)) :
    rowEval RowTerm.empty RowTerm.join RowTerm.var term = term := by
  induction term <;> simp_all only [rowEval]

theorem rowEval_flowEval (algebra : RowFlowSchemes.Algebra Row) (rows : Fin m → Row)
    (term : RowTerm (Fin m)) :
    rowEval algebra.empty algebra.join rows term = RowFlowSchemes.eval algebra rows term := by
  induction term <;> simp_all only [rowEval, RowFlowSchemes.eval]

theorem nodeOf_instantiate (pool : Pool m) (empty : Row) (join : Row → Row → Row)
    (rows : Fin m → Row) (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    nodeMapRows (rowEval empty join rows)
      (nodeOf pool RowTerm.empty RowTerm.join RowTerm.var term member) =
        nodeOf pool empty join rows term member := by
  cases term with
  | union | inter => have impossible := pool.supported _ member; cases impossible
  | _ => simp only [nodeOf, nodeMapRows, rowEval_symbolic]

theorem graph_instantiate (pool : Pool m) (empty : Row) (join : Row → Row → Row) (rows : Fin m → Row) :
    mapRows (rowEval empty join rows) (graph pool RowTerm.empty RowTerm.join RowTerm.var) =
      graph pool empty join rows := by
  funext node
  exact nodeOf_instantiate pool empty join rows _ _

theorem build_instantiate (empty : Row) (join : Row → Row → Row) (rows : Fin m → Row)
    (problem : Problem m) (valid : RigidProblem problem) :
    instantiateCompiled empty join rows (build RowTerm.empty RowTerm.join RowTerm.var problem valid) =
      build empty join rows problem valid := by
  simp only [instantiateCompiled, build, graph_instantiate]

/-- The complete actual compiler output is obtained by mapping only the rows
of the one symbolic output. No row-dependent node allocation is hidden. -/
theorem compile_instantiate (empty : Row) (join : Row → Row → Row) (rows : Fin m → Row)
    (problem : Problem m) :
    (symbolicCompile problem).map (instantiateCompiled empty join rows) =
      compile empty join rows problem := by
  unfold symbolicCompile compile
  split
  · rfl
  · simp only [Option.map_some, build_instantiate]

theorem compile_at_assignment (empty : Row) (join : Row → Row → Row) (rows : Fin m → Row)
    (problem : Problem m) (symbolic : Compiled m (RowTerm (Fin m)))
    (compiled : symbolicCompile problem = some symbolic) :
    compile empty join rows problem = some (instantiateCompiled empty join rows symbolic) := by
  rw [← compile_instantiate, compiled]
  rfl

theorem symbolicCompile_none_iff (empty : Row) (join : Row → Row → Row) (rows : Fin m → Row)
    (problem : Problem m) :
    symbolicCompile problem = none ↔ compile empty join rows problem = none := by
  rw [← compile_instantiate]
  cases symbolicCompile problem <;> simp

@[simp] theorem instantiateCompiled_input (empty : Row) (join : Row → Row → Row) (rows : Fin m → Row)
    (symbolic : Compiled m (RowTerm (Fin m))) :
    (instantiateCompiled empty join rows symbolic).input = symbolic.input := rfl

@[simp] theorem instantiateCompiled_constraints (empty : Row) (join : Row → Row → Row) (rows : Fin m → Row)
    (symbolic : Compiled m (RowTerm (Fin m))) :
    (instantiateCompiled empty join rows symbolic).constraints = symbolic.constraints := rfl

theorem instantiateCompiled_graph (algebra : RowFlowSchemes.Algebra Row) (rows : Fin m → Row)
    (symbolic : Compiled m (RowTerm (Fin m))) :
    (instantiateCompiled algebra.empty algebra.join rows symbolic).graph =
      NestedRowRequirements.instantiateGraph algebra rows symbolic.graph := by
  have same : rowEval algebra.empty algebra.join rows = RowFlowSchemes.eval algebra rows :=
    funext (rowEval_flowEval algebra rows)
  exact congrArg (fun evaluate => mapRows evaluate symbolic.graph) same

/-- The source compiler's constraints, including negative arrow input rows,
share one cache across all row instantiations. -/
theorem instantiated_saturate (empty : Row) (join : Row → Row → Row) (rows : Fin m → Row)
    (symbolic : Compiled m (RowTerm (Fin m))) :
    NestedValueSolver.saturate (instantiateCompiled empty join rows symbolic).graph
      (instantiateCompiled empty join rows symbolic).constraints =
        NestedValueSolver.saturate symbolic.graph symbolic.constraints :=
  NestedRowRequirements.saturate_mapRows _ _ _

end Yulang.TypeConstraintRowInstantiation
