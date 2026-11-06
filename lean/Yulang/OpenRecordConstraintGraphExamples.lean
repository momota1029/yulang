import Yulang.OpenRecordConstraintGraph
import Yulang.SemanticRecordQuotient

/-!
# Open-tail compilation checks and semantic-model specialization

These checks exercise the actual finite compiler, retaining a live tail,
unused original inputs, and source-level record extension. They assert
representation and model equivalence, not success of a record solver.
-/

namespace Yulang.OpenRecordConstraintGraph.Examples

open Inference

def openProblem : ConstraintProblems.Problem 4 where
  types := [(.record 7 (.var 0) (.var 1), .var 2), (.var 1, .emptyRecord)]
  rows := [(.var 1, .var 2)]

abbrev openCompiled := compile openProblem

abbrev firstEdge : Edge openCompiled.size :=
  openCompiled.constraints[0]'(by decide +kernel)

/-- The tail points to the same original input slot, not an empty field list. -/
theorem open_tail_retained : openCompiled.graph firstEdge.1 =
    .recordExtend 7 (openCompiled.input 0) (openCompiled.input 1) := by
  decide +kernel

theorem unused_input_retained : openCompiled.graph (openCompiled.input 3) = .input 3 := by
  decide +kernel

def hasInputTail (compiled : Compiled m) : Bool :=
  (List.finRange compiled.size).any fun node =>
    match compiled.graph node with
    | .recordExtend _ _ tail =>
        match compiled.graph tail with
        | .input _ => true
        | _ => false
    | _ => false

/-- Starting at the original lambda AST actually produces the open-tail
graph. Neither a source-support proof nor a graph is supplied by the caller. -/
theorem source_lambda_retains_open_tail :
    (compileSource (.lam (.record 7 (.lit .int) (.var 0)))).any
      (fun alternative => hasInputTail alternative.compiled) = true := by
  decide +kernel

def compoundProblem : ConstraintProblems.Problem 3 where
  types := [(.record 7 (.var 0) (.union (.var 1) .bottom), .var 2)]
  rows := []

def hasUnionTail (compiled : Compiled m) : Bool :=
  (List.finRange compiled.size).any fun node =>
    match compiled.graph node with
    | .recordExtend _ _ tail =>
        match compiled.graph tail with
        | .union _ _ => true
        | _ => false
    | _ => false

theorem compound_tail_retained : hasUnionTail (compile compoundProblem) = true := by
  decide +kernel

/-! The compiler is independent of how the intended record relation is
extended beyond its current congruence foundation. In particular, it already
preserves every assignment and target in the semantic quotient model. -/

universe u

variable {Row : Type u}

abbrev quotientModel (algebra : RowFlowSchemes.Algebra Row) :=
  SemanticRecordQuotient.model Row algebra.empty algebra.join algebra.le algebra.refl

theorem quotient_problem_instances_exact (algebra : RowFlowSchemes.Algebra Row)
    (problem : ConstraintProblems.Problem m) (output : Fin m) (target : Comp (quotientModel algebra)) :
    (compile problem).Instance (quotientModel algebra) output target ↔
      problem.Instance (quotientModel algebra) output target :=
  compile_instances_exact _ problem output target

/-- Every closed core expression is covered in the quotient model. The
right-hand family still contains constraints requiring a future solver. -/
theorem quotient_source_instances_exact (algebra : RowFlowSchemes.Algebra Row)
    (expression : Expr) (target : Comp (quotientModel algebra)) :
    SourceInstance (quotientModel algebra) (compileSource expression) target ↔
      Typing (quotientModel algebra) [] expression target :=
  compileSource_instances_exact (quotientModel algebra) SemanticRecordQuotient.union_is_join
    SemanticRecordQuotient.le_refl
    (fun {_ _ _} first last => SemanticRecordQuotient.le_trans _ _ _ first last)
    algebra.refl algebra.trans expression target

end Yulang.OpenRecordConstraintGraph.Examples
