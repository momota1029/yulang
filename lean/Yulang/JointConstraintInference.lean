import Yulang.ConstraintProblems
import Yulang.TypeConstraintInference
import Yulang.TypeConstraintRowInstantiation

/-!
# Joint principal inference for value and computation-row constraints

The computation is independent of the semantic row carrier. It compiles one
symbolic type graph, saturates constructor constraints once, and solves the
explicit and generated row obligations into a shared-parameter row scheme.
An inferred scheme has freely chosen row and value parameters and no residual
constraints. Its value component is a finite regular block.

Correctness is interpreted in any antisymmetric row join algebra. A semantic
row checker is used only inside proofs to reuse the fixed-row correctness
theorem; no checker or decision procedure on semantic rows is an input to
inference or scheme instantiation.
-/

namespace Yulang.JointConstraintInference

open Inference

universe u

variable {n : Nat} {Row : Type u}

def model (algebra : RowFlowSchemes.Algebra Row) : Inference.Model :=
  RegularInferenceModel.model Row algebra.empty algebra.join algebra.le

abbrev Value (Row : Type u) := RegularInferenceModel.Ty Row

/-- The finite result stores only its symbolic graph, closed cache, shared
input references, and explicit free row expressions. -/
structure Scheme (n : Nat) where
  size : Nat
  graph : NestedRowRequirements.SymbolicGraph size n
  cache : List (NestedValueSolver.Edge size)
  input : Fin n → Fin size
  rowScheme : RowFlowSchemes.Scheme n

def Scheme.ofCompiled (compiled : TypeConstraintGraph.Compiled n (RowTerm (Fin n)))
    (cache : List (NestedValueSolver.Edge compiled.size)) (rows : RowFlowSchemes.Scheme n) : Scheme n :=
  ⟨compiled.size, compiled.graph, cache, compiled.input, rows⟩

def Scheme.rows (scheme : Scheme n) (algebra : RowFlowSchemes.Algebra Row)
    (parameter : Fin n → Row) : Fin n → Row :=
  RowFlowSchemes.instantiate algebra scheme.rowScheme parameter

def Scheme.values (scheme : Scheme n) (algebra : RowFlowSchemes.Algebra Row)
    (rowParameter : Fin n → Row) (valueParameter : Fin scheme.size → Value Row) : Fin n → Value Row :=
  fun index => RegularInferenceModel.solution
    (NestedRowRequirements.instantiateGraph algebra (scheme.rows algebra rowParameter) scheme.graph)
    scheme.cache valueParameter (scheme.input index)

def Scheme.instantiate (scheme : Scheme n) (algebra : RowFlowSchemes.Algebra Row)
    (rowParameter : Fin n → Row) (valueParameter : Fin scheme.size → Value Row) : Fin n → Comp (model algebra) :=
  fun index => (scheme.values algebra rowParameter valueParameter index, scheme.rows algebra rowParameter index)

/-- Rows are recovered literally; value types use the existing mutual
subtyping equivalence. All parameter assignments are unrestricted. -/
def Scheme.Models (scheme : Scheme n) (algebra : RowFlowSchemes.Algebra Row)
    (values : Fin n → Value Row) (rows : Fin n → Row) : Prop :=
  ∃ rowParameter : Fin n → Row, ∃ valueParameter : Fin scheme.size → Value Row,
    scheme.rows algebra rowParameter = rows ∧
      ∀ index, RegularInferenceModel.Equivalent algebra.le
        (scheme.values algebra rowParameter valueParameter index) (values index)

def Scheme.Instance (scheme : Scheme n) (algebra : RowFlowSchemes.Algebra Row)
    (output : Fin n) (expected : Comp (model algebra)) : Prop :=
  ∃ rowParameter : Fin n → Row, ∃ valueParameter : Fin scheme.size → Value Row,
    Comp.le (model algebra) (scheme.instantiate algebra rowParameter valueParameter output) expected

inductive Status where
  | unsupported
  | rejected
  | inferred
  deriving DecidableEq, Repr

inductive Result (n : Nat) where
  | unsupported
  | rejected
  | inferred : Scheme n → Result n

def Result.status : Result n → Status
  | .unsupported => .unsupported
  | .rejected => .rejected
  | .inferred _ => .inferred

def Result.Models (algebra : RowFlowSchemes.Algebra Row)
    (values : Fin n → Value Row) (rows : Fin n → Row) : Result n → Prop
  | .inferred scheme => scheme.Models algebra values rows
  | _ => False

def Result.Instance (algebra : RowFlowSchemes.Algebra Row)
    (output : Fin n) (expected : Comp (model algebra)) : Result n → Prop
  | .inferred scheme => scheme.Instance algebra output expected
  | _ => False

/-- Purely symbolic inference: neither a semantic row algebra nor a row
checker is consulted during this computation. -/
def infer (problem : ConstraintProblems.Problem n) : Result n :=
  match TypeConstraintRowInstantiation.symbolicCompile problem.types with
  | none => .unsupported
  | some compiled =>
      match NestedRowRequirements.solveRows compiled.graph compiled.constraints problem.rows with
      | .unsupported => .unsupported
      | .rejected => .rejected
      | .solved cache rows => .inferred (Scheme.ofCompiled compiled cache rows)

/-- A constructor mismatch can already be rejected independently of rows.
Otherwise support additionally checks every explicit or generated row term. -/
def supported (problem : ConstraintProblems.Problem n) : Bool :=
  match TypeConstraintRowInstantiation.symbolicCompile problem.types with
  | none => false
  | some compiled =>
      match NestedValueSolver.solve NestedRowRequirements.shapeCheck compiled.graph compiled.constraints with
      | none => true
      | some cache => RowFlowSchemes.supported (NestedRowRequirements.jointProblem problem.rows compiled.graph cache)

theorem rowHolds_iff (algebra : RowFlowSchemes.Algebra Row) (rows : Fin n → Row)
    (constraints : RowFlowSchemes.Problem n) :
    ConstraintProblems.RowHolds (model algebra) rows constraints ↔
      RowFlowSchemes.Models algebra constraints rows :=
  ConstraintProblems.rowHolds_flow (model algebra) algebra rfl rfl rfl rows constraints

theorem fixed_infer_at_rows (algebra : RowFlowSchemes.Algebra Row) (rowCheck : Row → Row → Bool)
    (rows : Fin n → Row) (types : TypeConstraintGraph.Problem n)
    (symbolic : TypeConstraintGraph.Compiled n (RowTerm (Fin n)))
    (compiled : TypeConstraintRowInstantiation.symbolicCompile types = some symbolic)
    (cache : List (NestedValueSolver.Edge symbolic.size))
    (solved : NestedValueSolver.solve rowCheck
      (NestedRowRequirements.instantiateGraph algebra rows symbolic.graph) symbolic.constraints = some cache) :
    TypeConstraintInference.infer algebra.empty algebra.join rowCheck rows types =
      .inferred (TypeConstraintInference.Scheme.ofCompiled
        (TypeConstraintRowInstantiation.instantiateCompiled algebra.empty algebra.join rows symbolic) cache) := by
  have concreteSolved : NestedValueSolver.solve rowCheck
      (TypeConstraintRowInstantiation.instantiateCompiled algebra.empty algebra.join rows symbolic).graph
      (TypeConstraintRowInstantiation.instantiateCompiled algebra.empty algebra.join rows symbolic).constraints =
        some cache := by
    simp only [TypeConstraintRowInstantiation.instantiateCompiled_graph,
      TypeConstraintRowInstantiation.instantiateCompiled_constraints]
    exact solved
  unfold TypeConstraintInference.infer
  rw [TypeConstraintRowInstantiation.compile_at_assignment algebra.empty algebra.join rows types symbolic compiled]
  simp only [concreteSolved]

theorem fixed_scheme_instantiate (algebra : RowFlowSchemes.Algebra Row) (rows : Fin n → Row)
    (symbolic : TypeConstraintGraph.Compiled n (RowTerm (Fin n)))
    (cache : List (NestedValueSolver.Edge symbolic.size)) (parameter : Fin symbolic.size → Value Row) :
    (TypeConstraintInference.Scheme.ofCompiled
      (TypeConstraintRowInstantiation.instantiateCompiled algebra.empty algebra.join rows symbolic) cache).instantiate parameter =
      fun index => RegularInferenceModel.solution
        (NestedRowRequirements.instantiateGraph algebra rows symbolic.graph) cache parameter (symbolic.input index) := by
  funext index
  change RegularInferenceModel.solution
      (TypeConstraintRowInstantiation.instantiateCompiled algebra.empty algebra.join rows symbolic).graph
      cache parameter (symbolic.input index) = _
  exact congrArg
    (fun source : NestedValueSolver.Graph symbolic.size Row =>
      RegularInferenceModel.solution source cache parameter (symbolic.input index))
    (TypeConstraintRowInstantiation.instantiateCompiled_graph algebra rows symbolic)

private theorem source_solves_at_rows (algebra : RowFlowSchemes.Algebra Row)
    (rowCheck : Row → Row → Bool)
    (rowExact : ∀ left right, rowCheck left right = true ↔ algebra.le left right)
    (rows : Fin n → Row) (types : TypeConstraintGraph.Problem n)
    (symbolic : TypeConstraintGraph.Compiled n (RowTerm (Fin n)))
    (compiled : TypeConstraintRowInstantiation.symbolicCompile types = some symbolic)
    (cache : List (NestedValueSolver.Edge symbolic.size))
    (shapeSolved : NestedValueSolver.solve NestedRowRequirements.shapeCheck symbolic.graph symbolic.constraints = some cache)
    (values : Fin n → Value Row) (accepted : TypeConstraintGraph.Holds (model algebra) rows values types) :
    NestedValueSolver.solve rowCheck (NestedRowRequirements.instantiateGraph algebra rows symbolic.graph)
      symbolic.constraints = some cache := by
  let concrete := TypeConstraintRowInstantiation.instantiateCompiled algebra.empty algebra.join rows symbolic
  have compiledAtRows := TypeConstraintRowInstantiation.compile_at_assignment algebra.empty algebra.join
    rows types symbolic compiled
  have generated := (TypeConstraintGraphEquivalence.compile_extend_exact (model algebra)
    (TypeConstraintInference.latticeRules algebra.empty algebra.join algebra.le)
    (TypeConstraintInference.congruenceRules algebra.empty algebra.join algebra.le algebra.refl)
    rows types concrete compiledAtRows values).mpr accepted
  have realized := (TypeConstraintInference.semanticGraphModels_iff algebra.empty algebra.join algebra.le
    concrete.graph concrete.constraints (concrete.extend (model algebra) rows values)).mp generated
  cases found : NestedValueSolver.solve rowCheck
      (NestedRowRequirements.instantiateGraph algebra rows symbolic.graph) symbolic.constraints with
  | none =>
      have concreteRejected : NestedValueSolver.solve rowCheck concrete.graph concrete.constraints = none := by
        simp only [concrete, TypeConstraintRowInstantiation.instantiateCompiled_graph,
          TypeConstraintRowInstantiation.instantiateCompiled_constraints]
        exact found
      exact False.elim ((RegularInferenceModel.solve_none_iff rowCheck algebra.le algebra.refl algebra.trans
        rowExact concrete.graph concrete.constraints).mp concreteRejected
          ⟨concrete.extend (model algebra) rows values, realized⟩)
  | some actual =>
      have structural := (NestedRowRequirements.solve_mapRows_iff (RowFlowSchemes.eval algebra rows)
        rowCheck symbolic.graph symbolic.constraints actual).mp found
      have same : cache = actual := Option.some.inj (shapeSolved.symm.trans structural.1)
      exact congrArg some same.symm

private theorem compiled_models_exact (algebra : RowFlowSchemes.Algebra Row)
    (antisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (rowCheck : Row → Row → Bool)
    (rowExact : ∀ left right, rowCheck left right = true ↔ algebra.le left right)
    (problem : ConstraintProblems.Problem n)
    (symbolic : TypeConstraintGraph.Compiled n (RowTerm (Fin n)))
    (compiled : TypeConstraintRowInstantiation.symbolicCompile problem.types = some symbolic)
    (cache : List (NestedValueSolver.Edge symbolic.size)) (rowScheme : RowFlowSchemes.Scheme n)
    (solved : NestedRowRequirements.solveRows symbolic.graph symbolic.constraints problem.rows = .solved cache rowScheme)
    (values : Fin n → Value Row) (rows : Fin n → Row) :
    problem.Holds (model algebra) values rows ↔
      (Scheme.ofCompiled symbolic cache rowScheme).Models algebra values rows := by
  obtain ⟨shapeSolved, rowSolved⟩ :=
    (NestedRowRequirements.solveRows_solved_iff symbolic.graph symbolic.constraints cache problem.rows rowScheme).mp solved
  constructor
  · rintro ⟨typesHold, rowsHold⟩
    have sourceSolved := source_solves_at_rows algebra rowCheck rowExact rows problem.types
      symbolic compiled cache shapeSolved values typesHold
    have rowsModel := (rowHolds_iff algebra rows problem.rows).mp rowsHold
    obtain ⟨rowParameter, rowsEqual⟩ := (NestedRowRequirements.solveRows_models_exact_eq algebra antisymm
      rowCheck rowExact symbolic.graph symbolic.constraints cache problem.rows rowScheme solved rows).mp
        ⟨rowsModel, sourceSolved⟩
    have correct := TypeConstraintInference.infer_correct algebra.empty algebra.join rowCheck algebra.le
      algebra.refl algebra.trans rowExact rows problem.types
    rw [fixed_infer_at_rows algebra rowCheck rows problem.types symbolic compiled cache sourceSolved] at correct
    obtain ⟨valueParameter, equivalent⟩ := (correct.2 values).mp typesHold
    refine ⟨rowParameter, valueParameter, rowsEqual, ?_⟩
    intro index
    have fixed := congrFun (fixed_scheme_instantiate algebra rows symbolic cache valueParameter) index
    have recovered := equivalent index
    rw [fixed] at recovered
    simpa only [Scheme.ofCompiled, Scheme.values, Scheme.rows, rowsEqual] using recovered
  · rintro ⟨rowParameter, valueParameter, rowsEqual, equivalent⟩
    have generated := NestedRowRequirements.solveRows_instantiates algebra rowCheck rowExact
      symbolic.graph symbolic.constraints cache problem.rows rowScheme solved rowParameter
    have rowsEq : RowFlowSchemes.instantiate algebra rowScheme rowParameter = rows := rowsEqual
    rw [rowsEq] at generated
    have correct := TypeConstraintInference.infer_correct algebra.empty algebra.join rowCheck algebra.le
      algebra.refl algebra.trans rowExact rows problem.types
    rw [fixed_infer_at_rows algebra rowCheck rows problem.types symbolic compiled cache generated.2] at correct
    refine ⟨(correct.2 values).mpr ⟨valueParameter, ?_⟩, (rowHolds_iff algebra rows problem.rows).mpr generated.1⟩
    intro index
    have fixed := congrFun (fixed_scheme_instantiate algebra rows symbolic cache valueParameter) index
    rw [fixed]
    simpa only [Scheme.ofCompiled, Scheme.values, Scheme.rows, rowsEq] using equivalent index

private theorem compiled_rejects (algebra : RowFlowSchemes.Algebra Row)
    (rowCheck : Row → Row → Bool)
    (rowExact : ∀ left right, rowCheck left right = true ↔ algebra.le left right)
    (problem : ConstraintProblems.Problem n)
    (symbolic : TypeConstraintGraph.Compiled n (RowTerm (Fin n)))
    (compiled : TypeConstraintRowInstantiation.symbolicCompile problem.types = some symbolic)
    (rejected : NestedRowRequirements.solveRows symbolic.graph symbolic.constraints problem.rows = .rejected) :
    ¬ ∃ (values : Fin n → Value Row) (rows : Fin n → Row), problem.Holds (model algebra) values rows := by
  rintro ⟨values, rows, accepted⟩
  have shapeRejected := (NestedRowRequirements.solveRows_rejected_iff
    symbolic.graph symbolic.constraints problem.rows).mp rejected
  have concreteRejected := NestedRowRequirements.shape_rejection_preserved (RowFlowSchemes.eval algebra rows)
    rowCheck symbolic.graph symbolic.constraints shapeRejected
  have rejectedAtRows : NestedValueSolver.solve rowCheck
      (TypeConstraintRowInstantiation.instantiateCompiled algebra.empty algebra.join rows symbolic).graph
      (TypeConstraintRowInstantiation.instantiateCompiled algebra.empty algebra.join rows symbolic).constraints = none := by
    simp only [TypeConstraintRowInstantiation.instantiateCompiled_graph,
      TypeConstraintRowInstantiation.instantiateCompiled_constraints]
    exact concreteRejected
  have fixedRejected : TypeConstraintInference.infer algebra.empty algebra.join rowCheck rows problem.types = .rejected := by
    unfold TypeConstraintInference.infer
    rw [TypeConstraintRowInstantiation.compile_at_assignment algebra.empty algebra.join rows problem.types symbolic compiled]
    simp only [rejectedAtRows]
  have noModel := ((TypeConstraintInference.infer_rejected_iff algebra.empty algebra.join rowCheck algebra.le
    algebra.refl algebra.trans rowExact rows problem.types).mp
      (congrArg TypeConstraintInference.Result.status fixedRejected)).2
  exact noModel ⟨values, accepted.1⟩

/-- The support decision is independent of the interpretation of rows. -/
theorem infer_unsupported_iff (problem : ConstraintProblems.Problem n) :
    (infer problem).status = .unsupported ↔ supported problem = false := by
  cases compiled : TypeConstraintRowInstantiation.symbolicCompile problem.types with
  | none => simp [infer, supported, compiled, Result.status]
  | some symbolic =>
      cases shapeSolved : NestedValueSolver.solve NestedRowRequirements.shapeCheck symbolic.graph symbolic.constraints with
      | none => simp [infer, supported, compiled, NestedRowRequirements.solveRows, shapeSolved, Result.status]
      | some cache =>
          cases rowSolved : RowFlowSchemes.solve (NestedRowRequirements.jointProblem problem.rows symbolic.graph cache) with
          | unsupported =>
              have absent := (RowFlowSchemes.solve_unsupported_iff _).mp rowSolved
              simp [infer, supported, compiled, NestedRowRequirements.solveRows, shapeSolved,
                rowSolved, absent, Result.status]
          | solved rowScheme =>
              have accepted := ((RowFlowSchemes.solve_solved_iff _ rowScheme).mp rowSolved).2
              simp [infer, supported, compiled, NestedRowRequirements.solveRows, shapeSolved,
                rowSolved, accepted, Result.status]

def Result.Correct (algebra : RowFlowSchemes.Algebra Row) (problem : ConstraintProblems.Problem n) : Result n → Prop
  | .unsupported => supported problem = false
  | .rejected => supported problem = true ∧ ¬ ∃ values rows, problem.Holds (model algebra) values rows
  | .inferred scheme => supported problem = true ∧
      ∀ values rows, problem.Holds (model algebra) values rows ↔ scheme.Models algebra values rows

/-- Full correctness of symbolic inference, interpreted in any antisymmetric
row join algebra. The semantic checker below exists only in this proof. -/
theorem infer_correct (algebra : RowFlowSchemes.Algebra Row)
    (antisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (problem : ConstraintProblems.Problem n) : (infer problem).Correct algebra problem := by
  classical
  let rowCheck := fun left right => decide (algebra.le left right)
  have rowExact : ∀ left right, rowCheck left right = true ↔ algebra.le left right := by
    intro left right
    exact decide_eq_true_iff
  unfold infer
  cases compiled : TypeConstraintRowInstantiation.symbolicCompile problem.types with
  | none =>
      change supported problem = false
      simp only [supported, compiled]
  | some symbolic =>
      cases solved : NestedRowRequirements.solveRows symbolic.graph symbolic.constraints problem.rows with
      | unsupported =>
          simp only [solved, Result.Correct]
          have returned : (infer problem).status = .unsupported := by simp [infer, compiled, solved, Result.status]
          exact (infer_unsupported_iff problem).mp returned
      | rejected =>
          simp only [solved, Result.Correct]
          have shapeRejected := (NestedRowRequirements.solveRows_rejected_iff
            symbolic.graph symbolic.constraints problem.rows).mp solved
          refine ⟨?_, compiled_rejects algebra rowCheck rowExact problem symbolic compiled solved⟩
          simp only [supported, compiled, shapeRejected]
      | solved cache rowScheme =>
          simp only [solved, Result.Correct]
          obtain ⟨shapeSolved, rowSolved⟩ :=
            (NestedRowRequirements.solveRows_solved_iff symbolic.graph symbolic.constraints cache problem.rows rowScheme).mp solved
          refine ⟨?_, fun values rows => compiled_models_exact algebra antisymm rowCheck rowExact
            problem symbolic compiled cache rowScheme solved values rows⟩
          simpa only [supported, compiled, shapeSolved] using
            ((RowFlowSchemes.solve_solved_iff _ rowScheme).mp rowSolved).2

theorem Scheme.models_instantiate (scheme : Scheme n) (algebra : RowFlowSchemes.Algebra Row)
    (rowParameter : Fin n → Row) (valueParameter : Fin scheme.size → Value Row) :
    scheme.Models algebra (scheme.values algebra rowParameter valueParameter) (scheme.rows algebra rowParameter) :=
  ⟨rowParameter, valueParameter, rfl, fun _ => RegularInferenceModel.equivalent_refl algebra.le _⟩

theorem Scheme.models_instances_iff (scheme : Scheme n) (algebra : RowFlowSchemes.Algebra Row)
    (output : Fin n) (expected : Comp (model algebra)) :
    (∃ values rows, scheme.Models algebra values rows ∧ Comp.le (model algebra) (values output, rows output) expected) ↔
      scheme.Instance algebra output expected := by
  constructor
  · rintro ⟨values, rows, ⟨rowParameter, valueParameter, rowsEqual, equivalent⟩, below⟩
    refine ⟨rowParameter, valueParameter,
      RegularInferenceModel.subtype_trans (equivalent output).1 below.1, ?_⟩
    change algebra.le (scheme.rows algebra rowParameter output) expected.2
    rw [rowsEqual]
    exact below.2
  · rintro ⟨rowParameter, valueParameter, below⟩
    exact ⟨scheme.values algebra rowParameter valueParameter, scheme.rows algebra rowParameter,
      scheme.models_instantiate algebra rowParameter valueParameter, below⟩

theorem Result.models_instances_iff (result : Result n) (algebra : RowFlowSchemes.Algebra Row)
    (output : Fin n) (expected : Comp (model algebra)) :
    (∃ values rows, result.Models algebra values rows ∧ Comp.le (model algebra) (values output, rows output) expected) ↔
      result.Instance algebra output expected := by
  cases result with
  | unsupported | rejected => simp [Result.Models, Result.Instance]
  | inferred scheme => exact scheme.models_instances_iff algebra output expected

/-- Pointwise model exactness for the actual symbolic computation. All
original value and row assignments are retained in the left-hand statement. -/
theorem infer_models_exact (algebra : RowFlowSchemes.Algebra Row)
    (antisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (problem : ConstraintProblems.Problem n) (accepted : supported problem = true)
    (values : Fin n → Value Row) (rows : Fin n → Row) :
    problem.Holds (model algebra) values rows ↔ (infer problem).Models algebra values rows := by
  have correct := infer_correct algebra antisymm problem
  cases returned : infer problem with
  | unsupported =>
      rw [returned] at correct
      have absent : supported problem = false := correct
      rw [accepted] at absent
      cases absent
  | rejected =>
      rw [returned] at correct
      exact ⟨fun realized => correct.2 ⟨values, rows, realized⟩, False.elim⟩
  | inferred scheme =>
      rw [returned] at correct
      exact correct.2 values rows

/-- Every instance of the original paired source problem is exactly an
instance of the computed joint scheme. No row parameters are defaulted. -/
theorem infer_instances_exact (algebra : RowFlowSchemes.Algebra Row)
    (antisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (problem : ConstraintProblems.Problem n) (accepted : supported problem = true)
    (output : Fin n) (expected : Comp (model algebra)) :
    problem.Instance (model algebra) output expected ↔ (infer problem).Instance algebra output expected := by
  rw [← Result.models_instances_iff]
  constructor
  · rintro ⟨values, rows, realized, below⟩
    exact ⟨values, rows, (infer_models_exact algebra antisymm problem accepted values rows).mp realized, below⟩
  · rintro ⟨values, rows, realized, below⟩
    exact ⟨values, rows, (infer_models_exact algebra antisymm problem accepted values rows).mpr realized, below⟩

theorem infer_rejected_iff (algebra : RowFlowSchemes.Algebra Row)
    (antisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (problem : ConstraintProblems.Problem n) :
    (infer problem).status = .rejected ↔
      supported problem = true ∧ ¬ ∃ values rows, problem.Holds (model algebra) values rows := by
  have correct := infer_correct algebra antisymm problem
  cases returned : infer problem with
  | unsupported =>
      rw [returned] at correct
      have absent : supported problem = false := correct
      simp [Result.status, absent]
  | rejected =>
      rw [returned] at correct
      exact ⟨fun _ => correct, fun _ => rfl⟩
  | inferred scheme =>
      rw [returned] at correct
      have existsModel : ∃ values rows, problem.Holds (model algebra) values rows :=
        ⟨scheme.values algebra (fun _ => algebra.empty) (fun _ => .bottom), scheme.rows algebra (fun _ => algebra.empty),
          (correct.2 _ _).mpr (scheme.models_instantiate algebra (fun _ => algebra.empty) (fun _ => .bottom))⟩
      simp [Result.status, existsModel]

theorem infer_inferred_iff (algebra : RowFlowSchemes.Algebra Row)
    (antisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (problem : ConstraintProblems.Problem n) :
    (infer problem).status = .inferred ↔
      supported problem = true ∧ ∃ values rows, problem.Holds (model algebra) values rows := by
  have correct := infer_correct algebra antisymm problem
  cases returned : infer problem with
  | unsupported =>
      rw [returned] at correct
      have absent : supported problem = false := correct
      simp [Result.status, absent]
  | rejected =>
      rw [returned] at correct
      simp [Result.status, correct.2]
  | inferred scheme =>
      rw [returned] at correct
      have existsModel : ∃ values rows, problem.Holds (model algebra) values rows :=
        ⟨scheme.values algebra (fun _ => algebra.empty) (fun _ => .bottom), scheme.rows algebra (fun _ => algebra.empty),
          (correct.2 _ _).mpr (scheme.models_instantiate algebra (fun _ => algebra.empty) (fun _ => .bottom))⟩
      simp [Result.status, correct.1, existsModel]

theorem infer_inferred_sound (algebra : RowFlowSchemes.Algebra Row)
    (antisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (problem : ConstraintProblems.Problem n) (scheme : Scheme n)
    (returned : infer problem = .inferred scheme)
    (rowParameter : Fin n → Row) (valueParameter : Fin scheme.size → Value Row) :
    problem.Holds (model algebra) (scheme.values algebra rowParameter valueParameter) (scheme.rows algebra rowParameter) := by
  have correct := infer_correct algebra antisymm problem
  rw [returned] at correct
  exact (correct.2 _ _).mpr (scheme.models_instantiate algebra rowParameter valueParameter)

theorem infer_inferred_instances_exact (algebra : RowFlowSchemes.Algebra Row)
    (antisymm : ∀ {left right}, algebra.le left right → algebra.le right left → left = right)
    (problem : ConstraintProblems.Problem n) (scheme : Scheme n)
    (returned : infer problem = .inferred scheme) (output : Fin n) (expected : Comp (model algebra)) :
    problem.Instance (model algebra) output expected ↔ scheme.Instance algebra output expected := by
  have correct := infer_correct algebra antisymm problem
  rw [returned] at correct
  have exactInstances := infer_instances_exact algebra antisymm problem correct.1 output expected
  simpa only [returned, Result.Instance] using exactInstances

end Yulang.JointConstraintInference
