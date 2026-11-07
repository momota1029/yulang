import Yulang.ContextualTypeConstraintGraph
import Yulang.ContextualRegularInference

/-!
# Exact contextual instances of the existing type-constraint entry

The executable `infer`, result and scheme types, compiler and scheme evaluator
are aliases of `TypeConstraintInference`. This module changes only their
independent semantic specification to the contextual producer demand order.
All original shared unknowns are recovered up to that order's equivalence.

The public correctness theorem covers actual rejected/unsupported/inferred
results without a solver-success, independent-solution or fuel premise. The
supported grammar is exactly the existing type-term compiler's syntax gate;
no presence exact/default/open-tail constructors are silently added.
-/

namespace Yulang.ContextualTypeConstraintInference

open Inference TypeConstraintGraph

universe u
variable {m n : Nat} {Row : Type u}

abbrev Value := TypeConstraintInference.Value
abbrev model := @ContextualTypeConstraintGraph.model
abbrev Scheme := TypeConstraintInference.Scheme
abbrev Status := TypeConstraintInference.Status
abbrev Result := TypeConstraintInference.Result
abbrev infer := @TypeConstraintInference.infer
abbrev supported := @TypeConstraintInference.supported
theorem supported_eq_compile (empty : Row) (join : Row → Row → Row)
    (rows : Fin m → Row) (problem : Problem m) :
    supported problem = (compile empty join rows problem).isSome :=
  TypeConstraintInference.supported_eq_compile empty join rows problem

abbrev latticeRules := @ContextualTypeConstraintGraph.latticeRules
abbrev congruenceRules := @ContextualTypeConstraintGraph.congruenceRules
abbrev semanticGraphModels_iff := @ContextualTypeConstraintGraph.semanticGraphModels_iff

namespace Scheme

abbrev ofCompiled := @TypeConstraintInference.Scheme.ofCompiled
abbrev instantiate := @TypeConstraintInference.Scheme.instantiate

/-- Only free parameters and contextual equivalence occur here. The original
constraints are not retained as restrictions on parameter instantiation. -/
def Models (scheme : Scheme m Row) (leRow : Row → Row → Prop) (input : Fin m → Value Row) : Prop :=
  ∃ parameter : Fin scheme.size → Value Row,
    ∀ index, ContextualRegularInference.Equivalent leRow
      (instantiate scheme parameter index) (input index)

def Instance (scheme : Scheme m Row) (leRow : Row → Row → Prop)
    (output : Fin m) (expected : Value Row) : Prop :=
  ∃ parameter : Fin scheme.size → Value Row,
    ContextualRegularInference.Le leRow (instantiate scheme parameter output) expected

end Scheme

namespace Result

abbrev status := @TypeConstraintInference.Result.status

def Models (leRow : Row → Row → Prop) (input : Fin m → Value Row) : Result m Row → Prop
  | .inferred scheme => Scheme.Models scheme leRow input
  | _ => False

def Instance (leRow : Row → Row → Prop) (output : Fin m) (expected : Value Row) : Result m Row → Prop
  | .inferred scheme => Scheme.Instance scheme leRow output expected
  | _ => False

end Result

/-- Replacing shared source inputs requires the compiler's proved injection,
not congruence for arbitrary unknown record tails. -/
private theorem replace_input_values (leRow : Row → Row → Prop)
    (reference : Fin m → Fin n) (injective : Function.Injective reference)
    (original : Fin n → Value Row) (input : Fin m → Value Row)
    (same : ∀ index, ContextualRegularInference.Equivalent leRow
      (original (reference index)) (input index)) :
    ∃ updated : Fin n → Value Row,
      (∀ node, ContextualRegularInference.Equivalent leRow (original node) (updated node)) ∧
      ∀ index, updated (reference index) = input index := by
  classical
  let updated := fun node => if found : ∃ index, reference index = node then
    input (Classical.choose found) else original node
  refine ⟨updated, ?_, ?_⟩
  · intro node
    dsimp only [updated]
    split
    · rename_i found
      have atNode := Classical.choose_spec found
      simpa only [atNode] using same (Classical.choose found)
    · exact ProducerContextualRegular.producerEq_refl _
  · intro index
    dsimp only [updated]
    split
    · rename_i found
      have chosen : Classical.choose found = index := injective (Classical.choose_spec found)
      exact congrArg input chosen
    · rename_i absent
      exact False.elim (absent ⟨index, rfl⟩)

private theorem compiled_assignments_exact (empty : Row) (join : Row → Row → Row)
    (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (rows : Fin m → Row) (problem : Problem m) (compiled : Compiled m Row)
    (compiledOk : compile empty join rows problem = some compiled)
    (cache : List (NestedValueSolver.Edge compiled.size))
    (solved : NestedValueSolver.solve rowCheck compiled.graph compiled.constraints = some cache)
    (input : Fin m → Value Row) :
    Holds (model Row empty join leRow) rows input problem ↔
      Scheme.Models (Scheme.ofCompiled compiled cache) leRow input := by
  constructor
  · intro accepted
    obtain ⟨value, realized, agrees⟩ :=
      (ContextualTypeConstraintGraph.compile_assignment_exact empty join leRow rowRefl rowTrans
        rows problem compiled compiledOk input).mp accepted
    obtain ⟨parameter, equivalent⟩ :=
      (ContextualRegularInference.solve_models_exact rowCheck leRow rowRefl rowTrans rowExact
        compiled.graph compiled.constraints cache solved value).mp realized
    refine ⟨parameter, fun index => ?_⟩
    have atInput : value (compiled.input index) = input index := congrFun agrees index
    exact atInput ▸ equivalent (compiled.input index)
  · rintro ⟨parameter, equivalent⟩
    let generated := RegularInferenceModel.solution compiled.graph cache parameter
    have realized := ContextualRegularInference.solve_solution rowCheck leRow rowRefl rowTrans rowExact
      compiled.graph compiled.constraints cache solved parameter
    obtain ⟨updated, allSame, agrees⟩ := replace_input_values leRow compiled.input
      (compile_input_injective empty join rows problem compiled compiledOk) generated input equivalent
    have updatedModel := ContextualCoalescing.models_equivalent leRow rowRefl rowTrans
      compiled.graph compiled.constraints (RegularInferenceModel.graph Row)
      (fun index => .node (generated index)) (fun index => .node (updated index)) realized allSame
    exact (ContextualTypeConstraintGraph.compile_assignment_exact empty join leRow rowRefl rowTrans
      rows problem compiled compiledOk input).mpr ⟨updated, updatedModel, funext agrees⟩

private theorem compiled_rejected_iff (empty : Row) (join : Row → Row → Row)
    (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (rows : Fin m → Row) (problem : Problem m) (compiled : Compiled m Row)
    (compiledOk : compile empty join rows problem = some compiled) :
    NestedValueSolver.solve rowCheck compiled.graph compiled.constraints = none ↔
      ¬ ∃ input : Fin m → Value Row, Holds (model Row empty join leRow) rows input problem :=
  ContextualTypeConstraintGraph.compile_solve_none_iff empty join rowCheck leRow rowRefl rowTrans
    rowExact rows problem compiled compiledOk

/-- The specification of each public result. Successful schemes represent
exactly all source assignments, up to the same semantic type equivalence. -/
def Result.Correct (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (rows : Fin m → Row) (problem : Problem m) : Result m Row → Prop
  | .unsupported => supported problem = false
  | .rejected => supported problem = true ∧
      ¬ ∃ input : Fin m → Value Row,
        Holds (model Row empty join leRow) rows input problem
  | .inferred scheme => supported problem = true ∧
      ∀ input : Fin m → Value Row,
        Holds (model Row empty join leRow) rows input problem ↔ Scheme.Models scheme leRow input

/-- Correctness of the computation on its actual source input, with no
successful compilation, cache, guessed model, or fuel supplied as a premise. -/
theorem infer_correct (empty : Row) (join : Row → Row → Row)
    (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (rows : Fin m → Row) (problem : Problem m) :
    Result.Correct empty join leRow rows problem (infer empty join rowCheck rows problem) := by
  unfold infer TypeConstraintInference.infer
  cases compiledOk : compile empty join rows problem with
  | none =>
      change supported problem = false
      rw [supported_eq_compile empty join rows problem, compiledOk]
      rfl
  | some compiled =>
      have accepted : supported problem = true := by
        rw [supported_eq_compile empty join rows problem, compiledOk]
        rfl
      cases solved : NestedValueSolver.solve rowCheck compiled.graph compiled.constraints with
      | none =>
          simp only [solved, Result.Correct]
          exact ⟨accepted, (compiled_rejected_iff empty join rowCheck leRow rowRefl rowTrans rowExact
            rows problem compiled compiledOk).mp solved⟩
      | some cache =>
          simp only [solved, Result.Correct]
          exact ⟨accepted, fun input => compiled_assignments_exact empty join rowCheck leRow rowRefl
            rowTrans rowExact rows problem compiled compiledOk cache solved input⟩

theorem Scheme.models_instantiate (scheme : Scheme m Row) (leRow : Row → Row → Prop)
    (parameter : Fin scheme.size → Value Row) : Scheme.Models scheme leRow (Scheme.instantiate scheme parameter) :=
  ⟨parameter, fun _ => ProducerContextualRegular.producerEq_refl _⟩

theorem Scheme.models_instances_iff (scheme : Scheme m Row) (leRow : Row → Row → Prop)
    (output : Fin m) (expected : Value Row) :
    (∃ input : Fin m → Value Row,
      Scheme.Models scheme leRow input ∧ ContextualRegularInference.Le leRow (input output) expected) ↔
      Scheme.Instance scheme leRow output expected := by
  constructor
  · rintro ⟨input, ⟨parameter, equivalent⟩, below⟩
    exact ⟨parameter, ProducerContextualRegular.producerLe_trans (equivalent output).1 below⟩
  · rintro ⟨parameter, below⟩
    exact ⟨Scheme.instantiate scheme parameter, Scheme.models_instantiate scheme leRow parameter, below⟩

theorem Result.models_instances_iff (result : Result m Row) (leRow : Row → Row → Prop)
    (output : Fin m) (expected : Value Row) :
    (∃ input : Fin m → Value Row,
      Result.Models leRow input result ∧ ContextualRegularInference.Le leRow (input output) expected) ↔
      Result.Instance leRow output expected result := by
  cases result with
  | unsupported | rejected => simp [Result.Models, Result.Instance]
  | inferred scheme => exact Scheme.models_instances_iff scheme leRow output expected

/-- Support is a syntactic check. Unsupported input is never misreported as
inconsistent, even when its source constraints have a model. -/
theorem infer_unsupported_iff (empty : Row) (join : Row → Row → Row)
    (rowCheck : Row → Row → Bool) (rows : Fin m → Row) (problem : Problem m) :
    Result.status (infer empty join rowCheck rows problem) = .unsupported ↔ supported problem = false := by
  rw [supported_eq_compile empty join rows problem]
  cases compiledOk : compile empty join rows problem with
  | none => simp [infer, TypeConstraintInference.infer, compiledOk, Result.status, TypeConstraintInference.Result.status]
  | some compiled =>
      cases solved : NestedValueSolver.solve rowCheck compiled.graph compiled.constraints <;>
        simp [infer, TypeConstraintInference.infer, compiledOk, solved, Result.status, TypeConstraintInference.Result.status]

/-- Exactness at every original input assignment for the checked fragment.
The result on the right is the actual call to `infer`, including rejection. -/
theorem infer_models_exact (empty : Row) (join : Row → Row → Row)
    (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (rows : Fin m → Row) (problem : Problem m) (accepted : supported problem = true)
    (input : Fin m → Value Row) :
    Holds (model Row empty join leRow) rows input problem ↔
      Result.Models leRow input (infer empty join rowCheck rows problem) := by
  have correct := infer_correct empty join rowCheck leRow rowRefl rowTrans rowExact rows problem
  cases returned : infer empty join rowCheck rows problem with
  | unsupported =>
      rw [returned] at correct
      have absent : supported problem = false := correct
      rw [accepted] at absent
      cases absent
  | rejected =>
      rw [returned] at correct
      exact ⟨fun model => correct.2 ⟨input, model⟩, False.elim⟩
  | inferred scheme =>
      rw [returned] at correct
      exact correct.2 input

def SourceInstance (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (rows : Fin m → Row) (problem : Problem m) (output : Fin m) (expected : Value Row) : Prop :=
  ∃ input : Fin m → Value Row,
    Holds (model Row empty join leRow) rows input problem ∧
      ContextualRegularInference.Le leRow (input output) expected

/-- All upward output instances of the original source constraints are
exactly all free instances of the computed scheme, or none after rejection. -/
theorem infer_instances_exact (empty : Row) (join : Row → Row → Row)
    (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (rows : Fin m → Row) (problem : Problem m) (accepted : supported problem = true)
    (output : Fin m) (expected : Value Row) :
    SourceInstance empty join leRow rows problem output expected ↔
      Result.Instance leRow output expected (infer empty join rowCheck rows problem) := by
  rw [← Result.models_instances_iff]
  constructor
  · rintro ⟨input, model, below⟩
    exact ⟨input, (infer_models_exact empty join rowCheck leRow rowRefl rowTrans rowExact
      rows problem accepted input).mp model, below⟩
  · rintro ⟨input, model, below⟩
    exact ⟨input, (infer_models_exact empty join rowCheck leRow rowRefl rowTrans rowExact
      rows problem accepted input).mpr model, below⟩

/-- A rejection is exactly an inconsistent supported input. Unsupported
syntax is intentionally excluded from this equivalence. -/
theorem infer_rejected_iff (empty : Row) (join : Row → Row → Row)
    (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (rows : Fin m → Row) (problem : Problem m) :
    Result.status (infer empty join rowCheck rows problem) = .rejected ↔
      supported problem = true ∧ ¬ ∃ input : Fin m → Value Row,
        Holds (model Row empty join leRow) rows input problem := by
  have correct := infer_correct empty join rowCheck leRow rowRefl rowTrans rowExact rows problem
  cases returned : infer empty join rowCheck rows problem with
  | unsupported =>
      rw [returned] at correct
      have absent : supported problem = false := correct
      simp [Result.status, TypeConstraintInference.Result.status, absent]
  | rejected =>
      rw [returned] at correct
      exact ⟨fun _ => correct, fun _ => rfl⟩
  | inferred scheme =>
      rw [returned] at correct
      have existsInput : ∃ input : Fin m → Value Row,
          Holds (model Row empty join leRow) rows input problem :=
        ⟨Scheme.instantiate scheme (fun _ => .bottom),
          (correct.2 _).mpr (Scheme.models_instantiate scheme leRow (fun _ => .bottom))⟩
      simp [Result.status, TypeConstraintInference.Result.status, existsInput]

theorem infer_inferred_iff (empty : Row) (join : Row → Row → Row)
    (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (rows : Fin m → Row) (problem : Problem m) :
    Result.status (infer empty join rowCheck rows problem) = .inferred ↔
      supported problem = true ∧ ∃ input : Fin m → Value Row,
        Holds (model Row empty join leRow) rows input problem := by
  have correct := infer_correct empty join rowCheck leRow rowRefl rowTrans rowExact rows problem
  cases returned : infer empty join rowCheck rows problem with
  | unsupported =>
      rw [returned] at correct
      have absent : supported problem = false := correct
      simp [Result.status, TypeConstraintInference.Result.status, absent]
  | rejected =>
      rw [returned] at correct
      simp [Result.status, TypeConstraintInference.Result.status, correct.2]
  | inferred scheme =>
      rw [returned] at correct
      have existsInput : ∃ input : Fin m → Value Row,
          Holds (model Row empty join leRow) rows input problem :=
        ⟨Scheme.instantiate scheme (fun _ => .bottom),
          (correct.2 _).mpr (Scheme.models_instantiate scheme leRow (fun _ => .bottom))⟩
      simp [Result.status, TypeConstraintInference.Result.status, correct.1, existsInput]

/-- Every free instantiation of a returned scheme solves the original terms.
The only operational premise names the actual public inference result. -/
theorem infer_inferred_sound (empty : Row) (join : Row → Row → Row)
    (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (rows : Fin m → Row) (problem : Problem m) (scheme : Scheme m Row)
    (returned : infer empty join rowCheck rows problem = .inferred scheme)
    (parameter : Fin scheme.size → Value Row) :
    Holds (model Row empty join leRow) rows (Scheme.instantiate scheme parameter) problem := by
  have correct := infer_correct empty join rowCheck leRow rowRefl rowTrans rowExact rows problem
  rw [returned] at correct
  exact (correct.2 _).mpr (Scheme.models_instantiate scheme leRow parameter)

theorem infer_inferred_instances_exact (empty : Row) (join : Row → Row → Row)
    (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (rows : Fin m → Row) (problem : Problem m) (scheme : Scheme m Row)
    (returned : infer empty join rowCheck rows problem = .inferred scheme)
    (output : Fin m) (expected : Value Row) :
    SourceInstance empty join leRow rows problem output expected ↔ Scheme.Instance scheme leRow output expected := by
  have correct := infer_correct empty join rowCheck leRow rowRefl rowTrans rowExact rows problem
  rw [returned] at correct
  have exactInstances := infer_instances_exact empty join rowCheck leRow rowRefl rowTrans rowExact
    rows problem correct.1 output expected
  simpa only [returned, Result.Instance] using exactInstances

end Yulang.ContextualTypeConstraintInference
