import Yulang.TypeConstraintGraphEquivalence
import Yulang.RegularInferenceModel

/-!
# Executable principal inference from source type inequalities

Rows have a fixed interpretation in this entry point. The input is the actual
finite list of `TyTerm` inequalities, with shared unknowns and an output slot.
The entry compiles the terms, runs the terminating nested solver, and returns
a finite regular scheme whose parameters range freely over one inference
model. Unsupported syntax, inconsistent constraints, and inferred schemes are
distinct results.

The public correctness statements concern this computation itself. They do
not ask a caller to supply a successful graph compiler or solver cache.
-/

namespace Yulang.TypeConstraintInference

open Inference TypeConstraintGraph

universe u

variable {m n : Nat} {Row : Type u}

abbrev Value (Row : Type u) := RegularInferenceModel.Ty Row

/-- The front decomposition uses exactly the existing lattice laws. -/
theorem latticeRules (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop) :
    LatticeRules (RegularInferenceModel.model Row empty join leRow) where
  union_is_join := RegularInferenceModel.union_is_join leRow
  inter_is_meet := RegularInferenceModel.inter_is_meet leRow

theorem recordMeaning_eq (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (value : Fin n → Value Row) (fields : List (Nat × Fin n)) :
    TypeConstraintGraph.recordMeaning (RegularInferenceModel.model Row empty join leRow) value fields =
      RegularInferenceModel.recordMeaning value fields := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
      obtain ⟨label, field⟩ := field
      simp only [TypeConstraintGraph.recordMeaning, RegularInferenceModel.recordMeaning_cons, ← ih]
      rfl

/-- Congruence is required only for fixed record spines. No law for an
unknown or malformed record tail is introduced. -/
theorem congruenceRules (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row) :
    TypeConstraintGraphEquivalence.CongruenceRules (RegularInferenceModel.model Row empty join leRow) where
  refl := RegularInferenceModel.subtype_refl leRow
  trans := RegularInferenceModel.subtype_trans
  pair := RegularInferenceModel.pair_equivalent
  variant := RegularInferenceModel.variant_equivalent
  arrow := RegularInferenceModel.arrow_equivalent rowRefl
  record := by
    intro size fields left right same
    rw [recordMeaning_eq empty join leRow left fields, recordMeaning_eq empty join leRow right fields]
    exact RegularInferenceModel.recordMeaning_equivalent leRow fields left right same

theorem semanticNodeMeaning_iff (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (value : Fin n → Value Row) (actual : Value Row)
    (node : NestedValueSolver.Node n Row) :
    TypeConstraintGraphEquivalence.SemanticNodeMeaning
        (RegularInferenceModel.model Row empty join leRow) value actual node ↔
      (node ≠ .var → RegularInferenceModel.Equivalent leRow actual
        (RegularInferenceModel.rigidMeaning value node)) := by
  cases node with
  | record fields =>
      simp only [TypeConstraintGraphEquivalence.SemanticNodeMeaning,
        recordMeaning_eq empty join leRow value fields]
      simp [TypeConstraintGraphEquivalence.Equivalent, RegularInferenceModel.Equivalent,
        RegularInferenceModel.rigidMeaning, RigidValueLayers.rigidLayer,
        RegularInferenceModel.model, RegularInferenceModel.Subtype, RegularInferenceModel.recordMeaning]
  | _ =>
      simp [TypeConstraintGraphEquivalence.SemanticNodeMeaning,
        TypeConstraintGraphEquivalence.Equivalent, RegularInferenceModel.Equivalent,
        RegularInferenceModel.rigidMeaning, RigidValueLayers.rigidLayer,
        RegularInferenceModel.model, RegularInferenceModel.Subtype, RegularValueTypes.Layer.map]

/-- The compiler's generic semantic realizers and the recursive solver's
independent models give the same judgement on the common carrier. -/
theorem semanticGraphModels_iff (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (source : NestedValueSolver.Graph n Row)
    (constraints : List (NestedValueSolver.Edge n)) (value : Fin n → Value Row) :
    TypeConstraintGraphEquivalence.SemanticGraphModels
        (RegularInferenceModel.model Row empty join leRow) source constraints value ↔
      RegularInferenceModel.SemanticModels source constraints leRow value := by
  unfold TypeConstraintGraphEquivalence.SemanticGraphModels RegularInferenceModel.SemanticModels
  constructor
  · rintro ⟨realizes, satisfies⟩
    exact ⟨fun index => (semanticNodeMeaning_iff empty join leRow value (value index) (source index)).mp
      (realizes index), satisfies⟩
  · rintro ⟨realizes, satisfies⟩
    exact ⟨fun index => (semanticNodeMeaning_iff empty join leRow value (value index) (source index)).mpr
      (realizes index), satisfies⟩

/-- An inferred finite scheme. Its instance relation has only free parameters;
it neither retains nor rechecks the original inequalities. -/
structure Scheme (m : Nat) (Row : Type u) where
  size : Nat
  graph : NestedValueSolver.Graph size Row
  cache : List (NestedValueSolver.Edge size)
  input : Fin m → Fin size

def Scheme.ofCompiled (compiled : Compiled m Row) (cache : List (NestedValueSolver.Edge compiled.size)) :
    Scheme m Row := ⟨compiled.size, compiled.graph, cache, compiled.input⟩

def Scheme.instantiate (scheme : Scheme m Row) (parameter : Fin scheme.size → Value Row) : Fin m → Value Row :=
  fun index => RegularInferenceModel.solution scheme.graph scheme.cache parameter (scheme.input index)

def Scheme.Models (scheme : Scheme m Row) (leRow : Row → Row → Prop) (input : Fin m → Value Row) : Prop :=
  ∃ parameter : Fin scheme.size → Value Row,
    ∀ index, RegularInferenceModel.Equivalent leRow (scheme.instantiate parameter index) (input index)

def Scheme.Instance (scheme : Scheme m Row) (leRow : Row → Row → Prop)
    (output : Fin m) (expected : Value Row) : Prop :=
  ∃ parameter : Fin scheme.size → Value Row,
    RegularInferenceModel.Subtype leRow (scheme.instantiate parameter output) expected

inductive Status where
  | unsupported
  | rejected
  | inferred
  deriving DecidableEq, Repr

inductive Result (m : Nat) (Row : Type u) where
  | unsupported
  | rejected
  | inferred : Scheme m Row → Result m Row

def Result.status : Result m Row → Status
  | .unsupported => .unsupported
  | .rejected => .rejected
  | .inferred _ => .inferred

def Result.Models (leRow : Row → Row → Prop) (input : Fin m → Value Row) : Result m Row → Prop
  | .inferred scheme => scheme.Models leRow input
  | _ => False

def Result.Instance (leRow : Row → Row → Prop) (output : Fin m) (expected : Value Row) : Result m Row → Prop
  | .inferred scheme => scheme.Instance leRow output expected
  | _ => False

def supported (problem : Problem m) : Bool := (splitProblem problem).isSome

/-- The actual fixed-row entry: source terms, graph construction, finite
saturation, and the resulting regular scheme. No caller fuel is accepted. -/
def infer (empty : Row) (join : Row → Row → Row) (rowCheck : Row → Row → Bool)
    (rows : Fin m → Row) (problem : Problem m) : Result m Row :=
  match compile empty join rows problem with
  | none => .unsupported
  | some compiled =>
      match NestedValueSolver.solve rowCheck compiled.graph compiled.constraints with
      | none => .rejected
      | some cache => .inferred (Scheme.ofCompiled compiled cache)

theorem supported_eq_compile (empty : Row) (join : Row → Row → Row)
    (rows : Fin m → Row) (problem : Problem m) :
    supported problem = (compile empty join rows problem).isSome := by
  unfold compile
  split <;> simp_all [supported]

/-- A pointwise equivalent input assignment can replace just the shared input
nodes. This uses injectivity of the collector, not record-tail congruence. -/
private theorem replace_input_values (leRow : Row → Row → Prop)
    (reference : Fin m → Fin n) (injective : Function.Injective reference)
    (original : Fin n → Value Row) (input : Fin m → Value Row)
    (same : ∀ index, RegularInferenceModel.Equivalent leRow (original (reference index)) (input index)) :
    ∃ updated : Fin n → Value Row,
      (∀ node, RegularInferenceModel.Equivalent leRow (original node) (updated node)) ∧
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
    · exact RegularInferenceModel.equivalent_refl leRow _
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
    Holds (RegularInferenceModel.model Row empty join leRow) rows input problem ↔
      (Scheme.ofCompiled compiled cache).Models leRow input := by
  let regular := RegularInferenceModel.model Row empty join leRow
  constructor
  · intro accepted
    have generated := (TypeConstraintGraphEquivalence.compile_extend_exact regular
      (latticeRules empty join leRow) (congruenceRules empty join leRow rowRefl)
      rows problem compiled compiledOk input).mpr accepted
    have realized := (semanticGraphModels_iff empty join leRow compiled.graph compiled.constraints
      (compiled.extend regular rows input)).mp generated
    obtain ⟨parameter, equivalent⟩ :=
      (RegularInferenceModel.solve_models_exact rowCheck leRow rowRefl rowTrans rowExact
        compiled.graph compiled.constraints cache solved (compiled.extend regular rows input)).mp realized
    refine ⟨parameter, fun index => ?_⟩
    have agrees : compiled.extend regular rows input (compiled.input index) = input index :=
      congrFun (compile_restrict_extend regular rows problem compiled compiledOk input) index
    exact agrees ▸ equivalent (compiled.input index)
  · rintro ⟨parameter, equivalent⟩
    let generated := RegularInferenceModel.solution compiled.graph cache parameter
    have realized := RegularInferenceModel.solve_solution rowCheck leRow rowRefl
      (fun left right => (rowExact left right).mp) compiled.graph compiled.constraints cache solved parameter
    obtain ⟨updated, allSame, agrees⟩ := replace_input_values leRow compiled.input
      (compile_input_injective empty join rows problem compiled compiledOk) generated input equivalent
    have updatedModel := RegularInferenceModel.semanticModels_equivalent leRow rowRefl
      compiled.graph compiled.constraints generated updated realized allSame
    apply (TypeConstraintGraphEquivalence.compile_assignment_exact regular
      (latticeRules empty join leRow) (congruenceRules empty join leRow rowRefl)
      rows problem compiled compiledOk input).mpr
    exact ⟨updated,
      (semanticGraphModels_iff empty join leRow compiled.graph compiled.constraints updated).mpr updatedModel,
      funext agrees⟩

private theorem compiled_rejected_iff (empty : Row) (join : Row → Row → Row)
    (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (rows : Fin m → Row) (problem : Problem m) (compiled : Compiled m Row)
    (compiledOk : compile empty join rows problem = some compiled) :
    NestedValueSolver.solve rowCheck compiled.graph compiled.constraints = none ↔
      ¬ ∃ input : Fin m → Value Row,
        Holds (RegularInferenceModel.model Row empty join leRow) rows input problem := by
  rw [RegularInferenceModel.solve_none_iff rowCheck leRow rowRefl rowTrans rowExact]
  let regular := RegularInferenceModel.model Row empty join leRow
  constructor
  · rintro noGraph ⟨input, accepted⟩
    have generated := (TypeConstraintGraphEquivalence.compile_extend_exact regular
      (latticeRules empty join leRow) (congruenceRules empty join leRow rowRefl)
      rows problem compiled compiledOk input).mpr accepted
    exact noGraph ⟨compiled.extend regular rows input,
      (semanticGraphModels_iff empty join leRow compiled.graph compiled.constraints _).mp generated⟩
  · rintro noSource ⟨value, accepted⟩
    have generated := (semanticGraphModels_iff empty join leRow compiled.graph compiled.constraints value).mpr accepted
    exact noSource ⟨compiled.restrict value,
      ((TypeConstraintGraphEquivalence.compile_models_iff regular
        (latticeRules empty join leRow) (congruenceRules empty join leRow rowRefl)
        rows problem compiled compiledOk value).mp generated).2⟩

/-- The specification of each public result. Successful schemes represent
exactly all source assignments, up to the same semantic type equivalence. -/
def Result.Correct (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (rows : Fin m → Row) (problem : Problem m) : Result m Row → Prop
  | .unsupported => supported problem = false
  | .rejected => supported problem = true ∧
      ¬ ∃ input : Fin m → Value Row,
        Holds (RegularInferenceModel.model Row empty join leRow) rows input problem
  | .inferred scheme => supported problem = true ∧
      ∀ input : Fin m → Value Row,
        Holds (RegularInferenceModel.model Row empty join leRow) rows input problem ↔ scheme.Models leRow input

/-- Correctness of the computation on its actual source input, with no
successful compilation, cache, guessed model, or fuel supplied as a premise. -/
theorem infer_correct (empty : Row) (join : Row → Row → Row)
    (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (rows : Fin m → Row) (problem : Problem m) :
    (infer empty join rowCheck rows problem).Correct empty join leRow rows problem := by
  unfold infer
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
    (parameter : Fin scheme.size → Value Row) : scheme.Models leRow (scheme.instantiate parameter) :=
  ⟨parameter, fun _ => RegularInferenceModel.equivalent_refl leRow _⟩

theorem Scheme.models_instances_iff (scheme : Scheme m Row) (leRow : Row → Row → Prop)
    (output : Fin m) (expected : Value Row) :
    (∃ input : Fin m → Value Row,
      scheme.Models leRow input ∧ RegularInferenceModel.Subtype leRow (input output) expected) ↔
      scheme.Instance leRow output expected := by
  constructor
  · rintro ⟨input, ⟨parameter, equivalent⟩, below⟩
    exact ⟨parameter, RegularInferenceModel.subtype_trans (equivalent output).1 below⟩
  · rintro ⟨parameter, below⟩
    exact ⟨scheme.instantiate parameter, scheme.models_instantiate leRow parameter, below⟩

theorem Result.models_instances_iff (result : Result m Row) (leRow : Row → Row → Prop)
    (output : Fin m) (expected : Value Row) :
    (∃ input : Fin m → Value Row,
      result.Models leRow input ∧ RegularInferenceModel.Subtype leRow (input output) expected) ↔
      result.Instance leRow output expected := by
  cases result with
  | unsupported | rejected => simp [Result.Models, Result.Instance]
  | inferred scheme => exact scheme.models_instances_iff leRow output expected

/-- Support is a syntactic check. Unsupported input is never misreported as
inconsistent, even when its source constraints have a model. -/
theorem infer_unsupported_iff (empty : Row) (join : Row → Row → Row)
    (rowCheck : Row → Row → Bool) (rows : Fin m → Row) (problem : Problem m) :
    (infer empty join rowCheck rows problem).status = .unsupported ↔ supported problem = false := by
  rw [supported_eq_compile empty join rows problem]
  cases compiledOk : compile empty join rows problem with
  | none => simp [infer, compiledOk, Result.status]
  | some compiled =>
      cases solved : NestedValueSolver.solve rowCheck compiled.graph compiled.constraints <;>
        simp [infer, compiledOk, solved, Result.status]

/-- Exactness at every original input assignment for the checked fragment.
The result on the right is the actual call to `infer`, including rejection. -/
theorem infer_models_exact (empty : Row) (join : Row → Row → Row)
    (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (rows : Fin m → Row) (problem : Problem m) (accepted : supported problem = true)
    (input : Fin m → Value Row) :
    Holds (RegularInferenceModel.model Row empty join leRow) rows input problem ↔
      (infer empty join rowCheck rows problem).Models leRow input := by
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
    Holds (RegularInferenceModel.model Row empty join leRow) rows input problem ∧
      RegularInferenceModel.Subtype leRow (input output) expected

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
      (infer empty join rowCheck rows problem).Instance leRow output expected := by
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
    (infer empty join rowCheck rows problem).status = .rejected ↔
      supported problem = true ∧ ¬ ∃ input : Fin m → Value Row,
        Holds (RegularInferenceModel.model Row empty join leRow) rows input problem := by
  have correct := infer_correct empty join rowCheck leRow rowRefl rowTrans rowExact rows problem
  cases returned : infer empty join rowCheck rows problem with
  | unsupported =>
      rw [returned] at correct
      have absent : supported problem = false := correct
      simp [Result.status, absent]
  | rejected =>
      rw [returned] at correct
      exact ⟨fun _ => correct, fun _ => rfl⟩
  | inferred scheme =>
      rw [returned] at correct
      have existsInput : ∃ input : Fin m → Value Row,
          Holds (RegularInferenceModel.model Row empty join leRow) rows input problem :=
        ⟨scheme.instantiate (fun _ => .bottom),
          (correct.2 _).mpr (scheme.models_instantiate leRow (fun _ => .bottom))⟩
      simp [Result.status, existsInput]

theorem infer_inferred_iff (empty : Row) (join : Row → Row → Row)
    (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (rows : Fin m → Row) (problem : Problem m) :
    (infer empty join rowCheck rows problem).status = .inferred ↔
      supported problem = true ∧ ∃ input : Fin m → Value Row,
        Holds (RegularInferenceModel.model Row empty join leRow) rows input problem := by
  have correct := infer_correct empty join rowCheck leRow rowRefl rowTrans rowExact rows problem
  cases returned : infer empty join rowCheck rows problem with
  | unsupported =>
      rw [returned] at correct
      have absent : supported problem = false := correct
      simp [Result.status, absent]
  | rejected =>
      rw [returned] at correct
      simp [Result.status, correct.2]
  | inferred scheme =>
      rw [returned] at correct
      have existsInput : ∃ input : Fin m → Value Row,
          Holds (RegularInferenceModel.model Row empty join leRow) rows input problem :=
        ⟨scheme.instantiate (fun _ => .bottom),
          (correct.2 _).mpr (scheme.models_instantiate leRow (fun _ => .bottom))⟩
      simp [Result.status, correct.1, existsInput]

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
    Holds (RegularInferenceModel.model Row empty join leRow) rows (scheme.instantiate parameter) problem := by
  have correct := infer_correct empty join rowCheck leRow rowRefl rowTrans rowExact rows problem
  rw [returned] at correct
  exact (correct.2 _).mpr (scheme.models_instantiate leRow parameter)

theorem infer_inferred_instances_exact (empty : Row) (join : Row → Row → Row)
    (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (rows : Fin m → Row) (problem : Problem m) (scheme : Scheme m Row)
    (returned : infer empty join rowCheck rows problem = .inferred scheme)
    (output : Fin m) (expected : Value Row) :
    SourceInstance empty join leRow rows problem output expected ↔ scheme.Instance leRow output expected := by
  have correct := infer_correct empty join rowCheck leRow rowRefl rowTrans rowExact rows problem
  rw [returned] at correct
  have exactInstances := infer_instances_exact empty join rowCheck leRow rowRefl rowTrans rowExact
    rows problem correct.1 output expected
  simpa only [returned, Result.Instance] using exactInstances

end Yulang.TypeConstraintInference
