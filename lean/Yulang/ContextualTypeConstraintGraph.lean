import Yulang.ContextualNestedModels
import Yulang.TypeConstraintInference

/-!
# Source type constraints in the concrete contextual model

The existing type-term collector and compiler are unchanged. Its generic
lattice/congruence contracts are filled with proved contextual-order laws,
and its semantic graph model is connected to `ContextualNestedModels` on the
actual regular inference carrier. Shared source variables retain one value.

The compiler's syntax boundary remains its existing `splitProblem` check:
source unions, target intersections and fixed record spines are supported;
arbitrary open tails and presence-default terms are not added here.
-/

namespace Yulang.ContextualTypeConstraintGraph

open Inference TypeConstraintGraph

universe u
variable {Row : Type u} {m n : Nat}

abbrev model := @ProducerContextualRegular.model
abbrev Value := RegularInferenceModel.Ty

theorem latticeRules (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop) :
    LatticeRules (model Row empty join leRow) where
  union_is_join := ProducerContextualRegular.producerLe_union_iff
  inter_is_meet := fun a b c => ProducerContextualRegular.producerLe_inter_iff c a b

theorem recordMeaning_eq (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (value : Fin n → Value Row) (fields : List (Nat × Fin n)) :
    recordMeaning (model Row empty join leRow) value fields = RegularInferenceModel.recordMeaning value fields := by
  induction fields with
  | nil => rfl
  | cons field rest ih =>
      obtain ⟨label, field⟩ := field
      simp only [recordMeaning, RegularInferenceModel.recordMeaning_cons, ← ih]
      rfl

theorem recordMeaning_equivalent (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (fields : List (Nat × Fin n)) (left right : Fin n → Value Row)
    (same : ∀ field ∈ fields, TypeConstraintGraphEquivalence.Equivalent (model Row empty join leRow)
      (left field.2) (right field.2)) :
    TypeConstraintGraphEquivalence.Equivalent (model Row empty join leRow)
      (recordMeaning (model Row empty join leRow) left fields)
      (recordMeaning (model Row empty join leRow) right fields) := by
  induction fields with
  | nil => exact ProducerContextualRegular.producerEq_refl _
  | cons field rest ih =>
      exact ProducerContextualRegular.producerEq_record field.1
        (same field List.mem_cons_self) (ih (fun entry member => same entry (List.mem_cons_of_mem _ member)))

theorem congruenceRules (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c) :
    TypeConstraintGraphEquivalence.CongruenceRules (model Row empty join leRow) where
  refl := ProducerContextualRegular.producerLe_refl
  trans := ProducerContextualRegular.producerLe_trans
  pair := ProducerContextualRegular.producerEq_pair
  variant := ProducerContextualRegular.producerEq_variant
  arrow := ProducerContextualRegular.producerEq_arrow rowRefl rowTrans
  record := recordMeaning_equivalent empty join leRow

theorem semanticNodeMeaning_iff (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (value : Fin n → Value Row) (actual : Value Row)
    (node : NestedValueSolver.Node n Row) :
    TypeConstraintGraphEquivalence.SemanticNodeMeaning (model Row empty join leRow) value actual node ↔
      (node ≠ .var → ProducerContextualRegular.ProducerEq (RegularInferenceModel.graph Row) leRow
        actual ((RigidValueLayers.rigidLayer node).map (fun index => .node (value index)))) := by
  cases node with
  | record fields =>
      simp only [TypeConstraintGraphEquivalence.SemanticNodeMeaning, recordMeaning_eq]
      simp [TypeConstraintGraphEquivalence.Equivalent, ProducerContextualRegular.ProducerEq,
        RegularInferenceModel.recordMeaning, RigidValueLayers.rigidLayer,
        ProducerContextualRegular.model, model]
  | _ =>
      simp [TypeConstraintGraphEquivalence.SemanticNodeMeaning, TypeConstraintGraphEquivalence.Equivalent,
        ProducerContextualRegular.ProducerEq, RigidValueLayers.rigidLayer,
        ProducerContextualRegular.model, model, RegularInferenceModel.model, RegularValueTypes.Layer.map]

/-- Generic semantic realizers coincide with the independent contextual
solver model on the single concrete carrier used by source inference. -/
theorem semanticGraphModels_iff (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (graph : NestedValueSolver.Graph n Row)
    (constraints : List (NestedValueSolver.Edge n)) (value : Fin n → Value Row) :
    TypeConstraintGraphEquivalence.SemanticGraphModels (model Row empty join leRow) graph constraints value ↔
      ContextualNestedModels.Models leRow graph constraints (RegularInferenceModel.graph Row)
        (fun index => .node (value index)) := by
  constructor
  · rintro ⟨realizes, satisfies⟩
    exact ⟨fun index rigid => (semanticNodeMeaning_iff empty join leRow value (value index) (graph index)).mp
      (realizes index) rigid, satisfies⟩
  · rintro ⟨realizes, satisfies⟩
    exact ⟨fun index => (semanticNodeMeaning_iff empty join leRow value (value index) (graph index)).mpr
      (realizes index), satisfies⟩

/-- The real compiled graph preserves and reflects every assignment to the
original shared source variables. The graph is an actual compiler return,
not a guessed constraint system or a successful solver result. -/
theorem compile_assignment_exact (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rows : Fin m → Row) (problem : Problem m) (compiled : Compiled m Row)
    (returned : compile empty join rows problem = some compiled) (input : Fin m → Value Row) :
    Holds (model Row empty join leRow) rows input problem ↔
      ∃ value : Fin compiled.size → Value Row,
        ContextualNestedModels.Models leRow compiled.graph compiled.constraints
          (RegularInferenceModel.graph Row) (fun index => .node (value index)) ∧
            compiled.restrict value = input := by
  have exact := TypeConstraintGraphEquivalence.compile_assignment_exact (model Row empty join leRow)
    (latticeRules empty join leRow) (congruenceRules empty join leRow rowRefl rowTrans)
    rows problem compiled returned input
  constructor
  · intro holds
    obtain ⟨value, models, restriction⟩ := exact.mp holds
    exact ⟨value, (semanticGraphModels_iff empty join leRow _ _ _).mp models, restriction⟩
  · rintro ⟨value, models, restriction⟩
    exact exact.mpr ⟨value, (semanticGraphModels_iff empty join leRow _ _ _).mpr models, restriction⟩

theorem compile_output_instances_exact (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rows : Fin m → Row) (problem : Problem m) (compiled : Compiled m Row)
    (returned : compile empty join rows problem = some compiled) (output : Fin m) (expected : Value Row) :
    (∃ input, Holds (model Row empty join leRow) rows input problem ∧
      ProducerContextualRegular.ProducerLe (RegularInferenceModel.graph Row) leRow (input output) expected) ↔
      ∃ value : Fin compiled.size → Value Row,
        ContextualNestedModels.Models leRow compiled.graph compiled.constraints
          (RegularInferenceModel.graph Row) (fun index => .node (value index)) ∧
        ProducerContextualRegular.ProducerLe (RegularInferenceModel.graph Row) leRow
          (value (compiled.input output)) expected := by
  have exact := TypeConstraintGraphEquivalence.compile_output_instances_exact (model Row empty join leRow)
    (latticeRules empty join leRow) (congruenceRules empty join leRow rowRefl rowTrans)
    rows problem compiled returned output expected
  constructor
  · intro holds
    obtain ⟨value, models, below⟩ := exact.mp holds
    exact ⟨value, (semanticGraphModels_iff empty join leRow _ _ _).mp models, below⟩
  · rintro ⟨value, models, below⟩
    exact exact.mpr ⟨value, (semanticGraphModels_iff empty join leRow _ _ _).mpr models, below⟩

/-- Every free instantiation of the actual finite solver's accepted scheme
is a model in the same contextual inference carrier. -/
theorem solve_solution (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rowSound : ∀ left right, rowCheck left right = true → leRow left right)
    (graph : NestedValueSolver.Graph n Row) (constraints cache : List (NestedValueSolver.Edge n))
    (solved : NestedValueSolver.solve rowCheck graph constraints = some cache)
    (parameter : Fin n → Value Row) :
    ContextualNestedModels.Models leRow graph constraints (RegularInferenceModel.graph Row)
      (fun index => .node (RegularInferenceModel.solution graph cache parameter index)) :=
  ContextualNestedModels.old_models_preserved leRow rowTrans graph constraints _ _
    ((RegularInferenceModel.semanticModels_iff graph constraints leRow _).mp
      (RegularInferenceModel.solve_solution rowCheck leRow rowRefl rowSound graph constraints cache solved parameter))

/-- Rejection is exact on the concrete source carrier as well as on arbitrary
external regular graphs. No solve result or model is supplied by the caller. -/
theorem solve_none_iff (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (graph : NestedValueSolver.Graph n Row) (constraints : List (NestedValueSolver.Edge n)) :
    NestedValueSolver.solve rowCheck graph constraints = none ↔
      ¬ ∃ value : Fin n → Value Row,
        ContextualNestedModels.Models leRow graph constraints (RegularInferenceModel.graph Row)
          (fun index => .node (value index)) := by
  constructor
  · rintro rejected ⟨value, models⟩
    exact ContextualNestedModels.solve_rejects_model rowCheck leRow rowRefl rowTrans rowExact
      graph constraints rejected (RegularInferenceModel.graph Row) (fun index => .node (value index)) models
  · intro impossible
    cases solved : NestedValueSolver.solve rowCheck graph constraints with
    | none => rfl
    | some cache =>
        exact False.elim (impossible ⟨RegularInferenceModel.solution graph cache (fun _ => .bottom),
          solve_solution rowCheck leRow rowRefl rowTrans (fun left right => (rowExact left right).mp)
            graph constraints cache solved (fun _ => .bottom)⟩)

theorem compile_solve_none_iff (empty : Row) (join : Row → Row → Row)
    (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (rows : Fin m → Row) (problem : Problem m) (compiled : Compiled m Row)
    (returned : compile empty join rows problem = some compiled) :
    NestedValueSolver.solve rowCheck compiled.graph compiled.constraints = none ↔
      ¬ ∃ input : Fin m → Value Row, Holds (model Row empty join leRow) rows input problem := by
  rw [solve_none_iff rowCheck leRow rowRefl rowTrans rowExact]
  constructor
  · rintro noGraph ⟨input, holds⟩
    obtain ⟨value, models, _⟩ :=
      (compile_assignment_exact empty join leRow rowRefl rowTrans rows problem compiled returned input).mp holds
    exact noGraph ⟨value, models⟩
  · rintro noSource ⟨value, models⟩
    exact noSource ⟨compiled.restrict value,
      (compile_assignment_exact empty join leRow rowRefl rowTrans rows problem compiled returned _).mpr
        ⟨value, models, rfl⟩⟩

/-- The unchanged executable entry rejects exactly the supported contextual
constraint problems with no assignment. Success and fuel are not premises;
unsupported inputs retain their separate status. -/
theorem infer_rejected_iff (empty : Row) (join : Row → Row → Row)
    (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (rows : Fin m → Row) (problem : Problem m) :
    (TypeConstraintInference.infer empty join rowCheck rows problem).status = .rejected ↔
      TypeConstraintInference.supported problem = true ∧
        ¬ ∃ input : Fin m → Value Row, Holds (model Row empty join leRow) rows input problem := by
  rw [TypeConstraintInference.supported_eq_compile empty join rows problem]
  cases returned : compile empty join rows problem with
  | none => simp [TypeConstraintInference.infer, returned, TypeConstraintInference.Result.status]
  | some compiled =>
      have rejection := compile_solve_none_iff empty join rowCheck leRow rowRefl rowTrans rowExact
        rows problem compiled returned
      cases solved : NestedValueSolver.solve rowCheck compiled.graph compiled.constraints with
      | none =>
          simpa [TypeConstraintInference.infer, returned, solved,
            TypeConstraintInference.Result.status] using rejection
      | some cache =>
          simpa [TypeConstraintInference.infer, returned, solved,
            TypeConstraintInference.Result.status] using rejection

end Yulang.ContextualTypeConstraintGraph
