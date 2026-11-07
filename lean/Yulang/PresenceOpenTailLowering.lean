import Yulang.PresenceOpenTailTransport

/-!
# Shared regular-block lowering of compiled open-tail constraints

The actual source compiler records a finite source term at every slot. This
provenance permits a total lowering which inlines exactly the same-depth
dependencies (lattice children and record tails), while leaving constructor
payloads as references to the original shared slots. Arbitrary input types,
including cyclic regular blocks, remain external parameters.

The lowering does not solve the original constraints. It constructs a finite
regular representation of their unique constructor extension for every input
assignment, then preserves and reflects all constraints and all finite
observations. It does not handle a new solver graph whose unguarded tail
dependencies have no finite source-term provenance.
-/

namespace Yulang.PresenceOpenTailLowering

open Inference
open RegularValueTypes (Layer observe)
open RegularInferenceModel (State graph)
open OpenRecordConstraintGraph (Pool)
open PresenceOpenTailTransport (observationModel)

universe u
variable {Row : Type u} {m : Nat}

abbrev Ref (pool : Pool m) (Row : Type u) := Fin pool.size ⊕ State Row

/-- Shared payloads remain guarded references. The finite source syntax,
not observation fuel, drives expansion of same-depth dependencies. -/
def lowerLayer (pool : Pool m) (empty : Row) (join : Row → Row → Row)
    (input : Fin m → RegularInferenceModel.Ty Row) (rows : Fin m → Row) :
    (term : TyTerm (Fin m)) → term ∈ pool.terms → Layer Row (Ref pool Row)
  | .var index, _ => (input index).map Sum.inr
  | .base scalar, _ => .base scalar
  | .bottom, _ => .bottom
  | .top, _ => .top
  | .union first last, member =>
      .union (lowerLayer pool empty join input rows first
        (pool.closed _ member first (by simp [TypeConstraintGraph.subterms])))
        (lowerLayer pool empty join input rows last
          (pool.closed _ member last (by simp [TypeConstraintGraph.subterms])))
  | .inter first last, member =>
      .inter (lowerLayer pool empty join input rows first
        (pool.closed _ member first (by simp [TypeConstraintGraph.subterms])))
        (lowerLayer pool empty join input rows last
          (pool.closed _ member last (by simp [TypeConstraintGraph.subterms])))
  | .pair first last, member =>
      .pair (.inl (pool.child _ member first (by simp [TypeConstraintGraph.subterms])))
        (.inl (pool.child _ member last (by simp [TypeConstraintGraph.subterms])))
  | .emptyRecord, _ => .emptyRecord
  | .record label head tail, member =>
      .record label (.inl (pool.child _ member head (by simp [TypeConstraintGraph.subterms])))
        (lowerLayer pool empty join input rows tail
          (pool.closed _ member tail (by simp [TypeConstraintGraph.subterms])))
  | .variant label payload, member =>
      .variant label (.inl (pool.child _ member payload (by simp [TypeConstraintGraph.subterms])))
  | .arrow arg argRow result resultRow, member =>
      .arrow (.inl (pool.child _ member arg (by simp [TypeConstraintGraph.subterms])))
        (TypeConstraintGraph.rowEval empty join rows argRow)
        (.inl (pool.child _ member result (by simp [TypeConstraintGraph.subterms])))
        (TypeConstraintGraph.rowEval empty join rows resultRow)

def body (pool : Pool m) (empty : Row) (join : Row → Row → Row)
    (input : Fin m → RegularInferenceModel.Ty Row) (rows : Fin m → Row) :
    Fin pool.size → Layer Row (Ref pool Row) :=
  fun index => lowerLayer pool empty join input rows (pool.termAt index) (pool.at_mem index)

/-- The independent evaluation used for comparison is the existing model's
term evaluation, not evaluation of the generated block. -/
def evaluationRef (pool : Pool m) (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (input : Fin m → RegularInferenceModel.Ty Row) (rows : Fin m → Row) : Ref pool Row → State Row :=
  Sum.elim (fun index => .node (TypeConstraintGraph.evaluate
    (observationModel empty join leRow compare) rows input (pool.termAt index))) id

theorem lowerLayer_map_evaluation (pool : Pool m) (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (input : Fin m → RegularInferenceModel.Ty Row) (rows : Fin m → Row)
    (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    (lowerLayer pool empty join input rows term member).map
        (evaluationRef pool empty join leRow compare input rows) =
      TypeConstraintGraph.evaluate (observationModel empty join leRow compare) rows input term := by
  induction term with
  | var index =>
      simp only [lowerLayer, Layer.map_comp, evaluationRef, Sum.elim_inr,
        id_eq, TypeConstraintGraph.evaluate, TyTerm.eval]
      exact Layer.map_id _
  | base | bottom | top | emptyRecord => rfl
  | union first last ihf ihl | inter first last ihf ihl =>
      simp only [lowerLayer, Layer.map, TypeConstraintGraph.evaluate, TyTerm.eval,
        observationModel, RegularInferenceModel.model, ihf, ihl]
  | pair first last =>
      simp only [lowerLayer, Layer.map, evaluationRef, Sum.elim_inl, Pool.child,
        Pool.termAt_reference, TypeConstraintGraph.evaluate, TyTerm.eval,
        observationModel, RegularInferenceModel.model]
  | record label head tail ihh iht =>
      simp only [lowerLayer, Layer.map, evaluationRef, Sum.elim_inl, Pool.child,
        Pool.termAt_reference]
      exact congrArg (Layer.record label (.node (TypeConstraintGraph.evaluate
        (observationModel empty join leRow compare) rows input head))) (iht _)
  | variant label payload =>
      simp only [lowerLayer, Layer.map, evaluationRef, Sum.elim_inl, Pool.child,
        Pool.termAt_reference, TypeConstraintGraph.evaluate, TyTerm.eval,
        observationModel, RegularInferenceModel.model]
  | arrow arg argRow result resultRow =>
      simp only [lowerLayer, Layer.map, evaluationRef, Sum.elim_inl, Pool.child,
        Pool.termAt_reference, TypeConstraintGraph.evaluate, TyTerm.eval,
        observationModel, RegularInferenceModel.model]
      congr 1
      · exact TypeConstraintGraph.rowEval_eq (observationModel empty join leRow compare) rows input argRow
      · exact TypeConstraintGraph.rowEval_eq (observationModel empty join leRow compare) rows input resultRow

theorem evaluation_morphism (pool : Pool m) (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (input : Fin m → RegularInferenceModel.Ty Row) (rows : Fin m → Row) (state : Ref pool Row) :
    ((RegularInferenceModel.blockGraph (body pool empty join input rows)) state).map
        (evaluationRef pool empty join leRow compare input rows) =
      graph Row (evaluationRef pool empty join leRow compare input rows state) := by
  cases state with
  | inl index => exact lowerLayer_map_evaluation pool empty join leRow compare input rows _ _
  | inr state =>
      simp only [RegularInferenceModel.blockGraph, Layer.map_comp, evaluationRef, Sum.elim_inr, id_eq]
      exact Layer.map_id _

/-- A finite shared block for all original slots. Constructing this block
requires no solution of the constraints and no bound on observation depth. -/
def close (pool : Pool m) (empty : Row) (join : Row → Row → Row)
    (input : Fin m → RegularInferenceModel.Ty Row) (rows : Fin m → Row)
    (index : Fin pool.size) : State Row :=
  RegularInferenceModel.closeBlock (body pool empty join input rows) index

/-- Every lowered slot has exactly the independently evaluated finite
observations, including all arrow information and external cyclic blocks. -/
theorem close_observe_exact (pool : Pool m) (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (input : Fin m → RegularInferenceModel.Ty Row) (rows : Fin m → Row)
    (index : Fin pool.size) (depth : Nat) :
    observe (graph Row) depth (close pool empty join input rows index) =
      observe (graph Row) depth (.node (TypeConstraintGraph.evaluate
        (observationModel empty join leRow compare) rows input (pool.termAt index))) := by
  have closure := RegularInferenceModel.block_observe (body pool empty join input rows)
    depth (Sum.inl index)
  have evaluation := RegularValueTypes.observe_morphism (graph Row)
    (evaluationRef pool empty join leRow compare input rows)
    (evaluation_morphism pool empty join leRow compare input rows) depth (Sum.inl index)
  exact closure.trans evaluation.symm

/-- The root layer is the value type used by the inference model. -/
def lowerValue (pool : Pool m) (empty : Row) (join : Row → Row → Row)
    (input : Fin m → RegularInferenceModel.Ty Row) (rows : Fin m → Row)
    (index : Fin pool.size) : RegularInferenceModel.Ty Row :=
  graph Row (close pool empty join input rows index)

theorem lowerValue_observe_exact (pool : Pool m) (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (input : Fin m → RegularInferenceModel.Ty Row) (rows : Fin m → Row)
    (index : Fin pool.size) (depth : Nat) :
    (lowerValue pool empty join input rows index).eval (observe (graph Row) depth) =
      (TypeConstraintGraph.evaluate (observationModel empty join leRow compare) rows input
        (pool.termAt index)).eval (observe (graph Row) depth) :=
  close_observe_exact pool empty join leRow compare input rows index (depth + 1)

/-- Every mask on every original slot is preserved by the constructed
lowering, not only the unmasked outer value. -/
theorem lowerValue_mask_exact (pool : Pool m) (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (input : Fin m → RegularInferenceModel.Ty Row) (rows : Fin m → Row)
    (index : Fin pool.size) (depth : Nat) (hidden : List Nat) (item : SourceDataRuntime.Value) :
    PresenceLegacyBridge.translate
        ((lowerValue pool empty join input rows index).eval (observe (graph Row) depth)) hidden item ↔
      PresenceLegacyBridge.translate
        ((TypeConstraintGraph.evaluate (observationModel empty join leRow compare) rows input
          (pool.termAt index)).eval (observe (graph Row) depth)) hidden item := by
  rw [lowerValue_observe_exact pool empty join leRow compare]

/-- In particular, input slots preserve every observation of their freely
chosen original parameter; a fresh parameter is not substituted for a tail. -/
theorem lower_input_observe_exact (pool : Pool m) (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (input : Fin m → RegularInferenceModel.Ty Row) (rows : Fin m → Row)
    (index : Fin m) (depth : Nat) :
    (lowerValue pool empty join input rows (pool.input index)).eval (observe (graph Row) depth) =
      (input index).eval (observe (graph Row) depth) := by
  have exactObservation := lowerValue_observe_exact pool empty join leRow compare input rows
    (pool.input index) depth
  simpa only [Pool.input, Pool.termAt_reference, TypeConstraintGraph.evaluate, TyTerm.eval]
    using exactObservation

/-- Constructor equations and all edges in the actual compiler output have
exactly the original meaning after lowering to one finite shared block.
No successful solve, typing premise or original satisfiability is assumed. -/
theorem compile_lower_models_exact (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (compareRefl : ∀ type, compare type type) (problem : ConstraintProblems.Problem m)
    (input : Fin m → RegularInferenceModel.Ty Row) (rows : Fin m → Row) :
    let model := observationModel empty join leRow compare
    let compiled := OpenRecordConstraintGraph.compile problem
    let pool := OpenRecordConstraintGraph.collect problem.types
    (PresenceOpenTailTransport.Models (graph Row) compare empty join
        (State.node ∘ input) rows compiled.graph compiled.constraints (close pool empty join input rows) ∧
      ConstraintProblems.RowHolds model rows compiled.rows) ↔ problem.Holds model input rows := by
  dsimp only
  let pool := OpenRecordConstraintGraph.collect problem.types
  let source := RegularInferenceModel.blockGraph (body pool empty join input rows)
  let inputs : Fin m → Ref pool Row := fun index => .inr (.node (input index))
  let values : Fin pool.size → Ref pool Row := Sum.inl
  let nodes := (OpenRecordConstraintGraph.compile problem).graph
  let edges := (OpenRecordConstraintGraph.compile problem).constraints
  have closure := PresenceOpenTailTransport.models_morphism source (graph Row)
    (RegularInferenceModel.blockRef (body pool empty join input rows))
    (RegularInferenceModel.block_morphism (body pool empty join input rows))
    compare empty join inputs rows nodes edges values
  have evaluation := PresenceOpenTailTransport.models_morphism source (graph Row)
    (evaluationRef pool empty join leRow compare input rows)
    (evaluation_morphism pool empty join leRow compare input rows)
    compare empty join inputs rows nodes edges values
  have transfer := closure.trans evaluation.symm
  have original := PresenceOpenTailTransport.compile_extend_models_exact
    empty join leRow compare compareRefl problem input rows
  exact (and_congr transfer Iff.rfl).trans original

/-- The constructed lower block preserves every subtype comparison at an
original output slot, for any finite comparison relation and any target. -/
theorem lower_input_subtype_exact (pool : Pool m) (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (input : Fin m → RegularInferenceModel.Ty Row) (rows : Fin m → Row)
    (index : Fin m) (target : RegularInferenceModel.Ty Row) :
    PresenceOpenTailTransport.LayerLe (graph Row) compare
        (lowerValue pool empty join input rows (pool.input index)) target ↔
      PresenceOpenTailTransport.LayerLe (graph Row) compare (input index) target := by
  unfold PresenceOpenTailTransport.LayerLe
  apply forall_congr'
  intro depth
  rw [lower_input_observe_exact pool empty join leRow compare]

/-- The lowered graph has exactly the original full target instances.
Input types and rows are still arbitrary independent parameters subject to
the original constraints; this does not claim residual-free solved schemes. -/
theorem compile_lower_instances_exact (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (compareRefl : ∀ type, compare type type) (problem : ConstraintProblems.Problem m)
    (output : Fin m) (target : Comp (observationModel empty join leRow compare)) :
    let model := observationModel empty join leRow compare
    let compiled := OpenRecordConstraintGraph.compile problem
    let pool := OpenRecordConstraintGraph.collect problem.types
    (∃ input : Fin m → RegularInferenceModel.Ty Row, ∃ rows : Fin m → Row,
      (PresenceOpenTailTransport.Models (graph Row) compare empty join
          (State.node ∘ input) rows compiled.graph compiled.constraints (close pool empty join input rows) ∧
        ConstraintProblems.RowHolds model rows compiled.rows) ∧
      Comp.le model (lowerValue pool empty join input rows (pool.input output), rows output) target) ↔
        problem.Instance model output target := by
  dsimp only
  unfold ConstraintProblems.Problem.Instance
  apply exists_congr
  intro input
  apply exists_congr
  intro rows
  apply and_congr (compile_lower_models_exact empty join leRow compare compareRefl problem input rows)
  exact and_congr (lower_input_subtype_exact _ empty join leRow compare input rows output target.1) Iff.rfl

/-- Any independently supplied assignment satisfying the compiler's original
literal constructor equations is recovered at every original slot and depth.
Only constructor realization is needed; subtype constraints need not hold.
This statement does not silently replace literal realization by semantic
equivalence of constructor equations. -/
theorem compile_lower_raw_retraction (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (problem : ConstraintProblems.Problem m) (input : Fin m → RegularInferenceModel.Ty Row)
    (rows : Fin m → Row)
    (value : Fin (OpenRecordConstraintGraph.compile problem).size → RegularInferenceModel.Ty Row)
    (realized : OpenRecordConstraintGraph.Realizes (observationModel empty join leRow compare)
      input rows (OpenRecordConstraintGraph.compile problem).graph value)
    (index : Fin (OpenRecordConstraintGraph.compile problem).size) (depth : Nat) :
    (lowerValue (OpenRecordConstraintGraph.collect problem.types) empty join input rows index).eval
        (observe (graph Row) depth) = (value index).eval (observe (graph Row) depth) := by
  let pool := OpenRecordConstraintGraph.collect problem.types
  have recovered := OpenRecordConstraintGraph.realizes_evaluate pool
    (observationModel empty join leRow compare) input rows value realized
    (pool.termAt index) (pool.at_mem index)
  have recovered' := (congrArg value (Pool.reference_termAt pool index)).symm.trans recovered
  exact (lowerValue_observe_exact pool empty join leRow compare input rows index depth).trans
    (congrArg (fun layer => layer.eval (observe (graph Row) depth)) recovered'.symm)

/-- A record with a genuinely unknown tail keeps the tail's complete first
layer even at observation depth zero. The payload alone is truncated. -/
theorem open_tail_at_zero (pool : Pool m) (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (compare : StructuralBase.Ty Row → StructuralBase.Ty Row → Prop)
    (input : Fin m → RegularInferenceModel.Ty Row) (rows : Fin m → Row)
    (label : Nat) (head : TyTerm (Fin m)) (tail : Fin m)
    (member : .record label head (.var tail) ∈ pool.terms) :
    (lowerValue pool empty join input rows
        (pool.reference (.record label head (.var tail)) member)).eval (observe (graph Row) 0) =
      .record label .bottom ((input tail).eval (observe (graph Row) 0)) := by
  have exactObservation := lowerValue_observe_exact pool empty join leRow compare input rows
    (pool.reference (.record label head (.var tail)) member) 0
  simpa only [Pool.termAt_reference, TypeConstraintGraph.evaluate, TyTerm.eval,
    observationModel, RegularInferenceModel.model, Layer.eval, observe] using exactObservation

end Yulang.PresenceOpenTailLowering
