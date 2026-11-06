import Yulang.RegularValueCoalescing

/-!
# A common inference model containing finite regular blocks

The carrier combines finite outer layers with finite, simultaneously recursive
blocks. A block may refer to previously constructed values. All recursive
references remain guarded by a structural constructor, exactly as in
`RegularValueTypes`; no equation or subtyping law is added here.

The interpretation is the independent finite-observation subtype relation.
Graph embeddings preserve and reflect that relation, so closing a generated
solver graph into a block changes its representation but not its meaning.
-/

namespace Yulang.RegularInferenceModel

open Inference
open RegularValueTypes (Layer)

universe u

/-- Finite syntax for ordinary layers and finite simultaneous recursive blocks.
The external references of a block are already constructed values. -/
inductive State (Row : Type u) where
  | node : Layer Row (State Row) → State Row
  | block (body : List (Layer Row (Nat ⊕ State Row))) (root : Nat) : State Row

abbrev Ty (Row : Type u) := Layer Row (State Row)

/-- Resolve one block's internal references while leaving its parameters fixed. -/
def rawBlockRef {Row : Type u} (body : List (Layer Row (Nat ⊕ State Row))) :
    Nat ⊕ State Row → State Row :=
  Sum.elim (State.block body) id

/-- Unfold one outer layer. This is a finite pattern match, not a recursive
evaluation of the block. -/
def graph (Row : Type u) : RegularValueTypes.Graph Row (State Row)
  | .node type => type
  | .block body root => (body[root]?.getD .bottom).map (rawBlockRef body)

@[simp] theorem graph_node {Row : Type u} (type : Ty Row) :
    graph Row (.node type) = type := rfl

@[simp] theorem graph_block {Row : Type u}
    (body : List (Layer Row (Nat ⊕ State Row))) (root : Nat) :
    graph Row (.block body root) = (body[root]?.getD .bottom).map (rawBlockRef body) := rfl

/-- The stored list uses natural indices because Lean's nested-inductive
parameters cannot depend on a constructor's local block size. -/
def blockBody {Row : Type u} {size : Nat}
    (body : Fin size → Layer Row (Fin size ⊕ State Row)) :
    List (Layer Row (Nat ⊕ State Row)) :=
  List.ofFn fun index => (body index).map (Sum.map Fin.val id)

def closeBlock {Row : Type u} {size : Nat}
    (body : Fin size → Layer Row (Fin size ⊕ State Row)) (root : Fin size) : State Row :=
  .block (blockBody body) root.val

def blockRef {Row : Type u} {size : Nat}
    (body : Fin size → Layer Row (Fin size ⊕ State Row)) :
    Fin size ⊕ State Row → State Row :=
  Sum.elim (closeBlock body) id

@[simp] theorem graph_closeBlock {Row : Type u} {size : Nat}
    (body : Fin size → Layer Row (Fin size ⊕ State Row)) (root : Fin size) :
    graph Row (closeBlock body root) = (body root).map (blockRef body) := by
  simp only [closeBlock, graph, blockBody, List.getElem?_ofFn, root.isLt, ↓reduceDIte,
    Option.getD_some, Layer.map_comp]
  congr 1
  funext state
  cases state <;> rfl

/-- All inference constructors are closed in this one carrier. -/
def model (Row : Type u) (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) : Inference.Model where
  Ty := Ty Row
  Row := Row
  base := .base
  bottom := .bottom
  top := .top
  union := .union
  inter := .inter
  pair := fun left right => .pair (.node left) (.node right)
  emptyRecord := .emptyRecord
  record := fun label value rest => .record label (.node value) rest
  variant := fun label value => .variant label (.node value)
  arrow := fun input inputRow output outputRow =>
    .arrow (.node input) inputRow (.node output) outputRow
  empty := empty
  join := join
  subTy := RegularValueTypes.Subtype (graph Row) leRow
  subRow := leRow

variable {Row : Type u} {size : Nat}

/-- An open finite block and its existing external graph, before closing it. -/
def blockGraph (body : Fin size → Layer Row (Fin size ⊕ State Row)) :
    RegularValueTypes.Graph Row (Fin size ⊕ State Row)
  | .inl index => body index
  | .inr state => (graph Row state).map Sum.inr

theorem block_morphism (body : Fin size → Layer Row (Fin size ⊕ State Row))
    (state : Fin size ⊕ State Row) :
    (blockGraph body state).map (blockRef body) = graph Row (blockRef body state) := by
  cases state with
  | inl index => exact (graph_closeBlock body index).symm
  | inr state =>
      simp only [blockGraph, Layer.map_comp]
      change (graph Row state).map id = graph Row state
      exact Layer.map_id _

theorem block_observe (body : Fin size → Layer Row (Fin size ⊕ State Row))
    (depth : Nat) (state : Fin size ⊕ State Row) :
    RegularValueTypes.observe (graph Row) depth (blockRef body state) =
      RegularValueTypes.observe (blockGraph body) depth state :=
  RegularValueTypes.observe_morphism (graph Row) (blockRef body) (block_morphism body) depth state

/-- Closing a finite block preserves and reflects every comparison of layers,
including comparisons against externally supplied values. -/
theorem block_subtype (body : Fin size → Layer Row (Fin size ⊕ State Row))
    (leRow : Row → Row → Prop) (left right : Layer Row (Fin size ⊕ State Row)) :
    RegularValueTypes.Subtype (graph Row) leRow
        (left.map (blockRef body)) (right.map (blockRef body)) ↔
      RegularValueTypes.Subtype (blockGraph body) leRow left right :=
  RegularValueTypes.subtype_morphism (graph Row) (blockRef body) (block_morphism body) left right

theorem block_nodeSubtype (body : Fin size → Layer Row (Fin size ⊕ State Row))
    (leRow : Row → Row → Prop) (left right : Fin size ⊕ State Row) :
    RegularValueTypes.NodeSubtype (graph Row) leRow (blockRef body left) (blockRef body right) ↔
      RegularValueTypes.NodeSubtype (blockGraph body) leRow left right := by
  unfold RegularValueTypes.NodeSubtype
  rw [← block_morphism body left, ← block_morphism body right]
  exact block_subtype body leRow _ _

/-- Every standalone finite regular graph embeds in the common carrier. -/
def finiteRef (source : RegularValueTypes.FiniteGraph Row size) : Fin size → State Row :=
  closeBlock (fun index => (source index).map Sum.inl)

theorem finite_morphism (source : RegularValueTypes.FiniteGraph Row size) (index : Fin size) :
    (source index).map (finiteRef source) = graph Row (finiteRef source index) := by
  rw [finiteRef, graph_closeBlock, Layer.map_comp]
  rfl

theorem finite_subtype (source : RegularValueTypes.FiniteGraph Row size)
    (leRow : Row → Row → Prop) (left right : Layer Row (Fin size)) :
    RegularValueTypes.Subtype (graph Row) leRow
        (left.map (finiteRef source)) (right.map (finiteRef source)) ↔
      RegularValueTypes.Subtype source leRow left right :=
  RegularValueTypes.subtype_morphism (graph Row) (finiteRef source) (finite_morphism source) left right

theorem finite_nodeSubtype (source : RegularValueTypes.FiniteGraph Row size)
    (leRow : Row → Row → Prop) (left right : Fin size) :
    RegularValueTypes.NodeSubtype (graph Row) leRow (finiteRef source left) (finiteRef source right) ↔
      RegularValueTypes.NodeSubtype source leRow left right := by
  unfold RegularValueTypes.NodeSubtype
  rw [← finite_morphism source left, ← finite_morphism source right]
  exact finite_subtype source leRow _ _

abbrev Subtype (leRow : Row → Row → Prop) := RegularValueTypes.Subtype (graph Row) leRow

def Equivalent (leRow : Row → Row → Prop) (left right : Ty Row) : Prop :=
  Subtype leRow left right ∧ Subtype leRow right left

theorem subtype_refl (leRow : Row → Row → Prop) (type : Ty Row) : Subtype leRow type type :=
  RegularValueTypes.subtype_refl type

theorem subtype_trans {leRow : Row → Row → Prop} {left middle right : Ty Row}
    (first : Subtype leRow left middle) (last : Subtype leRow middle right) :
    Subtype leRow left right := RegularValueTypes.subtype_trans first last

theorem equivalent_refl (leRow : Row → Row → Prop) (type : Ty Row) : Equivalent leRow type type :=
  ⟨subtype_refl leRow type, subtype_refl leRow type⟩

theorem equivalent_symm {leRow : Row → Row → Prop} {left right : Ty Row}
    (same : Equivalent leRow left right) : Equivalent leRow right left := ⟨same.2, same.1⟩

theorem equivalent_trans {leRow : Row → Row → Prop} {left middle right : Ty Row}
    (first : Equivalent leRow left middle) (last : Equivalent leRow middle right) :
    Equivalent leRow left right :=
  ⟨subtype_trans first.1 last.1, subtype_trans last.2 first.2⟩

@[simp] theorem quote_subtype (leRow : Row → Row → Prop) (left right : Ty Row) :
    RegularValueTypes.NodeSubtype (graph Row) leRow (.node left) (.node right) ↔
      Subtype leRow left right := Iff.rfl

theorem quote_observe_subtype {leRow : Row → Row → Prop} {left right : Ty Row}
    (below : Subtype leRow left right) (depth : Nat) :
    StructuralBase.Subtype leRow
      (RegularValueTypes.observe (graph Row) depth (.node left))
      (RegularValueTypes.observe (graph Row) depth (.node right)) :=
  RegularNestedModels.observe_subtype (graph Row) leRow
    (show RegularValueTypes.NodeSubtype (graph Row) leRow (.node left) (.node right) from below) depth

theorem union_is_join (leRow : Row → Row → Prop) (left right target : Ty Row) :
    Subtype leRow (.union left right) target ↔
      Subtype leRow left target ∧ Subtype leRow right target := by
  constructor
  · intro below
    exact ⟨fun depth => (StructuralBase.union_is_join _ _ _).mp (below depth) |>.1,
      fun depth => (StructuralBase.union_is_join _ _ _).mp (below depth) |>.2⟩
  · rintro ⟨first, last⟩ depth
    exact .unionElim (first depth) (last depth)

theorem inter_is_meet (leRow : Row → Row → Prop) (left right source : Ty Row) :
    Subtype leRow source (.inter left right) ↔
      Subtype leRow source left ∧ Subtype leRow source right := by
  constructor
  · intro below
    exact ⟨fun depth => (StructuralBase.inter_is_meet _ _ _).mp (below depth) |>.1,
      fun depth => (StructuralBase.inter_is_meet _ _ _).mp (below depth) |>.2⟩
  · rintro ⟨first, last⟩ depth
    exact .interIntro (first depth) (last depth)

theorem bottom_subtype (leRow : Row → Row → Prop) (type : Ty Row) : Subtype leRow .bottom type :=
  fun _ => .bottom _

theorem subtype_top (leRow : Row → Row → Prop) (type : Ty Row) : Subtype leRow type .top :=
  fun _ => .top _

theorem pair_subtype {leRow : Row → Row → Prop} {left left' right right' : Ty Row}
    (first : Subtype leRow left left') (last : Subtype leRow right right') :
    Subtype leRow (.pair (.node left) (.node right)) (.pair (.node left') (.node right')) := by
  intro depth
  exact .pair (quote_observe_subtype first depth) (quote_observe_subtype last depth)

theorem variant_subtype {leRow : Row → Row → Prop} (label : Nat) {left right : Ty Row}
    (below : Subtype leRow left right) :
    Subtype leRow (.variant label (.node left)) (.variant label (.node right)) := by
  intro depth
  exact .variant (quote_observe_subtype below depth)

theorem arrow_subtype {leRow : Row → Row → Prop} {input input' output output' : Ty Row}
    {inputRow inputRow' outputRow outputRow' : Row}
    (before : Subtype leRow input' input) (beforeRow : leRow inputRow' inputRow)
    (after : Subtype leRow output output') (afterRow : leRow outputRow outputRow') :
    Subtype leRow (.arrow (.node input) inputRow (.node output) outputRow)
      (.arrow (.node input') inputRow' (.node output') outputRow') := by
  intro depth
  exact .arrow (quote_observe_subtype before depth) beforeRow
    (quote_observe_subtype after depth) afterRow

/-! ## Constructor meanings and semantic graph realizers -/

variable {n : Nat}

/-- Interpret a rigid solver constructor using arbitrary values of the common
carrier. Variable nodes have the same unused bottom sentinel as `rigidLayer`. -/
def rigidMeaning (value : Fin n → Ty Row) (node : NestedValueSolver.Node n Row) : Ty Row :=
  (RigidValueLayers.rigidLayer node).map (fun index => State.node (value index))

/-- A fixed record spine; duplicate labels retain their first-field-wins
meaning. Only values actually present in this finite spine are relevant. -/
def recordMeaning (value : Fin n → Ty Row) (fields : List (Nat × Fin n)) : Ty Row :=
  (RigidValueLayers.recordLayer fields).map (fun index => State.node (value index))

@[simp] theorem recordMeaning_nil (value : Fin n → Ty Row) : recordMeaning value [] = .emptyRecord := rfl

@[simp] theorem recordMeaning_cons (value : Fin n → Ty Row) (label : Nat) (field : Fin n)
    (rest : List (Nat × Fin n)) :
    recordMeaning value ((label, field) :: rest) =
      .record label (.node (value field)) (recordMeaning value rest) := rfl

theorem recordMeaning_mono (leRow : Row → Row → Prop) (fields : List (Nat × Fin n))
    (left right : Fin n → Ty Row)
    (below : ∀ field ∈ fields, Subtype leRow (left field.2) (right field.2)) :
    Subtype leRow (recordMeaning left fields) (recordMeaning right fields) := by
  intro depth
  simp only [RegularValueTypes.At, recordMeaning, Layer.eval_map, RigidValueLayers.recordLayer_eval]
  apply RigidValueLayers.record_subtype leRow _ _ fields fields
  · intro label expected found
    exact ⟨expected, found⟩
  · intro label actual expected actualFound expectedFound
    have same : actual = expected := Option.some.inj (actualFound.symm.trans expectedFound)
    subst expected
    exact quote_observe_subtype (below (label, actual) (RigidValueLayers.lookupField_mem actualFound)) depth

theorem recordMeaning_equivalent (leRow : Row → Row → Prop) (fields : List (Nat × Fin n))
    (left right : Fin n → Ty Row)
    (same : ∀ field ∈ fields, Equivalent leRow (left field.2) (right field.2)) :
    Equivalent leRow (recordMeaning left fields) (recordMeaning right fields) :=
  ⟨recordMeaning_mono leRow fields left right (fun field member => (same field member).1),
    recordMeaning_mono leRow fields right left (fun field member => (same field member).2)⟩

theorem pair_equivalent {leRow : Row → Row → Prop} {left left' right right' : Ty Row}
    (first : Equivalent leRow left left') (last : Equivalent leRow right right') :
    Equivalent leRow (.pair (.node left) (.node right)) (.pair (.node left') (.node right')) :=
  ⟨pair_subtype first.1 last.1, pair_subtype first.2 last.2⟩

theorem variant_equivalent {leRow : Row → Row → Prop} (label : Nat) {left right : Ty Row}
    (same : Equivalent leRow left right) :
    Equivalent leRow (.variant label (.node left)) (.variant label (.node right)) :=
  ⟨variant_subtype label same.1, variant_subtype label same.2⟩

theorem arrow_equivalent {leRow : Row → Row → Prop} (rowRefl : ∀ row, leRow row row)
    {input input' output output' : Ty Row} (inputRow outputRow : Row)
    (before : Equivalent leRow input input') (after : Equivalent leRow output output') :
    Equivalent leRow (.arrow (.node input) inputRow (.node output) outputRow)
      (.arrow (.node input') inputRow (.node output') outputRow) :=
  ⟨arrow_subtype before.2 (rowRefl _) after.1 (rowRefl _),
    arrow_subtype before.1 (rowRefl _) after.2 (rowRefl _)⟩

/-- Recursive realization uses the already defined semantic equivalence;
finite syntax equality is stronger and is not silently assumed. -/
def SemanticRealizes (source : NestedValueSolver.Graph n Row) (leRow : Row → Row → Prop)
    (value : Fin n → Ty Row) : Prop :=
  ∀ index, source index ≠ .var → Equivalent leRow (value index) (rigidMeaning value (source index))

def SemanticModels (source : NestedValueSolver.Graph n Row)
    (constraints : List (NestedValueSolver.Edge n)) (leRow : Row → Row → Prop)
    (value : Fin n → Ty Row) : Prop :=
  SemanticRealizes source leRow value ∧
    ∀ edge ∈ constraints, Subtype leRow (value edge.1) (value edge.2)

theorem semanticRealizes_of_eq (source : NestedValueSolver.Graph n Row) (leRow : Row → Row → Prop)
    (value : Fin n → Ty Row)
    (realized : ∀ index, source index ≠ .var → value index = rigidMeaning value (source index)) :
    SemanticRealizes source leRow value := by
  intro index rigid
  rw [realized index rigid]
  exact equivalent_refl leRow _

theorem semanticModels_iff (source : NestedValueSolver.Graph n Row)
    (constraints : List (NestedValueSolver.Edge n)) (leRow : Row → Row → Prop)
    (value : Fin n → Ty Row) :
    SemanticModels source constraints leRow value ↔
      RegularNestedModels.Models leRow source constraints (graph Row)
        (fun index => State.node (value index)) := Iff.rfl

theorem rigidMeaning_equivalent (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (left right : Fin n → Ty Row) (same : ∀ index, Equivalent leRow (left index) (right index))
    (node : NestedValueSolver.Node n Row) :
    Equivalent leRow (rigidMeaning left node) (rigidMeaning right node) :=
  RegularNestedModels.rigidLayer_map_equivalent (graph Row) leRow rowRefl
    (fun index => State.node (left index)) (fun index => State.node (right index)) same node

theorem semanticModels_equivalent (leRow : Row → Row → Prop) (rowRefl : ∀ row, leRow row row)
    (source : NestedValueSolver.Graph n Row) (constraints : List (NestedValueSolver.Edge n))
    (left right : Fin n → Ty Row) (realized : SemanticModels source constraints leRow left)
    (same : ∀ index, Equivalent leRow (left index) (right index)) :
    SemanticModels source constraints leRow right := by
  apply (semanticModels_iff source constraints leRow right).mpr
  exact RegularNestedModels.models_equivalent leRow rowRefl source constraints (graph Row)
    (fun index => State.node (left index)) (fun index => State.node (right index))
    ((semanticModels_iff source constraints leRow left).mp realized) same

/-- An exact graph morphism preserves and reflects semantic realization as
well as all constraints. No injectivity or finiteness assumption is needed. -/
theorem models_embedding {SourceState : Type v}
    (sourceGraph : RegularValueTypes.Graph Row SourceState) (rename : SourceState → State Row)
    (commutes : ∀ state, (sourceGraph state).map rename = graph Row (rename state))
    (source : NestedValueSolver.Graph n Row) (constraints : List (NestedValueSolver.Edge n))
    (leRow : Row → Row → Prop) (value : Fin n → SourceState) :
    RegularNestedModels.Models leRow source constraints sourceGraph value ↔
      RegularNestedModels.Models leRow source constraints (graph Row) (fun index => rename (value index)) := by
  have transfer (left right : Layer Row SourceState) :=
    RegularValueTypes.subtype_morphism (graph Row) rename commutes left right (leRow := leRow)
  have rigidTransfer (index : Fin n) :
      (RegularValueTypes.Subtype (graph Row) leRow (graph Row (rename (value index)))
          ((RigidValueLayers.rigidLayer (source index)).map (fun child => rename (value child))) ↔
        RegularValueTypes.Subtype sourceGraph leRow (sourceGraph (value index))
          ((RigidValueLayers.rigidLayer (source index)).map value)) ∧
      (RegularValueTypes.Subtype (graph Row) leRow
          ((RigidValueLayers.rigidLayer (source index)).map (fun child => rename (value child)))
          (graph Row (rename (value index))) ↔
        RegularValueTypes.Subtype sourceGraph leRow
          ((RigidValueLayers.rigidLayer (source index)).map value) (sourceGraph (value index))) := by
    constructor
    · simpa only [commutes, Layer.map_comp] using
        transfer (sourceGraph (value index)) ((RigidValueLayers.rigidLayer (source index)).map value)
    · simpa only [commutes, Layer.map_comp] using
        transfer ((RigidValueLayers.rigidLayer (source index)).map value) (sourceGraph (value index))
  have edgeTransfer (edge : NestedValueSolver.Edge n) :
      RegularValueTypes.NodeSubtype (graph Row) leRow (rename (value edge.1)) (rename (value edge.2)) ↔
        RegularValueTypes.NodeSubtype sourceGraph leRow (value edge.1) (value edge.2) := by
    simpa only [commutes, RegularValueTypes.NodeSubtype] using
      transfer (sourceGraph (value edge.1)) (sourceGraph (value edge.2))
  constructor
  · rintro ⟨realizes, satisfies⟩
    refine ⟨?_, ?_⟩
    · intro index rigid
      exact ⟨(rigidTransfer index).1.mpr (realizes index rigid).1,
        (rigidTransfer index).2.mpr (realizes index rigid).2⟩
    · intro edge member
      exact (edgeTransfer edge).mpr (satisfies edge member)
  · rintro ⟨realizes, satisfies⟩
    refine ⟨?_, ?_⟩
    · intro index rigid
      exact ⟨(rigidTransfer index).1.mp (realizes index rigid).1,
        (rigidTransfer index).2.mp (realizes index rigid).2⟩
    · intro edge member
      exact (edgeTransfer edge).mp (satisfies edge member)

/-! ## Closing the actual solver result in the common inference carrier -/

def solutionBody (source : NestedValueSolver.Graph n Row) (cache : List (NestedValueSolver.Edge n))
    (parameter : Fin n → Ty Row) : Fin n → Layer Row (Fin n ⊕ State Row) :=
  fun index => RegularValueCoalescing.coalesceGraph source cache (graph Row) parameter (.inl index)

def solutionRef (source : NestedValueSolver.Graph n Row) (cache : List (NestedValueSolver.Edge n))
    (parameter : Fin n → Ty Row) : Fin n ⊕ State Row → State Row :=
  blockRef (solutionBody source cache parameter)

def solution (source : NestedValueSolver.Graph n Row) (cache : List (NestedValueSolver.Edge n))
    (parameter : Fin n → Ty Row) (index : Fin n) : Ty Row :=
  graph Row (solutionRef source cache parameter (.inl index))

theorem solution_blockGraph (source : NestedValueSolver.Graph n Row)
    (cache : List (NestedValueSolver.Edge n)) (parameter : Fin n → Ty Row) :
    blockGraph (solutionBody source cache parameter) =
      RegularValueCoalescing.coalesceGraph source cache (graph Row) parameter := by
  funext state
  cases state <;> rfl

theorem solution_morphism (source : NestedValueSolver.Graph n Row)
    (cache : List (NestedValueSolver.Edge n)) (parameter : Fin n → Ty Row)
    (state : Fin n ⊕ State Row) :
    (RegularValueCoalescing.coalesceGraph source cache (graph Row) parameter state).map
        (solutionRef source cache parameter) = graph Row (solutionRef source cache parameter state) := by
  rw [← solution_blockGraph source cache parameter]
  exact block_morphism (solutionBody source cache parameter) state

theorem solution_nodeSubtype (source : NestedValueSolver.Graph n Row)
    (cache : List (NestedValueSolver.Edge n)) (parameter : Fin n → Ty Row)
    (leRow : Row → Row → Prop) (left right : Fin n ⊕ State Row) :
    RegularValueTypes.NodeSubtype (graph Row) leRow
        (solutionRef source cache parameter left) (solutionRef source cache parameter right) ↔
      RegularValueTypes.NodeSubtype
        (RegularValueCoalescing.coalesceGraph source cache (graph Row) parameter) leRow left right := by
  rw [← solution_blockGraph source cache parameter]
  exact block_nodeSubtype (solutionBody source cache parameter) leRow left right

theorem solve_solution_model (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowSound : ∀ left right, rowCheck left right = true → leRow left right)
    (source : NestedValueSolver.Graph n Row) (constraints cache : List (NestedValueSolver.Edge n))
    (solved : NestedValueSolver.solve rowCheck source constraints = some cache)
    (parameter : Fin n → Ty Row) :
    RegularNestedModels.Models leRow source constraints (graph Row)
      (fun index => solutionRef source cache parameter (.inl index)) := by
  apply (models_embedding _ (solutionRef source cache parameter) (solution_morphism source cache parameter)
    source constraints leRow Sum.inl).mp
  exact RegularValueCoalescing.solve_instantiates_model rowCheck leRow rowSound
    source constraints cache solved (graph Row) parameter

theorem solve_solution (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowSound : ∀ left right, rowCheck left right = true → leRow left right)
    (source : NestedValueSolver.Graph n Row) (constraints cache : List (NestedValueSolver.Edge n))
    (solved : NestedValueSolver.solve rowCheck source constraints = some cache)
    (parameter : Fin n → Ty Row) :
    SemanticModels source constraints leRow (solution source cache parameter) := by
  apply (semanticModels_iff source constraints leRow _).mpr
  apply RegularNestedModels.models_equivalent leRow rowRefl source constraints (graph Row)
    (fun index => solutionRef source cache parameter (.inl index))
    (fun index => State.node (solution source cache parameter index))
    (solve_solution_model rowCheck leRow rowSound source constraints cache solved parameter)
  intro index
  exact equivalent_refl leRow _

/-- Every solution in the one inference carrier is represented by a free
parameter instance, and every such instance is a solution. The parameters
carry no residual bound condition. -/
theorem solve_models_exact (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (source : NestedValueSolver.Graph n Row) (constraints cache : List (NestedValueSolver.Edge n))
    (solved : NestedValueSolver.solve rowCheck source constraints = some cache)
    (value : Fin n → Ty Row) :
    SemanticModels source constraints leRow value ↔
      ∃ parameter : Fin n → Ty Row,
        ∀ index, Equivalent leRow (solution source cache parameter index) (value index) := by
  rw [semanticModels_iff]
  rw [RegularValueCoalescing.solve_models_exact rowCheck leRow rowRefl rowTrans rowExact
    source constraints cache solved (graph Row) (fun index => State.node (value index))]
  constructor
  · rintro ⟨parameter, equivalent⟩
    refine ⟨parameter, fun index => ?_⟩
    exact ⟨(solution_nodeSubtype source cache parameter leRow (.inl index)
        (.inr (.node (value index)))).mpr (equivalent index).1,
      (solution_nodeSubtype source cache parameter leRow (.inr (.node (value index)))
        (.inl index)).mpr (equivalent index).2⟩
  · rintro ⟨parameter, equivalent⟩
    refine ⟨parameter, fun index => ?_⟩
    exact ⟨(solution_nodeSubtype source cache parameter leRow (.inl index)
        (.inr (.node (value index)))).mp (equivalent index).1,
      (solution_nodeSubtype source cache parameter leRow (.inr (.node (value index)))
        (.inl index)).mp (equivalent index).2⟩

/-- Failure is exactly the absence of solutions in this fixed inference
carrier, not merely in a separately chosen graph representation. -/
theorem solve_none_iff (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (source : NestedValueSolver.Graph n Row) (constraints : List (NestedValueSolver.Edge n)) :
    NestedValueSolver.solve rowCheck source constraints = none ↔
      ¬ ∃ value : Fin n → Ty Row, SemanticModels source constraints leRow value := by
  constructor
  · rintro rejected ⟨value, realized⟩
    exact RegularNestedModels.solve_rejects_model rowCheck leRow rowRefl rowTrans rowExact
      source constraints rejected (graph Row) (fun index => State.node (value index))
      ((semanticModels_iff source constraints leRow value).mp realized)
  · intro impossible
    cases solved : NestedValueSolver.solve rowCheck source constraints with
    | none => rfl
    | some cache =>
        exact False.elim (impossible ⟨solution source cache (fun _ => .bottom),
          solve_solution rowCheck leRow rowRefl (fun left right => (rowExact left right).mp)
            source constraints cache solved (fun _ => .bottom)⟩)

/-- An original constrained output inside the common inference model. -/
def ConstrainedInstance (source : NestedValueSolver.Graph n Row)
    (constraints : List (NestedValueSolver.Edge n)) (root : Fin n)
    (leRow : Row → Row → Prop) (target : Ty Row) : Prop :=
  ∃ value : Fin n → Ty Row,
    SemanticModels source constraints leRow value ∧ Subtype leRow (value root) target

/-- A free instance of the executable solver's finite regular block. -/
def SchemeInstance (source : NestedValueSolver.Graph n Row)
    (cache : List (NestedValueSolver.Edge n)) (root : Fin n)
    (leRow : Row → Row → Prop) (target : Ty Row) : Prop :=
  ∃ parameter : Fin n → Ty Row, Subtype leRow (solution source cache parameter root) target

/-- Full output-instance equality in a single `Inference.Model`. Both sides
quantify over the same carrier and use the same independent subtype relation. -/
theorem solve_instances_exact (rowCheck : Row → Row → Bool) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c : Row}, leRow a b → leRow b c → leRow a c)
    (rowExact : ∀ left right, rowCheck left right = true ↔ leRow left right)
    (source : NestedValueSolver.Graph n Row) (constraints cache : List (NestedValueSolver.Edge n))
    (solved : NestedValueSolver.solve rowCheck source constraints = some cache)
    (root : Fin n) (target : Ty Row) :
    ConstrainedInstance source constraints root leRow target ↔
      SchemeInstance source cache root leRow target := by
  constructor
  · rintro ⟨value, realized, below⟩
    obtain ⟨parameter, equivalent⟩ :=
      (solve_models_exact rowCheck leRow rowRefl rowTrans rowExact source constraints cache solved value).mp realized
    exact ⟨parameter, subtype_trans (equivalent root).1 below⟩
  · rintro ⟨parameter, below⟩
    exact ⟨solution source cache parameter,
      solve_solution rowCheck leRow rowRefl (fun left right => (rowExact left right).mp)
        source constraints cache solved parameter, below⟩

end Yulang.RegularInferenceModel
