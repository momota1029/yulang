import Yulang.CommonPresenceConstraintGraph

/-!
# Finite constructor nodes for optional payload bounds

The extension is computed from an original constructor graph and a finite
list of `(label, payload)` queries. A missing payload means `top`; a present
payload is an original shared node ID. The original node numbers and every
row ID are retained. Three constant nodes and two nodes per query are added:
`top`, width, exact empty, required fields, and their unions with exact empty.

Both the graph and its index maps are independent of row and value assignments.
The canonical extension of values is a direct constructor interpretation.
Arbitrary extended realizers restrict to original realizers, and the values
at the new nodes are demand equivalent to that interpretation. Cycles and
negative guarded references in the original graph are not restricted.

This is exactness of a finite graph extension. It does not assert worklist
closure, termination of repeated inspection, or a family of unconstrained
solutions to the original inference problem.
-/

namespace Yulang.CommonOptionalGraphExtension

open Common (Ty Row)
open CommonRowTailInference (Body)

variable {slots larger labels rowSlots : Nat}

abbrev Graph (slots labels rowSlots : Nat) :=
  Fin slots → Body slots labels rowSlots

/-- Original shared node IDs are the only nonconstant payload parameters. -/
abbrev Query (slots : Nat) := Nat × Option (Fin slots)

/-- Constructor equations, interpreted independently of any solver. -/
def Realizes (graph : Graph slots labels rowSlots) (rows : Fin rowSlots → Row)
    (values : Fin slots → Ty) : Prop :=
  ∀ index, Common.Equivalent ((graph index).eval rows values) (values index)

/-- Rename both same-depth and guarded references; row syntax is unchanged. -/
def renameBody (rename : Fin slots → Fin larger) :
    Body slots labels rowSlots → Body larger labels rowSlots
  | .atom type => .atom type
  | .layer layer => .layer (layer.map rename)
  | .ref index => .ref (rename index)
  | .union first last => .union (renameBody rename first) (renameBody rename last)
  | .inter first last => .inter (renameBody rename first) (renameBody rename last)
  | .mask hidden source => .mask hidden (renameBody rename source)
  | .record label payload tail => .record label payload (renameBody rename tail)
  | .recordDefault label source fallback =>
      .recordDefault label (renameBody rename source) fallback
  | .recordRef label payload tail => .recordRef label (rename payload) (renameBody rename tail)
  | .recordDefaultRef label source fallback =>
      .recordDefaultRef label (renameBody rename source) (rename fallback)

theorem layerAtRows_map (rows : Fin rowSlots → Row) (rename : Fin slots → Fin larger)
    (layer : CommonSyntax.Layer (Inference.RowTerm (Fin rowSlots)) (Fin slots)) :
    CommonRowTailInference.layerAtRows rows (layer.map rename) =
      (CommonRowTailInference.layerAtRows rows layer).map rename := by
  induction layer <;> simp_all [CommonRowTailInference.layerAtRows, CommonSyntax.Layer.map]

/-- Renaming changes references only, at every observation depth. -/
theorem renameBody_eval (rename : Fin slots → Fin larger)
    (body : Body slots labels rowSlots) (rows : Fin rowSlots → Row)
    (values : Fin larger → Ty) :
    (renameBody rename body).eval rows values = body.eval rows (values ∘ rename) := by
  induction body <;>
    simp_all [renameBody, Body.eval, layerAtRows_map,
      CommonPresenceTailLayers.quoteLayer_map, Function.comp_def]

/-- The four contiguous blocks are original, constants, required, optional. -/
def size (queries : List (Query slots)) : Nat :=
  slots + (3 + (queries.length + queries.length))

theorem size_exact (queries : List (Query slots)) :
    size queries = slots + 3 + 2 * queries.length := by
  simp only [size]
  omega

def originalIndex (queries : List (Query slots)) (index : Fin slots) : Fin (size queries) :=
  index.castAdd (3 + (queries.length + queries.length))

def constantIndex (queries : List (Query slots)) (index : Fin 3) : Fin (size queries) :=
  (index.castAdd (queries.length + queries.length)).natAdd slots

def topIndex (queries : List (Query slots)) : Fin (size queries) := constantIndex queries 0
def widthIndex (queries : List (Query slots)) : Fin (size queries) := constantIndex queries 1
def exactIndex (queries : List (Query slots)) : Fin (size queries) := constantIndex queries 2

def requiredIndex (queries : List (Query slots))
    (index : Fin queries.length) : Fin (size queries) :=
  ((index.castAdd queries.length).natAdd 3).natAdd slots

def optionalIndex (queries : List (Query slots))
    (index : Fin queries.length) : Fin (size queries) :=
  ((index.natAdd queries.length).natAdd 3).natAdd slots

@[simp] theorem originalIndex_val (queries : List (Query slots)) (index : Fin slots) :
    (originalIndex queries index).val = index.val := rfl

theorem originalIndex_injective (queries : List (Query slots)) :
    Function.Injective (originalIndex queries) := by
  intro first last same
  exact Fin.ext (congrArg (fun index : Fin (size queries) => index.val) same)

@[simp] theorem requiredIndex_val (queries : List (Query slots)) (index : Fin queries.length) :
    (requiredIndex queries index).val = slots + 3 + index.val := by
  simp [requiredIndex, Nat.add_assoc]

@[simp] theorem optionalIndex_val (queries : List (Query slots)) (index : Fin queries.length) :
    (optionalIndex queries index).val = slots + 3 + queries.length + index.val := by
  simp [optionalIndex, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def payloadIndex (queries : List (Query slots)) (query : Query slots) : Fin (size queries) :=
  match query.2 with
  | none => topIndex queries
  | some index => originalIndex queries index

def constantBody (index : Fin 3) : Body slots labels rowSlots :=
  if index = 0 then .layer .top
  else if index = 1 then .layer .emptyRecord
  else .layer .exactEmpty

def constantValue (index : Fin 3) : Ty :=
  if index = 0 then .top
  else if index = 1 then Common.emptyRecord
  else Common.exactEmpty

@[simp] theorem constantBody_eval (index : Fin 3) (rows : Fin rowSlots → Row)
    (values : Fin slots → Ty) :
    (constantBody (labels := labels) index).eval rows values = constantValue index := by
  unfold constantBody constantValue
  split
  · rfl
  · split <;> rfl

/-- No model, solution, fuel, row assignment, or value assignment is consulted. -/
def extendGraph (queries : List (Query slots)) (graph : Graph slots labels rowSlots) :
    Graph (size queries) labels rowSlots :=
  Fin.addCases
    (fun index => renameBody (originalIndex queries) (graph index))
    (Fin.addCases constantBody
      (Fin.addCases
        (fun index => .recordRef (queries.get index).1
          (payloadIndex queries (queries.get index)) (.ref (widthIndex queries)))
        (fun index => .union (.ref (exactIndex queries)) (.ref (requiredIndex queries index)))))

def payloadValue (values : Fin slots → Ty) (query : Query slots) : Ty :=
  match query.2 with
  | none => .top
  | some index => values index

def requiredValue (values : Fin slots → Ty) (query : Query slots) : Ty :=
  Common.required query.1 (payloadValue values query)

def optionalValue (values : Fin slots → Ty) (query : Query slots) : Ty :=
  .union Common.exactEmpty (requiredValue values query)

/-- Direct independent constructor interpretation of the additional nodes. -/
def extendValues (queries : List (Query slots)) (values : Fin slots → Ty) :
    Fin (size queries) → Ty :=
  Fin.addCases values
    (Fin.addCases constantValue
      (Fin.addCases
        (fun index => requiredValue values (queries.get index))
        (fun index => optionalValue values (queries.get index))))

def restrictValues (queries : List (Query slots)) (values : Fin (size queries) → Ty) :
    Fin slots → Ty := values ∘ originalIndex queries

@[simp] theorem extendGraph_original (queries : List (Query slots))
    (graph : Graph slots labels rowSlots) (index : Fin slots) :
    extendGraph queries graph (originalIndex queries index) =
      renameBody (originalIndex queries) (graph index) := by
  simp [extendGraph, originalIndex]

@[simp] theorem extendGraph_constant (queries : List (Query slots))
    (graph : Graph slots labels rowSlots) (index : Fin 3) :
    extendGraph queries graph (constantIndex queries index) = constantBody index := by
  simp [extendGraph, constantIndex]

@[simp] theorem extendGraph_required (queries : List (Query slots))
    (graph : Graph slots labels rowSlots) (index : Fin queries.length) :
    extendGraph queries graph (requiredIndex queries index) =
      .recordRef (queries.get index).1 (payloadIndex queries (queries.get index))
        (.ref (widthIndex queries)) := by
  simp only [extendGraph, requiredIndex, Fin.addCases_right, Fin.addCases_left]

@[simp] theorem extendGraph_optional (queries : List (Query slots))
    (graph : Graph slots labels rowSlots) (index : Fin queries.length) :
    extendGraph queries graph (optionalIndex queries index) =
      .union (.ref (exactIndex queries)) (.ref (requiredIndex queries index)) := by
  simp only [extendGraph, optionalIndex, Fin.addCases_right]

@[simp] theorem extendValues_original (queries : List (Query slots))
    (values : Fin slots → Ty) (index : Fin slots) :
    extendValues queries values (originalIndex queries index) = values index := by
  simp [extendValues, originalIndex]

@[simp] theorem extendValues_constant (queries : List (Query slots))
    (values : Fin slots → Ty) (index : Fin 3) :
    extendValues queries values (constantIndex queries index) = constantValue index := by
  simp [extendValues, constantIndex]

@[simp] theorem extendValues_required (queries : List (Query slots))
    (values : Fin slots → Ty) (index : Fin queries.length) :
    extendValues queries values (requiredIndex queries index) =
      requiredValue values (queries.get index) := by
  simp only [extendValues, requiredIndex, Fin.addCases_right, Fin.addCases_left]

@[simp] theorem extendValues_optional (queries : List (Query slots))
    (values : Fin slots → Ty) (index : Fin queries.length) :
    extendValues queries values (optionalIndex queries index) =
      optionalValue values (queries.get index) := by
  simp only [extendValues, optionalIndex, Fin.addCases_right]

@[simp] theorem extendValues_payload (queries : List (Query slots))
    (values : Fin slots → Ty) (query : Query slots) :
    extendValues queries values (payloadIndex queries query) = payloadValue values query := by
  cases query with
  | mk label payload =>
    cases payload <;>
      simp [payloadIndex, payloadValue, topIndex, constantValue]

@[simp] theorem restrict_extend (queries : List (Query slots)) (values : Fin slots → Ty) :
    restrictValues queries (extendValues queries values) = values := by
  funext index
  exact extendValues_original queries values index

/-- Exhaustion of the finite universe uses syntax and arithmetic only. -/
@[elab_as_elim] theorem indexCases (queries : List (Query slots))
    {motive : Fin (size queries) → Prop}
    (original : ∀ index, motive (originalIndex queries index))
    (constant : ∀ index, motive (constantIndex queries index))
    (required : ∀ index, motive (requiredIndex queries index))
    (optional : ∀ index, motive (optionalIndex queries index))
    (index : Fin (size queries)) : motive index :=
  Fin.addCases original (Fin.addCases constant (Fin.addCases required optional)) index

/-- Equivalence, not covariance, transports arbitrary guarded arrow inputs. -/
theorem realizes_congr (graph : Graph slots labels rowSlots) (rows : Fin rowSlots → Row)
    (first last : Fin slots → Ty)
    (same : ∀ index, Common.Equivalent (first index) (last index)) :
    Realizes graph rows first ↔ Realizes graph rows last := by
  simpa only [Realizes, CommonPresenceTailRegular.Models, Body.eval_atRows] using
    CommonPresenceTailRegular.models_congr (fun index => (graph index).atRows rows)
      first last same

/-- Every original solution extends, with the very same row assignment. -/
theorem extend_realizes (queries : List (Query slots)) (graph : Graph slots labels rowSlots)
    (rows : Fin rowSlots → Row) (values : Fin slots → Ty)
    (realizes : Realizes graph rows values) :
    Realizes (extendGraph queries graph) rows (extendValues queries values) := by
  intro index
  refine indexCases queries ?_ ?_ ?_ ?_ index
  · intro original
    rw [extendGraph_original, renameBody_eval, extendValues_original]
    change Common.Equivalent
      ((graph original).eval rows (restrictValues queries (extendValues queries values)))
      (values original)
    rw [restrict_extend]
    exact realizes original
  · intro constant
    rw [extendGraph_constant, constantBody_eval, extendValues_constant]
    exact Common.equivalent_refl _
  · intro query
    rw [extendGraph_required, extendValues_required]
    simp only [Body.eval, extendValues_payload, widthIndex, extendValues_constant]
    exact Common.equivalent_refl _
  · intro query
    rw [extendGraph_optional, extendValues_optional]
    simp only [Body.eval, exactIndex, extendValues_constant, extendValues_required]
    exact Common.equivalent_refl _

/-- No constructor equation is lost by restriction, including cyclic ones. -/
theorem restrict_realizes (queries : List (Query slots)) (graph : Graph slots labels rowSlots)
    (rows : Fin rowSlots → Row) (values : Fin (size queries) → Ty)
    (realizes : Realizes (extendGraph queries graph) rows values) :
    Realizes graph rows (restrictValues queries values) := by
  intro index
  simpa only [extendGraph_original, renameBody_eval, restrictValues, Function.comp_def] using
    realizes (originalIndex queries index)

/-- Arbitrary realizers need only agree by demands at the new nodes. -/
theorem constant_readback (queries : List (Query slots)) (graph : Graph slots labels rowSlots)
    (rows : Fin rowSlots → Row) (values : Fin (size queries) → Ty)
    (realizes : Realizes (extendGraph queries graph) rows values) (index : Fin 3) :
    Common.Equivalent (values (constantIndex queries index)) (constantValue index) := by
  exact Common.equivalent_symm
    (by simpa only [extendGraph_constant, constantBody_eval] using
      realizes (constantIndex queries index))

theorem payload_readback (queries : List (Query slots)) (graph : Graph slots labels rowSlots)
    (rows : Fin rowSlots → Row) (values : Fin (size queries) → Ty)
    (realizes : Realizes (extendGraph queries graph) rows values) (query : Query slots) :
    Common.Equivalent (values (payloadIndex queries query))
      (payloadValue (restrictValues queries values) query) := by
  rcases query with ⟨label, payload⟩
  cases payload with
  | none => exact constant_readback queries graph rows values realizes 0
  | some index => exact Common.equivalent_refl _

private theorem record_congr (label : Nat) {first last tail rest : Ty}
    (payload : Common.Equivalent first last) (remaining : Common.Equivalent tail rest) :
    Common.Equivalent (Common.record label first tail) (Common.record label last rest) :=
  ⟨Common.common_record_mono label payload.1 remaining.1,
    Common.common_record_mono label payload.2 remaining.2⟩

private theorem union_congr {first last first' last' : Ty}
    (left : Common.Equivalent first first') (right : Common.Equivalent last last') :
    Common.Equivalent (.union first last) (.union first' last') :=
  ⟨Common.common_union_mono left.1 right.1, Common.common_union_mono left.2 right.2⟩

theorem required_readback (queries : List (Query slots)) (graph : Graph slots labels rowSlots)
    (rows : Fin rowSlots → Row) (values : Fin (size queries) → Ty)
    (realizes : Realizes (extendGraph queries graph) rows values)
    (index : Fin queries.length) :
    Common.Equivalent (values (requiredIndex queries index))
      (requiredValue (restrictValues queries values) (queries.get index)) := by
  have equation := Common.equivalent_symm (realizes (requiredIndex queries index))
  rw [extendGraph_required] at equation
  exact Common.equivalent_trans equation
    (record_congr (queries.get index).1
      (payload_readback queries graph rows values realizes (queries.get index))
      (constant_readback queries graph rows values realizes 1))

theorem optional_readback (queries : List (Query slots)) (graph : Graph slots labels rowSlots)
    (rows : Fin rowSlots → Row) (values : Fin (size queries) → Ty)
    (realizes : Realizes (extendGraph queries graph) rows values)
    (index : Fin queries.length) :
    Common.Equivalent (values (optionalIndex queries index))
      (optionalValue (restrictValues queries values) (queries.get index)) := by
  have equation := Common.equivalent_symm (realizes (optionalIndex queries index))
  rw [extendGraph_optional] at equation
  exact Common.equivalent_trans equation
    (union_congr (constant_readback queries graph rows values realizes 2)
      (required_readback queries graph rows values realizes index))

/-- Reconstruction retains every original value literally and recovers all
additional values up to the independent common demand order. -/
theorem extended_readback (queries : List (Query slots)) (graph : Graph slots labels rowSlots)
    (rows : Fin rowSlots → Row) (values : Fin (size queries) → Ty)
    (realizes : Realizes (extendGraph queries graph) rows values)
    (index : Fin (size queries)) :
    Common.Equivalent (values index)
      (extendValues queries (restrictValues queries values) index) := by
  refine indexCases queries ?_ ?_ ?_ ?_ index
  · intro original
    rw [extendValues_original]
    exact Common.equivalent_refl _
  · intro constant
    rw [extendValues_constant]
    exact constant_readback queries graph rows values realizes constant
  · intro query
    rw [extendValues_required]
    exact required_readback queries graph rows values realizes query
  · intro query
    rw [extendValues_optional]
    exact optional_readback queries graph rows values realizes query

/-- Complete characterization of arbitrary extended realizers. The extra
node values are determined by the original values up to demand equivalence. -/
theorem realizes_extension_iff (queries : List (Query slots)) (graph : Graph slots labels rowSlots)
    (rows : Fin rowSlots → Row) (values : Fin (size queries) → Ty) :
    Realizes (extendGraph queries graph) rows values ↔
      Realizes graph rows (restrictValues queries values) ∧
      ∀ index, Common.Equivalent (values index)
        (extendValues queries (restrictValues queries values) index) := by
  constructor
  · intro realizes
    exact ⟨restrict_realizes queries graph rows values realizes,
      extended_readback queries graph rows values realizes⟩
  · rintro ⟨original, readback⟩
    exact (realizes_congr (extendGraph queries graph) rows values
      (extendValues queries (restrictValues queries values)) readback).mpr
      (extend_realizes queries graph rows (restrictValues queries values) original)

/-- Extension neither removes nor introduces an original realization. -/
theorem exists_extension_exact (queries : List (Query slots)) (graph : Graph slots labels rowSlots)
    (rows : Fin rowSlots → Row) (values : Fin slots → Ty) :
    Realizes graph rows values ↔
      ∃ extended, Realizes (extendGraph queries graph) rows extended ∧
        restrictValues queries extended = values := by
  constructor
  · intro original
    exact ⟨extendValues queries values, extend_realizes queries graph rows values original,
      restrict_extend queries values⟩
  · rintro ⟨extended, realizes, same⟩
    rw [← same]
    exact restrict_realizes queries graph rows extended realizes

/-- Explicit row constraints and their original IDs are carried unchanged. -/
def extendProblem (queries : List (Query slots))
    (problem : CommonRowTailInference.Problem slots labels rowSlots) :
    CommonRowTailInference.Problem (size queries) labels rowSlots where
  rows := problem.rows
  body := extendGraph queries problem.body

@[simp] theorem extendProblem_rows (queries : List (Query slots))
    (problem : CommonRowTailInference.Problem slots labels rowSlots) :
    (extendProblem queries problem).rows = problem.rows := rfl

theorem problem_extension_exact (queries : List (Query slots))
    (problem : CommonRowTailInference.Problem slots labels rowSlots)
    (rows : Fin rowSlots → Row) (values : Fin slots → Ty) :
    CommonRowTailInference.Models problem rows values ↔
      ∃ extended, CommonRowTailInference.Models (extendProblem queries problem) rows extended ∧
        restrictValues queries extended = values := by
  constructor
  · rintro ⟨rowModels, typeModels⟩
    exact ⟨extendValues queries values, ⟨rowModels,
      extend_realizes queries problem.body rows values typeModels⟩, restrict_extend queries values⟩
  · rintro ⟨extended, ⟨rowModels, typeModels⟩, same⟩
    refine ⟨rowModels, ?_⟩
    rw [← same]
    exact restrict_realizes queries problem.body rows extended typeModels

/-- In particular, the shared source pool can be extended without changing
its original realization predicate or any source variable's shared ID. -/
theorem source_extension_exact (pool : PresenceOpenTailGenerationLowering.Pool rowSlots)
    (queries : List (Query pool.size)) (rows : Fin rowSlots → Row)
    (values : Fin pool.size → Ty) :
    CommonPresenceConstraintGraph.Realizes pool rows values ↔
      ∃ extended, Realizes (extendGraph queries (CommonPresenceConstraintGraph.graph pool))
          rows extended ∧ restrictValues queries extended = values :=
  exists_extension_exact queries (CommonPresenceConstraintGraph.graph pool) rows values

end Yulang.CommonOptionalGraphExtension
