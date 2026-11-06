import Yulang.ShadowRegularValueTypes
import Yulang.RegularInferenceModel
import Yulang.InferenceModelMap

/-!
# The common regular inference carrier with shadow subtyping

This model reuses `RegularInferenceModel.State`, its graph, and every value and
row constructor. Its subtype relation compares all finite observations using
the decision-40 finite relation. In particular, the existing record operation
has semantic congruence and arbitrary-layer-tail hidden-field equality.

Closing a finite regular block preserves and reflects every subtype judgment.
Finite raw trees also embed with exact subtype reflection. Formula and source
typing transport below is preservation only: regular existential witnesses
need not be finite trees, and the previous solver's completeness is not implied.
No open-tail coalescing or regular decision procedure is supplied here.
-/

namespace Yulang.ShadowRegularInferenceModel

open Inference
open RegularValueTypes (Layer)
open RegularInferenceModel (State Ty graph blockGraph blockRef finiteRef)

universe u

variable {Row : Type u} {size : Nat}

abbrev Subtype (leRow : Row → Row → Prop) :=
  ShadowRegularValueTypes.Subtype (graph Row) leRow

abbrev Equivalent (leRow : Row → Row → Prop) :=
  ShadowRegularValueTypes.Equivalent (graph Row) leRow

/-- The carrier and constructors are unchanged; only subtyping is extended. -/
def model (Row : Type u) (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) : Inference.Model :=
  { RegularInferenceModel.model Row empty join leRow with subTy := Subtype leRow }

@[simp] theorem model_record (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (label : Nat) (value rest : Ty Row) :
    (model Row empty join leRow).record label value rest = .record label (.node value) rest := rfl

theorem subtype_refl (leRow : Row → Row → Prop) (type : Ty Row) : Subtype leRow type type :=
  ShadowRegularValueTypes.subtype_refl type

theorem subtype_trans {leRow : Row → Row → Prop} {left middle right : Ty Row}
    (first : Subtype leRow left middle) (last : Subtype leRow middle right) :
    Subtype leRow left right :=
  ShadowRegularValueTypes.subtype_trans first last

theorem quote_subtype (leRow : Row → Row → Prop) (left right : Ty Row) :
    ShadowRegularValueTypes.NodeSubtype (graph Row) leRow (.node left) (.node right) ↔
      Subtype leRow left right := Iff.rfl

theorem pair_subtype {leRow : Row → Row → Prop} {left left' right right' : Ty Row}
    (first : Subtype leRow left left') (last : Subtype leRow right right') :
    Subtype leRow (.pair (.node left) (.node right)) (.pair (.node left') (.node right')) :=
  ShadowRegularValueTypes.pair_subtype first last

theorem variant_subtype {leRow : Row → Row → Prop} (label : Nat) {left right : Ty Row}
    (below : Subtype leRow left right) :
    Subtype leRow (.variant label (.node left)) (.variant label (.node right)) :=
  ShadowRegularValueTypes.variant_subtype label below

theorem arrow_subtype {leRow : Row → Row → Prop} {input input' output output' : Ty Row}
    {inputRow inputRow' outputRow outputRow' : Row}
    (before : Subtype leRow input' input) (beforeRow : leRow inputRow' inputRow)
    (after : Subtype leRow output output') (afterRow : leRow outputRow outputRow') :
    Subtype leRow (.arrow (.node input) inputRow (.node output) outputRow)
      (.arrow (.node input') inputRow' (.node output') outputRow') :=
  ShadowRegularValueTypes.arrow_subtype before beforeRow after afterRow

theorem record_congr {leRow : Row → Row → Prop} (label : Nat)
    {value value' rest rest' : Ty Row}
    (head : Equivalent leRow value value') (tail : Equivalent leRow rest rest') :
    Equivalent leRow (.record label (.node value) rest) (.record label (.node value') rest') :=
  ShadowRegularValueTypes.record_congr label head tail

theorem record_tail_covariant {leRow : Row → Row → Prop} (label : Nat) (value : Ty Row)
    {rest rest' : Ty Row} (rigid : rest'.IsRecord) (below : Subtype leRow rest rest') :
    Subtype leRow (.record label (.node value) rest) (.record label (.node value) rest') :=
  ShadowRegularValueTypes.record_tail_covariant label (.node value) rigid below

theorem record_head {leRow : Row → Row → Prop} (label : Nat) (value : Ty Row)
    {rest : Ty Row} (admissible : Subtype leRow rest .emptyRecord) :
    Subtype leRow (.record label (.node value) rest) (.record label (.node value) .emptyRecord) :=
  ShadowRegularValueTypes.record_head label (.node value) admissible

/-- The existing operation obeys the shadow equation for all values in the
common carrier, including finite cyclic blocks and arbitrary opaque tails. -/
theorem record_shadow {leRow : Row → Row → Prop} (label : Nat) (visible hidden rest : Ty Row) :
    Equivalent leRow (.record label (.node visible) (.record label (.node hidden) rest))
      (.record label (.node visible) rest) :=
  ShadowRegularValueTypes.shadow_equivalent label (.node visible) (.node hidden) rest

theorem record_empty_exact {leRow : Row → Row → Prop}
    (label : Nat) (value rest : Ty Row) :
    Subtype leRow (.record label (.node value) rest) .emptyRecord ↔
      Subtype leRow rest .emptyRecord :=
  ShadowRegularValueTypes.record_empty_exact label (.node value) rest

theorem record_singleton_same_exact {leRow : Row → Row → Prop}
    (label : Nat) (value rest expected : Ty Row) :
    Subtype leRow (.record label (.node value) rest) (.record label (.node expected) .emptyRecord) ↔
      Subtype leRow value expected ∧ Subtype leRow rest .emptyRecord :=
  ShadowRegularValueTypes.record_singleton_same_exact label (.node value) (.node expected) rest

theorem record_singleton_other_exact {leRow : Row → Row → Prop}
    (label demanded : Nat) (different : label ≠ demanded) (value rest expected : Ty Row) :
    Subtype leRow (.record label (.node value) rest) (.record demanded (.node expected) .emptyRecord) ↔
      Subtype leRow rest (.record demanded (.node expected) .emptyRecord) :=
  ShadowRegularValueTypes.record_singleton_other_exact label demanded different
    (.node value) (.node expected) rest

/-! ## The existing finite-block representation is exact -/

theorem block_subtype (body : Fin size → Layer Row (Fin size ⊕ State Row))
    (leRow : Row → Row → Prop) (left right : Layer Row (Fin size ⊕ State Row)) :
    Subtype leRow (left.map (blockRef body)) (right.map (blockRef body)) ↔
      ShadowRegularValueTypes.Subtype (blockGraph body) leRow left right :=
  ShadowRegularValueTypes.subtype_morphism (graph Row) (blockRef body)
    (RegularInferenceModel.block_morphism body) left right

theorem block_nodeSubtype (body : Fin size → Layer Row (Fin size ⊕ State Row))
    (leRow : Row → Row → Prop) (left right : Fin size ⊕ State Row) :
    ShadowRegularValueTypes.NodeSubtype (graph Row) leRow (blockRef body left) (blockRef body right) ↔
      ShadowRegularValueTypes.NodeSubtype (blockGraph body) leRow left right := by
  unfold ShadowRegularValueTypes.NodeSubtype
  rw [← RegularInferenceModel.block_morphism body left, ← RegularInferenceModel.block_morphism body right]
  exact block_subtype body leRow _ _

theorem finite_subtype (source : RegularValueTypes.FiniteGraph Row size)
    (leRow : Row → Row → Prop) (left right : Layer Row (Fin size)) :
    Subtype leRow (left.map (finiteRef source)) (right.map (finiteRef source)) ↔
      ShadowRegularValueTypes.Subtype source leRow left right :=
  ShadowRegularValueTypes.subtype_morphism (graph Row) (finiteRef source)
    (RegularInferenceModel.finite_morphism source) left right

theorem finite_nodeSubtype (source : RegularValueTypes.FiniteGraph Row size)
    (leRow : Row → Row → Prop) (left right : Fin size) :
    ShadowRegularValueTypes.NodeSubtype (graph Row) leRow (finiteRef source left) (finiteRef source right) ↔
      ShadowRegularValueTypes.NodeSubtype source leRow left right := by
  unfold ShadowRegularValueTypes.NodeSubtype
  rw [← RegularInferenceModel.finite_morphism source left, ← RegularInferenceModel.finite_morphism source right]
  exact finite_subtype source leRow _ _

/-! ## A constructor-preserving embedding of finite raw types -/

def embed : StructuralBase.Ty Row → Ty Row
  | .base value => .base value
  | .bottom => .bottom
  | .top => .top
  | .union left right => .union (embed left) (embed right)
  | .inter left right => .inter (embed left) (embed right)
  | .pair left right => .pair (.node (embed left)) (.node (embed right))
  | .emptyRecord => .emptyRecord
  | .record label value rest => .record label (.node (embed value)) (embed rest)
  | .variant label value => .variant label (.node (embed value))
  | .arrow input inputRow output outputRow =>
      .arrow (.node (embed input)) inputRow (.node (embed output)) outputRow

def treeRef (type : StructuralBase.Ty Row) : State Row := .node (embed type)

theorem embed_as_map (type : StructuralBase.Ty Row) :
    (RegularValueTypes.ofTree type).map treeRef = embed type := by
  induction type <;> simp [RegularValueTypes.ofTree, Layer.map, embed, treeRef, *]

theorem tree_morphism (type : StructuralBase.Ty Row) :
    (RegularValueTypes.treeGraph Row type).map treeRef = graph Row (treeRef type) :=
  embed_as_map type

theorem tree_observe (depth : Nat) (type : StructuralBase.Ty Row) :
    RegularValueTypes.observe (graph Row) depth (treeRef type) =
      RegularValueTypes.observe (RegularValueTypes.treeGraph Row) depth type :=
  RegularValueTypes.observe_morphism (graph Row) treeRef tree_morphism depth type

/-- Finite types retain exactly their comparisons after embedding into the
same carrier that also holds recursive blocks. -/
theorem embed_subtype (leRow : Row → Row → Prop) (left right : StructuralBase.Ty Row) :
    Subtype leRow (embed left) (embed right) ↔ ShadowSemanticRecords.Subtype leRow left right := by
  rw [← embed_as_map left, ← embed_as_map right]
  exact (ShadowRegularValueTypes.subtype_morphism (graph Row) treeRef tree_morphism _ _).trans
    (ShadowRegularValueTypes.finite_conservative left right)

theorem embed_equivalent (leRow : Row → Row → Prop) (left right : StructuralBase.Ty Row) :
    Equivalent leRow (embed left) (embed right) ↔ ShadowSemanticRecords.Equivalent leRow left right :=
  and_congr (embed_subtype leRow left right) (embed_subtype leRow right left)

/-! ## Preservation of the original formulas and source typing -/

/-- All values, rows and constructors are identities for the old regular
model; its comparisons are preserved, with no converse completeness claim. -/
def legacyMap (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop) :
    ModelMap (RegularInferenceModel.model Row empty join leRow) (model Row empty join leRow) where
  value := id
  row := id
  base _ := rfl
  bottom := rfl
  top := rfl
  union _ _ := rfl
  inter _ _ := rfl
  pair _ _ := rfl
  emptyRecord := rfl
  record _ _ _ := rfl
  variant _ _ := rfl
  arrow _ _ _ _ := rfl
  empty := rfl
  join _ _ := rfl
  subtype := ShadowRegularValueTypes.old_subtype
  subrow proof := proof

def finiteMap (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop) :
    ModelMap (ShadowSemanticRecords.model Row empty join leRow) (model Row empty join leRow) where
  value := embed
  row := id
  base _ := rfl
  bottom := rfl
  top := rfl
  union _ _ := rfl
  inter _ _ := rfl
  pair _ _ := rfl
  emptyRecord := rfl
  record _ _ _ := rfl
  variant _ _ := rfl
  arrow _ _ _ _ := rfl
  empty := rfl
  join _ _ := rfl
  subtype := (embed_subtype leRow _ _).mpr
  subrow proof := proof

theorem old_formula_preserved (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (formula : Formula α) (assignment : α → Ty Row × Row)
    (held : formula.Holds (RegularInferenceModel.model Row empty join leRow) assignment) :
    formula.Holds (model Row empty join leRow) assignment :=
  (legacyMap empty join leRow).formula_preserved formula assignment held

theorem old_closed_typing_preserved (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (expression : Expr) (result : Ty Row × Row)
    (typed : Typing (RegularInferenceModel.model Row empty join leRow) [] expression result) :
    Typing (model Row empty join leRow) [] expression result :=
  (legacyMap empty join leRow).closed_typing_preserved expression result typed

theorem finite_formula_preserved (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (formula : Formula α) (assignment : α → StructuralBase.Ty Row × Row)
    (held : formula.Holds (ShadowSemanticRecords.model Row empty join leRow) assignment) :
    formula.Holds (model Row empty join leRow)
      (fun index => (embed (assignment index).1, (assignment index).2)) :=
  (finiteMap empty join leRow).formula_preserved formula assignment held

theorem finite_closed_typing_preserved (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (expression : Expr) (result : StructuralBase.Ty Row × Row)
    (typed : Typing (ShadowSemanticRecords.model Row empty join leRow) [] expression result) :
    Typing (model Row empty join leRow) [] expression (embed result.1, result.2) :=
  (finiteMap empty join leRow).closed_typing_preserved expression result typed

end Yulang.ShadowRegularInferenceModel
