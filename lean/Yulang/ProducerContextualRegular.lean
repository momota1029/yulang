import Yulang.ProducerContextual
import Yulang.RegularInferenceModel
import Yulang.InferenceModelMap
import Yulang.SourcePrincipalInference

/-!
# Contextual demand comparison for arbitrary regular graphs

All constructor-unfolding depths, negative-context ranks, type-parameter
assignments and concrete role-head tables are quantified. None is a solver
fuel or cutoff. Arbitrary graph states occur as arrow arguments: the full
arrow iff compares their entire regular observation families, including
cycles, without a closed-negative target or finite-depth premise.

This extends the existing regular carrier and preserves every old structural
subtype and supported source instance. The role observation core is the
explicit head-profile model of `ProducerContextual`; conditional dictionaries,
exact/optional records, record-default images and the complete presence solver
remain separate contracts. The old empty record remains the width supertype.
-/

namespace Yulang.ProducerContextualRegular

open Inference RegularValueTypes

universe u v

variable {Row : Type u} {State : Type v}

def ProducerLe (graph : Graph Row State) (leRow : Row → Row → Prop)
    (source target : Layer Row State) : Prop :=
  ∀ depth, ProducerContextual.ProducerLe leRow
    (source.eval (observe graph depth)) (target.eval (observe graph depth))

def ProducerEq (graph : Graph Row State) (leRow : Row → Row → Prop)
    (source target : Layer Row State) : Prop :=
  ProducerLe graph leRow source target ∧ ProducerLe graph leRow target source

variable {graph : Graph Row State} {leRow : Row → Row → Prop}

/-- Comparing arbitrary graph references needs every constructor depth, with
all contextual demands at that depth. No finiteness or guarded-cycle witness
for the referenced graph is an extra premise. -/
def ReferenceLe (graph : Graph Row State) (leRow : Row → Row → Prop)
    (source target : State) : Prop :=
  ∀ depth, ProducerContextual.ProducerLe leRow
    (observe graph depth source) (observe graph depth target)

theorem referenceLe_refl (state : State) : ReferenceLe graph leRow state state :=
  fun _ => ProducerContextual.producerLe_refl _

theorem referenceLe_trans {a b c : State}
    (first : ReferenceLe graph leRow a b) (last : ReferenceLe graph leRow b c) :
    ReferenceLe graph leRow a c :=
  fun depth => ProducerContextual.producerLe_trans (first depth) (last depth)

/-- Full inversion for arbitrary reference targets, including recursive graph
states. The only laws assumed are those of the row preorder. -/
theorem producerLe_arrow_reference_iff
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (input input' output output' : State) (inputRow inputRow' outputRow outputRow' : Row) :
    ProducerLe graph leRow (.arrow input inputRow output outputRow)
      (.arrow input' inputRow' output' outputRow') ↔
      ReferenceLe graph leRow input' input ∧ leRow inputRow' inputRow ∧
      ReferenceLe graph leRow output output' ∧ leRow outputRow outputRow' := by
  constructor
  · intro below
    have decomposed := fun depth =>
      (ProducerContextual.producerLe_arrow_iff (leRow := leRow) rowRefl rowTrans
        _ _ _ _ _ _ _ _).mp (below depth)
    exact ⟨fun depth => (decomposed depth).1, (decomposed 0).2.1,
      fun depth => (decomposed depth).2.2.1, (decomposed 0).2.2.2⟩
  · rintro ⟨argument, incoming, result, outgoing⟩ depth
    exact ProducerContextual.producerLe_arrow (leRow := leRow) rowTrans
      (argument depth) incoming (result depth) outgoing

theorem producerLe_pair_reference_iff (a b c d : State) :
    ProducerLe graph leRow (.pair a b) (.pair c d) ↔
      ReferenceLe graph leRow a c ∧ ReferenceLe graph leRow b d := by
  constructor
  · intro below
    exact ⟨fun depth => (ProducerContextual.producerLe_pair_iff _ _ _ _).mp (below depth) |>.1,
      fun depth => (ProducerContextual.producerLe_pair_iff _ _ _ _).mp (below depth) |>.2⟩
  · rintro ⟨first, last⟩ depth
    exact (ProducerContextual.producerLe_pair_iff _ _ _ _).mpr ⟨first depth, last depth⟩

theorem producerLe_variant_reference_iff (label : Nat) (a b : State) :
    ProducerLe graph leRow (.variant label a) (.variant label b) ↔
      ReferenceLe graph leRow a b := by
  constructor
  · intro below depth
    exact (ProducerContextual.producerLe_variant_iff label _ _).mp (below depth)
  · intro below depth
    exact (ProducerContextual.producerLe_variant_iff label _ _).mpr (below depth)

theorem producerLe_refl (type : Layer Row State) : ProducerLe graph leRow type type :=
  fun _ => ProducerContextual.producerLe_refl _

theorem producerLe_trans {a b c : Layer Row State}
    (hab : ProducerLe graph leRow a b) (hbc : ProducerLe graph leRow b c) :
    ProducerLe graph leRow a c :=
  fun depth => ProducerContextual.producerLe_trans (hab depth) (hbc depth)

theorem producerEq_refl (type : Layer Row State) : ProducerEq graph leRow type type :=
  ⟨producerLe_refl type, producerLe_refl type⟩

theorem producerEq_symm {a b : Layer Row State} (same : ProducerEq graph leRow a b) :
    ProducerEq graph leRow b a := ⟨same.2, same.1⟩

theorem producerEq_trans {a b c : Layer Row State}
    (first : ProducerEq graph leRow a b) (last : ProducerEq graph leRow b c) :
    ProducerEq graph leRow a c :=
  ⟨producerLe_trans first.1 last.1, producerLe_trans last.2 first.2⟩

theorem structural_subtype_preserved
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    {source target : Layer Row State} (h : RegularValueTypes.Subtype graph leRow source target) :
    ProducerLe graph leRow source target :=
  fun depth => ProducerContextual.structural_subtype_preserved (leRow := leRow) rowTrans (h depth)

theorem producerLe_union_iff (a b c : Layer Row State) :
    ProducerLe graph leRow (.union a b) c ↔
      ProducerLe graph leRow a c ∧ ProducerLe graph leRow b c := by
  constructor
  · intro h
    exact ⟨fun depth => (ProducerContextual.producerLe_union_iff _ _ _).mp (h depth) |>.1,
      fun depth => (ProducerContextual.producerLe_union_iff _ _ _).mp (h depth) |>.2⟩
  · rintro ⟨ha, hb⟩ depth
    exact (ProducerContextual.producerLe_union_iff _ _ _).mpr ⟨ha depth, hb depth⟩

theorem producerLe_union_left (a b : Layer Row State) : ProducerLe graph leRow a (.union a b) :=
  fun _ => ProducerContextual.producerLe_union_left _ _

theorem producerLe_union_right (a b : Layer Row State) : ProducerLe graph leRow b (.union a b) :=
  fun _ => ProducerContextual.producerLe_union_right _ _

theorem producerEq_union_absorb {a b : Layer Row State} (h : ProducerLe graph leRow a b) :
    ProducerEq graph leRow (.union a b) b :=
  ⟨(producerLe_union_iff _ _ _).mpr ⟨h, producerLe_refl _⟩, producerLe_union_right _ _⟩

theorem producerLe_inter_iff (a b c : Layer Row State) :
    ProducerLe graph leRow a (.inter b c) ↔
      ProducerLe graph leRow a b ∧ ProducerLe graph leRow a c := by
  constructor
  · intro h
    exact ⟨fun depth => (ProducerContextual.producerLe_inter_iff _ _ _).mp (h depth) |>.1,
      fun depth => (ProducerContextual.producerLe_inter_iff _ _ _).mp (h depth) |>.2⟩
  · rintro ⟨ha, hb⟩ depth
    exact (ProducerContextual.producerLe_inter_iff _ _ _).mpr ⟨ha depth, hb depth⟩

theorem producerLe_union_mono {a b c d : Layer Row State}
    (first : ProducerLe graph leRow a c) (last : ProducerLe graph leRow b d) :
    ProducerLe graph leRow (.union a b) (.union c d) :=
  fun depth => ProducerContextual.producerLe_union_mono (first depth) (last depth)

theorem producerLe_inter_mono {a b c d : Layer Row State}
    (first : ProducerLe graph leRow a c) (last : ProducerLe graph leRow b d) :
    ProducerLe graph leRow (.inter a b) (.inter c d) :=
  fun depth => ProducerContextual.producerLe_inter_mono (first depth) (last depth)

/-- The existing regular carrier with the new demand-defined order. -/
def model (Row : Type u) (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) : Model :=
  { RegularInferenceModel.model Row empty join leRow with
    subTy := ProducerLe (RegularInferenceModel.graph Row) leRow }

/-- Quoting a value behind a constructor preserves every observation depth. -/
theorem quote_observe_le {a b : RegularInferenceModel.Ty Row}
    (below : ProducerLe (RegularInferenceModel.graph Row) leRow a b) (depth : Nat) :
    ProducerContextual.ProducerLe leRow
      (observe (RegularInferenceModel.graph Row) depth (.node a))
      (observe (RegularInferenceModel.graph Row) depth (.node b)) := by
  cases depth with
  | zero => exact ProducerContextual.producerLe_refl _
  | succ depth => exact below depth

theorem producerLe_pair_iff (a b c d : RegularInferenceModel.Ty Row) :
    ProducerLe (RegularInferenceModel.graph Row) leRow (.pair (.node a) (.node b))
      (.pair (.node c) (.node d)) ↔
      ProducerLe (RegularInferenceModel.graph Row) leRow a c ∧
      ProducerLe (RegularInferenceModel.graph Row) leRow b d := by
  constructor
  · intro below
    exact ⟨fun depth => (ProducerContextual.producerLe_pair_iff _ _ _ _).mp (below (depth + 1)) |>.1,
      fun depth => (ProducerContextual.producerLe_pair_iff _ _ _ _).mp (below (depth + 1)) |>.2⟩
  · rintro ⟨first, last⟩ depth
    exact (ProducerContextual.producerLe_pair_iff _ _ _ _).mpr
      ⟨quote_observe_le first depth, quote_observe_le last depth⟩

theorem producerLe_variant_iff (label : Nat) (a b : RegularInferenceModel.Ty Row) :
    ProducerLe (RegularInferenceModel.graph Row) leRow (.variant label (.node a))
      (.variant label (.node b)) ↔ ProducerLe (RegularInferenceModel.graph Row) leRow a b := by
  constructor
  · intro below depth
    exact (ProducerContextual.producerLe_variant_iff label _ _).mp (below (depth + 1))
  · intro below depth
    exact (ProducerContextual.producerLe_variant_iff label _ _).mpr (quote_observe_le below depth)

theorem producerLe_record_mono (label : Nat) {a b rest tail : RegularInferenceModel.Ty Row}
    (payload : ProducerLe (RegularInferenceModel.graph Row) leRow a b)
    (remaining : ProducerLe (RegularInferenceModel.graph Row) leRow rest tail) :
    ProducerLe (RegularInferenceModel.graph Row) leRow (.record label (.node a) rest)
      (.record label (.node b) tail) := by
  intro depth
  exact ProducerContextual.producerLe_record_mono label (quote_observe_le payload depth) (remaining depth)

/-- Contravariance uses the new order on the entire regular input type. -/
theorem producerLe_arrow (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    {input input' output output' : RegularInferenceModel.Ty Row}
    {inputRow inputRow' outputRow outputRow' : Row}
    (argument : ProducerLe (RegularInferenceModel.graph Row) leRow input' input)
    (incoming : leRow inputRow' inputRow)
    (result : ProducerLe (RegularInferenceModel.graph Row) leRow output output')
    (outgoing : leRow outputRow outputRow') :
    ProducerLe (RegularInferenceModel.graph Row) leRow
      (.arrow (.node input) inputRow (.node output) outputRow)
      (.arrow (.node input') inputRow' (.node output') outputRow') := by
  intro depth
  exact ProducerContextual.producerLe_arrow (leRow := leRow) rowTrans
    (quote_observe_le argument depth) incoming (quote_observe_le result depth) outgoing

/-- In the concrete recursive carrier, arrows decompose against every target
type, with no restriction to embeddings of closed negative demands. -/
theorem producerLe_arrow_iff
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (input input' output output' : RegularInferenceModel.Ty Row)
    (inputRow inputRow' outputRow outputRow' : Row) :
    ProducerLe (RegularInferenceModel.graph Row) leRow
      (.arrow (.node input) inputRow (.node output) outputRow)
      (.arrow (.node input') inputRow' (.node output') outputRow') ↔
      ProducerLe (RegularInferenceModel.graph Row) leRow input' input ∧ leRow inputRow' inputRow ∧
      ProducerLe (RegularInferenceModel.graph Row) leRow output output' ∧ leRow outputRow outputRow' := by
  constructor
  · intro below
    have decomposed := (producerLe_arrow_reference_iff (leRow := leRow) rowRefl rowTrans
      _ _ _ _ _ _ _ _).mp below
    exact ⟨fun depth => decomposed.1 (depth + 1), decomposed.2.1,
      fun depth => decomposed.2.2.1 (depth + 1), decomposed.2.2.2⟩
  · rintro ⟨argument, incoming, result, outgoing⟩
    exact producerLe_arrow (leRow := leRow) rowTrans argument incoming result outgoing

theorem producerEq_pair {a b c d : RegularInferenceModel.Ty Row}
    (first : ProducerEq (RegularInferenceModel.graph Row) leRow a c)
    (last : ProducerEq (RegularInferenceModel.graph Row) leRow b d) :
    ProducerEq (RegularInferenceModel.graph Row) leRow (.pair (.node a) (.node b))
      (.pair (.node c) (.node d)) :=
  ⟨(producerLe_pair_iff _ _ _ _).mpr ⟨first.1, last.1⟩,
    (producerLe_pair_iff _ _ _ _).mpr ⟨first.2, last.2⟩⟩

theorem producerEq_variant (label : Nat) {a b : RegularInferenceModel.Ty Row}
    (same : ProducerEq (RegularInferenceModel.graph Row) leRow a b) :
    ProducerEq (RegularInferenceModel.graph Row) leRow (.variant label (.node a))
      (.variant label (.node b)) :=
  ⟨(producerLe_variant_iff label _ _).mpr same.1, (producerLe_variant_iff label _ _).mpr same.2⟩

theorem producerEq_record (label : Nat) {a b rest tail : RegularInferenceModel.Ty Row}
    (payload : ProducerEq (RegularInferenceModel.graph Row) leRow a b)
    (remaining : ProducerEq (RegularInferenceModel.graph Row) leRow rest tail) :
    ProducerEq (RegularInferenceModel.graph Row) leRow (.record label (.node a) rest)
      (.record label (.node b) tail) :=
  ⟨producerLe_record_mono label payload.1 remaining.1,
    producerLe_record_mono label payload.2 remaining.2⟩

theorem producerEq_arrow (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    {input input' output output' : RegularInferenceModel.Ty Row} (inputRow outputRow : Row)
    (argument : ProducerEq (RegularInferenceModel.graph Row) leRow input input')
    (result : ProducerEq (RegularInferenceModel.graph Row) leRow output output') :
    ProducerEq (RegularInferenceModel.graph Row) leRow
      (.arrow (.node input) inputRow (.node output) outputRow)
      (.arrow (.node input') inputRow (.node output') outputRow) :=
  ⟨producerLe_arrow (leRow := leRow) rowTrans argument.2 (rowRefl _) result.1 (rowRefl _),
    producerLe_arrow (leRow := leRow) rowTrans argument.1 (rowRefl _) result.2 (rowRefl _)⟩

/-- At depth zero both children are unobserved; their union still has the
same demands as bottom. At successor depths quotation distributes literally. -/
theorem quote_observe_union (a b : RegularInferenceModel.Ty Row) (depth : Nat) :
    ProducerContextual.ProducerEq leRow
      (observe (RegularInferenceModel.graph Row) depth (.node (.union a b)))
      (.union (observe (RegularInferenceModel.graph Row) depth (.node a))
        (observe (RegularInferenceModel.graph Row) depth (.node b))) := by
  cases depth with
  | zero =>
      exact ProducerContextual.producerEq_symm
        (ProducerContextual.producerEq_union_absorb (ProducerContextual.producerLe_refl _))
  | succ depth => exact ProducerContextual.producerEq_refl _

theorem pair_union_group (a b c d : RegularInferenceModel.Ty Row) :
    ProducerEq (RegularInferenceModel.graph Row) leRow
      (.union (.pair (.node a) (.node b)) (.pair (.node c) (.node d)))
      (.pair (.node (.union a c)) (.node (.union b d))) := by
  have pointwise : ∀ depth, ProducerContextual.ProducerEq leRow
      (((.union (.pair (.node a) (.node b)) (.pair (.node c) (.node d))) : RegularInferenceModel.Ty Row).eval
        (observe (RegularInferenceModel.graph Row) depth))
      (((.pair (.node (.union a c)) (.node (.union b d))) : RegularInferenceModel.Ty Row).eval
        (observe (RegularInferenceModel.graph Row) depth)) := by
    intro depth
    have first := quote_observe_union (leRow := leRow) a c depth
    have last := quote_observe_union (leRow := leRow) b d depth
    apply ProducerContextual.producerEq_trans (ProducerContextual.pair_union_group _ _ _ _)
    exact ⟨(ProducerContextual.producerLe_pair_iff _ _ _ _).mpr ⟨first.2, last.2⟩,
      (ProducerContextual.producerLe_pair_iff _ _ _ _).mpr ⟨first.1, last.1⟩⟩
  exact ⟨fun depth => (pointwise depth).1, fun depth => (pointwise depth).2⟩

theorem record_union_group (label : Nat) (a rest b tail : RegularInferenceModel.Ty Row) :
    ProducerEq (RegularInferenceModel.graph Row) leRow
      (.union (.record label (.node a) rest) (.record label (.node b) tail))
      (.record label (.node (.union a b)) (.union rest tail)) := by
  have pointwise : ∀ depth, ProducerContextual.ProducerEq leRow
      (((.union (.record label (.node a) rest) (.record label (.node b) tail)) : RegularInferenceModel.Ty Row).eval
        (observe (RegularInferenceModel.graph Row) depth))
      (((.record label (.node (.union a b)) (.union rest tail)) : RegularInferenceModel.Ty Row).eval
        (observe (RegularInferenceModel.graph Row) depth)) := by
    intro depth
    have payload := quote_observe_union (leRow := leRow) a b depth
    apply ProducerContextual.producerEq_trans (ProducerContextual.record_union_group label _ _ _ _)
    exact ⟨ProducerContextual.producerLe_record_mono label payload.2 (ProducerContextual.producerLe_refl _),
      ProducerContextual.producerLe_record_mono label payload.1 (ProducerContextual.producerLe_refl _)⟩
  exact ⟨fun depth => (pointwise depth).1, fun depth => (pointwise depth).2⟩

theorem variant_union (label : Nat) (a b : RegularInferenceModel.Ty Row) :
    ProducerEq (RegularInferenceModel.graph Row) leRow
      (.variant label (.node (.union a b)))
      (.union (.variant label (.node a)) (.variant label (.node b))) := by
  have pointwise : ∀ depth, ProducerContextual.ProducerEq leRow
      (((.variant label (.node (.union a b))) : RegularInferenceModel.Ty Row).eval
        (observe (RegularInferenceModel.graph Row) depth))
      (((.union (.variant label (.node a)) (.variant label (.node b))) : RegularInferenceModel.Ty Row).eval
        (observe (RegularInferenceModel.graph Row) depth)) := by
    intro depth
    have payload := quote_observe_union (leRow := leRow) a b depth
    apply ProducerContextual.producerEq_trans ?_ (ProducerContextual.variant_union label _ _)
    exact ⟨(ProducerContextual.producerLe_variant_iff label _ _).mpr payload.1,
      (ProducerContextual.producerLe_variant_iff label _ _).mpr payload.2⟩
  exact ⟨fun depth => (pointwise depth).1, fun depth => (pointwise depth).2⟩

/-- All constructors map identically. The only proof-bearing step is the
proved preservation of the old structural comparison at every finite depth. -/
def modelMap (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c) :
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
  subtype := structural_subtype_preserved (leRow := leRow) rowTrans
  subrow := id

/-- Preservation reaches every actual legacy supported source and every old
result value/row, including lambda/application and polymorphic lets. It targets
the independent typing judgment over the concrete regular producer model. -/
theorem legacy_instances_preserved (algebra : RowFlowSchemes.Algebra Row)
    (rowAntisymm : ∀ {a b}, algebra.le a b → algebra.le b a → a = b)
    (expression : Expr) (supported : SourcePrincipalInference.supported expression = true)
    (result : Comp (SourcePrincipalInference.model algebra))
    (accepted : (SourcePrincipalInference.infer expression).Instance algebra result) :
    Typing (model Row algebra.empty algebra.join algebra.le) [] expression result := by
  rcases result with ⟨value, row⟩
  simpa only [ModelMap.comp, modelMap, model, SourcePrincipalInference.model,
    JointConstraintInference.model, RegularInferenceModel.model, id] using
    (modelMap algebra.empty algebra.join algebra.le algebra.trans).closed_typing_preserved
    expression (value, row)
    ((SourcePrincipalInference.infer_instances_exact algebra rowAntisymm expression supported (value, row)).mp
      accepted)

namespace Examples

theorem mixed_union_not_equivalent_top (graph : Graph Row State) (leRow : Row → Row → Prop) :
    ¬ ProducerEq graph leRow (.union (.base .int) (.base .str)) .top := by
  intro same
  exact ProducerContextual.Examples.mixed_union_not_equivalent_top leRow ⟨same.1 0, same.2 0⟩

end Examples

end Yulang.ProducerContextualRegular
