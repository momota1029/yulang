import Yulang.ProducerDemand
import Yulang.RegularInferenceModel
import Yulang.InferenceModelMap
import Yulang.SourcePrincipalInference

/-!
# Demand comparison on the existing regular carrier

Every finite observation is compared with `ProducerDemand.ProducerLe`.
The carrier, graph unfolding, arrow constructors, row operations and guarded
block representation are unchanged. This supplies an actual concrete model
map from the original regular model; no preservation law is assumed as data.
It does not yet add presence/exact-record/default constructors or solve the
new comparison. Arrow argument observations retain the finite structural
boundary documented in `ProducerDemand`.
-/

namespace Yulang.ProducerRegular

open Inference RegularValueTypes

universe u v

variable {Row : Type u} {State : Type v}

def ProducerLe (graph : Graph Row State) (leRow : Row → Row → Prop)
    (source target : Layer Row State) : Prop :=
  ∀ depth, ProducerDemand.ProducerLe leRow
    (source.eval (observe graph depth)) (target.eval (observe graph depth))

def ProducerEq (graph : Graph Row State) (leRow : Row → Row → Prop)
    (source target : Layer Row State) : Prop :=
  ProducerLe graph leRow source target ∧ ProducerLe graph leRow target source

variable {graph : Graph Row State} {leRow : Row → Row → Prop}

theorem producerLe_refl (type : Layer Row State) : ProducerLe graph leRow type type :=
  fun _ => ProducerDemand.producerLe_refl _

theorem producerLe_trans {a b c : Layer Row State}
    (hab : ProducerLe graph leRow a b) (hbc : ProducerLe graph leRow b c) :
    ProducerLe graph leRow a c :=
  fun depth => ProducerDemand.producerLe_trans (hab depth) (hbc depth)

theorem structural_subtype_preserved
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    {source target : Layer Row State} (h : RegularValueTypes.Subtype graph leRow source target) :
    ProducerLe graph leRow source target :=
  fun depth => ProducerDemand.structural_subtype_preserved (leRow := leRow) rowTrans (h depth)

theorem producerLe_union_iff (a b c : Layer Row State) :
    ProducerLe graph leRow (.union a b) c ↔
      ProducerLe graph leRow a c ∧ ProducerLe graph leRow b c := by
  constructor
  · intro h
    exact ⟨fun depth => (ProducerDemand.producerLe_union_iff _ _ _).mp (h depth) |>.1,
      fun depth => (ProducerDemand.producerLe_union_iff _ _ _).mp (h depth) |>.2⟩
  · rintro ⟨ha, hb⟩ depth
    exact (ProducerDemand.producerLe_union_iff _ _ _).mpr ⟨ha depth, hb depth⟩

theorem producerLe_union_left (a b : Layer Row State) : ProducerLe graph leRow a (.union a b) :=
  fun _ => ProducerDemand.producerLe_union_left _ _

theorem producerLe_union_right (a b : Layer Row State) : ProducerLe graph leRow b (.union a b) :=
  fun _ => ProducerDemand.producerLe_union_right _ _

theorem producerEq_union_absorb {a b : Layer Row State} (h : ProducerLe graph leRow a b) :
    ProducerEq graph leRow (.union a b) b :=
  ⟨(producerLe_union_iff _ _ _).mpr ⟨h, producerLe_refl _⟩, producerLe_union_right _ _⟩

/-- The existing regular carrier with the new demand-defined order. -/
def model (Row : Type u) (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) : Model :=
  { RegularInferenceModel.model Row empty join leRow with
    subTy := ProducerLe (RegularInferenceModel.graph Row) leRow }

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

end Yulang.ProducerRegular
