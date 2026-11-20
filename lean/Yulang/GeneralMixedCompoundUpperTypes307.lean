import Yulang.GeneralMixedCompoundUpperSupport307
import Yulang.GeneralDictionaryInspectionHeads215

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17000
namespace Yulang.GeneralMixedCompoundUpperTypes307
open GeneralDictionaryJournalRefinement228Source (foo root_fixed alias_zero width_two top_three)
open GeneralDictionaryCompoundObstruction238 (associated_value)
open GeneralDictionaryCompoundBase239 (lo hi)
open GeneralMixedCompoundUpperBase307 (upper)
open GeneralMixedCompoundUpperSnapshot307 (snap)
open GeneralMixedCompoundUpperRefresh307 (upperState models_iff)
open GeneralMixedCompoundUpperSupport307 (lower identity witness putId putId_models child_history lower_read support_subset)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)
open GeneralDictionaryInspectionHeads215 (Tagged tag_subtype tagged_nominal tagged_shape tagged_scalar)
open CommonNominalFullCarrier

inductive Kind
  | nominal | width | optional | top | variantOptional | variantWidth | index
  deriving DecidableEq, Repr

abbrev optional := GeneralDictionaryOptionalOutput229.value

def meaning : Kind → Ty
  | .nominal => foo
  | .width => .emptyRecord
  | .optional => optional
  | .top => .top
  | .variantOptional => variant 0 optional
  | .variantWidth => variant 0 .emptyRecord
  | .index => .base .int

def tag : Kind → Option CommonNominalFullDemand.Head
  | .nominal => some (.nominal 0 2)
  | .width | .optional => some .records
  | .top => none
  | .variantOptional | .variantWidth => some (.variant 0)
  | .index => some (.base .int)

theorem tagged (k : Kind) (h : tag k = some t) : Tagged (meaning k) t := by
  cases k
  · cases Option.some.inj h; exact tagged_nominal _ _
  · cases Option.some.inj h; exact tagged_shape (.record []) [] rfl
  · cases Option.some.inj h; exact GeneralDictionaryOptionalOutput229.tagged
  · cases h
  · cases Option.some.inj h; exact tagged_shape (.variant 0) [optional] rfl
  · cases Option.some.inj h; exact tagged_shape (.variant 0) [.emptyRecord] rfl
  · cases Option.some.inj h; exact tagged_scalar .int

theorem top_tag_conflict {head : CommonNominalFullDemand.Head} (h : Tagged ty head) : ¬ Subtype .top ty := by
  intro impossible
  let env : CommonNominalFullDemand.Environment Row := ⟨fun _ => .bottom,fun _ => [head]⟩
  exact (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (impossible 0) 0 env (.role 0)
    ((h env).mpr (List.mem_singleton_self _))

theorem tag_preserved {a b : Kind} (same : Equivalent (meaning a) (meaning b)) :
    tag a = tag b := by
  cases ha : tag a with
  | none =>
    have aTop : a = .top := by cases a <;> first | rfl | cases ha
    subst a
    cases hb : tag b with
    | none => rfl
    | some t => exact False.elim (top_tag_conflict (tagged b hb) same.1)
  | some ta =>
    cases hb : tag b with
    | none =>
      have bTop : b = .top := by cases b <;> first | rfl | cases hb
      subst b
      exact False.elim (top_tag_conflict (tagged a ha) same.2)
    | some tb => exact congrArg some (tag_subtype (tagged a ha) (tagged b hb) same.1)

theorem equiv_kind {a b : Kind} (same : Equivalent (meaning a) (meaning b)) : a = b := by
  have tags := tag_preserved same
  have diff := GeneralDictionaryOptionalOutput229.not_width
  have vdiff : ¬ Equivalent (variant 0 optional) (variant 0 .emptyRecord) := fun h =>
    diff ⟨(common_variant_iff ..).mp h.1,(common_variant_iff ..).mp h.2⟩
  cases a <;> cases b <;> first
    | rfl
    | exact False.elim (diff same)
    | exact False.elim (diff ⟨same.2,same.1⟩)
    | exact False.elim (vdiff same)
    | exact False.elim (vdiff ⟨same.2,same.1⟩)
    | cases tags

def kind (n : Nat) : Kind :=
  if n = 0 ∨ n = 1 then .nominal else
  if n = 2 ∨ n = upper then .width else
  if n = 4 ∨ n = lower then .optional else
  if n = lo then .variantOptional else
  if n = hi then .variantWidth else
  if n = identity then .index else .top

theorem at_known (m : Assignment) (valid : Models upperState m) (n : Nat)
    (member : n ∈ GeneralNominalState.sources snap) (notId : n ≠ identity) :
    Equivalent (m n).1 (meaning (kind n)) := by
  have held := child_history m valid
  have parts := GeneralMixedCompoundUpperTrust307.ports m
    (GeneralNominalVersionedSupport233.trusted_models GeneralMixedCompoundUpperTrust307.input_trusted ((models_iff m).mp valid))
  have a := associated_value m held
  have b := width_two m held.1
  have member := support_subset member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · change Equivalent (m 0).1 foo
    exact root_fixed m held.1
  · change Equivalent (m 1).1 foo
    have equal := alias_zero m held.1
    exact equivalent_trans ⟨equal.2,equal.1⟩ (root_fixed m held.1)
  · change Equivalent (m 2).1 .emptyRecord
    exact b
  · change Equivalent (m 3).1 .top
    exact top_three m held.1
  · change Equivalent (m 4).1 optional
    exact a
  · change Equivalent (m lower).1 optional
    exact lower_read m valid
  · change Equivalent (m upper).1 .emptyRecord
    exact GeneralMixedCompoundUpperTrust307.aggregate m
      (GeneralNominalVersionedSupport233.trusted_models GeneralMixedCompoundUpperTrust307.input_trusted ((models_iff m).mp valid))
  · exact (notId rfl).elim
  · change Equivalent (m lo).1 (variant 0 optional)
    exact equivalent_trans parts.1 ⟨(common_variant_iff ..).mpr a.1,(common_variant_iff ..).mpr a.2⟩
  · change Equivalent (m hi).1 (variant 0 .emptyRecord)
    exact equivalent_trans parts.2 ⟨(common_variant_iff ..).mpr b.1,(common_variant_iff ..).mpr b.2⟩

noncomputable abbrev classifierModel := putId GeneralDictionaryCompoundVersionedModel238.extended (.base .int)
theorem classifier_model : Models upperState classifierModel := putId_models witness _
theorem model_class (n : Nat) (member : n ∈ GeneralNominalState.sources snap) :
    Equivalent (classifierModel n).1 (meaning (kind n)) := by
  by_cases atId : n = identity
  · subst n
    change Equivalent (classifierModel identity).1 (.base .int)
    simp only [classifierModel,putId,ite_true]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · exact at_known classifierModel classifier_model n member atId

theorem entailed_kind (one : a ∈ GeneralNominalState.sources snap) (two : b ∈ GeneralNominalState.sources snap)
    (same : GeneralNominalVersionedMixedKernel234.Equal upperState a b) : kind a = kind b := by
  have first := model_class a one
  have last := model_class b two
  exact equiv_kind (equivalent_trans ⟨first.2,first.1⟩ (equivalent_trans (same _ classifier_model) last))

end Yulang.GeneralMixedCompoundUpperTypes307
