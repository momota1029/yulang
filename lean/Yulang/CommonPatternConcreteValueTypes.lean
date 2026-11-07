import Yulang.CommonPatternConcreteRecordTypes

/-! Principal constructor types of concrete structural values. This is a
readout of actual values, not a replacement semantics for Common demand
subtyping. Lists/nominals still have no rule in the old Common value judgment. -/

namespace Yulang.CommonPatternConcreteValueTypes

set_option backward.isDefEq.respectTransparency false

open Core.CommonData (Value ValueTyping covered)
open Core.PresenceGeneration (Comp)
open CommonPatternConcreteRecordTypes (recordTypeOf recordTypeOf_width)

mutual
  def typeOf : Value → Common.Ty
    | .literal value => .base (Core.CommonData.literalBase value)
    | .pair first last => Common.pair (typeOf first) (typeOf last)
    | .record fields => fieldsType fields
    | .variant tag payload => Common.variant tag (typeOf payload)
    | .nominal _ _ _ | .list _ => .bottom

  def fieldsType : CaseValues.Bindings Empty → Common.Ty
    | [] => Common.exactEmpty
    | (name, value) :: rest => Common.record name (typeOf value) (fieldsType rest)
end

theorem fieldsType_eq (fields : CaseValues.Bindings Empty) : fieldsType fields = recordTypeOf typeOf fields := by
  induction fields with
  | nil => rfl
  | cons field rest ih => simp only [fieldsType, recordTypeOf, ih]

theorem canonical_below (typed : ValueTyping Common.model value result) : Common.Subtype (typeOf value) result.1 := by
  induction typed with
  | literal below => exact below.1
  | pair first last below ihf ihl =>
      exact Common.subtype_trans ((Common.common_pair_iff _ _ _ _).mpr ⟨ihf, ihl⟩) below.1
  | emptyRecord below => exact below.1
  | record head tail width below ihh iht =>
      exact Common.subtype_trans (Common.common_record_mono _ ihh iht) below.1
  | variant payload below ih =>
      exact Common.subtype_trans ((Common.common_variant_iff _ _ _).mpr ih) below.1

private theorem pure_join : Common.rowLe (Common.rowJoin Common.rowEmpty Common.rowEmpty) Common.rowEmpty :=
  (Common.rowJoin_le_iff _ _ _).mpr ⟨Common.rowLe_refl _, Common.rowLe_refl _⟩

theorem canonical_typed (value : Value) (within : covered value = true) :
    ValueTyping Common.model value (Comp.pure Common.model (typeOf value)) := by
  cases value with
  | literal value => exact .literal ⟨Common.subtype_refl _, Common.rowLe_refl _⟩
  | pair first last =>
      have parts : covered first = true ∧ covered last = true := by simpa only [covered, Bool.and_eq_true] using within
      exact .pair (canonical_typed first parts.1) (canonical_typed last parts.2) ⟨Common.subtype_refl _, pure_join⟩
  | record fields =>
      cases fields with
      | nil => exact .emptyRecord ⟨Common.subtype_refl _, Common.rowLe_refl _⟩
      | cons field rest =>
          have smaller : sizeOf field.2 < sizeOf (CaseValues.Value.record (field :: rest)) := by
            cases field; simp; omega
          have parts : covered field.2 = true ∧ covered (.record rest) = true := by
            simpa only [Core.CommonData.covered_record_cons, Bool.and_eq_true] using within
          refine .record (canonical_typed field.2 parts.1) (canonical_typed (.record rest) parts.2) ?_
            ⟨Common.subtype_refl _, pure_join⟩
          change Common.Subtype (fieldsType rest) Common.emptyRecord
          rw [fieldsType_eq]
          exact recordTypeOf_width typeOf rest
  | variant tag payload =>
      have child : covered payload = true := by simpa only [covered] using within
      exact .variant (canonical_typed payload child) ⟨Common.subtype_refl _, Common.rowLe_refl _⟩
  | nominal | list => simp only [covered, Bool.false_eq_true] at within
termination_by sizeOf value
decreasing_by
  all_goals simp_all
  all_goals omega

/-- Every concrete value and arbitrary Common computation result. The full
old value judgment is exactly structural coverage plus a single independent
Common demand comparison from its actual principal constructor type. -/
theorem value_typing_exact (value : Value) (result : Comp Common.model) :
    ValueTyping Common.model value result ↔ covered value = true ∧ Common.Subtype (typeOf value) result.1 := by
  constructor
  · intro typed
    exact ⟨Core.CommonData.typing_covered typed, canonical_below typed⟩
  · rintro ⟨within, below⟩
    exact CommonPatternLookup.typing_change_result (canonical_typed value within) result below

theorem covered_fields_exact (fields : CaseValues.Bindings Empty) :
    covered (.record fields) = true ↔ ∀ field ∈ fields, covered field.2 = true := by
  induction fields with
  | nil => simp [covered]
  | cons field rest ih =>
      simp only [Core.CommonData.covered_record_cons, Bool.and_eq_true, ih, List.forall_mem_cons]

theorem insertion_typed (name : Nat) (value : Value) (fields : CaseValues.Bindings Empty)
    (head : ValueTyping Common.model value a) (tail : ValueTyping Common.model (.record fields) b) :
    ValueTyping Common.model (.record (CaseDataTerms.insert name value fields))
      (Comp.pure Common.model (Common.record name a.1 b.1)) := by
  apply (value_typing_exact _ _).mpr
  constructor
  · apply (covered_fields_exact _).mpr
    intro field member
    rcases List.mem_cons.mp member with same | member
    · subst field
      exact Core.CommonData.typing_covered head
    · exact (covered_fields_exact fields).mp (Core.CommonData.typing_covered tail) field
        (List.mem_filter.mp member).1
  · have image := CommonPatternConcreteRecordTypes.insert_exact typeOf name value fields
    change Common.Subtype (fieldsType _) (Common.record name a.1 b.1)
    rw [fieldsType_eq]
    exact Common.subtype_trans image.1 (Common.common_record_mono name (canonical_below head)
      (by simpa only [typeOf, fieldsType_eq] using canonical_below tail))

theorem default_insertion_typed (name : Nat) (value : Value) (fields : CaseValues.Bindings Empty)
    (base : ValueTyping Common.model (.record fields) a) (fallback : ValueTyping Common.model value b) :
    ValueTyping Common.model (.record (CaseDataTerms.insertDefault name value fields))
      (Comp.pure Common.model (Common.recordDefault name a.1 b.1)) := by
  apply (value_typing_exact _ _).mpr
  constructor
  · apply (covered_fields_exact _).mpr
    intro field member
    unfold CaseDataTerms.insertDefault at member
    split at member
    · exact (covered_fields_exact fields).mp (Core.CommonData.typing_covered base) field member
    · rcases List.mem_append.mp member with old | new
      · exact (covered_fields_exact fields).mp (Core.CommonData.typing_covered base) field old
      · have same := List.mem_singleton.mp new
        subst field
        exact Core.CommonData.typing_covered fallback
  · have image := CommonPatternConcreteRecordTypes.insertDefault_exact typeOf name value fields
    change Common.Subtype (fieldsType _) (Common.recordDefault name a.1 b.1)
    rw [fieldsType_eq]
    exact Common.subtype_trans image.1 (Common.common_default_mono name
      (by
        change Common.Subtype (recordTypeOf typeOf fields) a.1
        simpa only [typeOf, fieldsType_eq] using canonical_below base) (canonical_below fallback))

end Yulang.CommonPatternConcreteValueTypes
