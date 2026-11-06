import Yulang.ShadowRecordHeadViews

/-!
# Semantic shadow normalization through the decided rigid relation

An opaque tail is shortened only after its whole equivalence class exposes
another field of the same label. Semantically proper tails are left to the
existing first-field-wins comparison. This distinction avoids introducing
general tail covariance or distribution through lattice connectives.
-/

namespace Yulang.ShadowRecordNormalization

open StructuralBase (Ty IsRecord)
open RigidSemanticRecords (Subtype Equivalent)
open RigidRecordLatticeCheck (depth)
open ShadowRecordHeadViews

universe u
variable {Row : Type u} {leRow : Row → Row → Prop}

/-- Remove semantically exposed equal-label prefixes of an opaque tail.
Every recursive call uses a strictly smaller original constructor depth. -/
def strip [DecidableEq Row] (rows : Row → Row → Bool) (label : Nat) (type : Ty Row) : Ty Row :=
  if proper rows type then type
  else match _selected : headView rows label type with
    | none => type
    | some (_, rest) => strip rows label rest
termination_by depth type
decreasing_by exact headView_depth rows _selected

theorem strip_of_proper [DecidableEq Row] (rows : Row → Row → Bool) (label : Nat)
    (type : Ty Row) (present : proper rows type = true) : strip rows label type = type := by
  rw [strip]
  simp only [present, ↓reduceIte]

theorem strip_of_none [DecidableEq Row] (rows : Row → Row → Bool) (label : Nat)
    (type : Ty Row) (missing : headView rows label type = none) : strip rows label type = type := by
  rw [strip]
  split
  · rfl
  · split
    · rfl
    · rename_i pair found
      rw [missing] at found
      cases found

theorem strip_of_head [DecidableEq Row] (rows : Row → Row → Bool)
    {label : Nat} {type value rest : Ty Row} (absent : proper rows type = false)
    (found : headView rows label type = some (value, rest)) :
    strip rows label type = strip rows label rest := by
  rw [strip]
  simp only [absent, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i missing
    rw [found] at missing
    cases missing
  · rename_i actual tail selected
    have equal : (actual, tail) = (value, rest) := Option.some.inj (selected.symm.trans found)
    cases equal
    rfl

def smartRecord [DecidableEq Row] (rows : Row → Row → Bool)
    (label : Nat) (value rest : Ty Row) : Ty Row :=
  .record label value (strip rows label rest)

section Exact

variable [DecidableEq Row] (rows : Row → Row → Bool)
  (rowExact : ∀ a b, rows a b = true ↔ leRow a b)
  (rowRefl : ∀ row, leRow row row)
  (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)

include rowExact rowRefl rowTrans

theorem strip_proper (label : Nat) {type : Ty Row} (shape : HasProper leRow type) :
    strip rows label type = type :=
  strip_of_proper rows label type ((proper_exact rows rowExact rowRefl rowTrans type).mpr shape)

theorem strip_stable_or_proper (label : Nat) (type : Ty Row) :
    HasProper leRow (strip rows label type) ∨
      headView rows label (strip rows label type) = none := by
  cases shaped : proper rows type with
  | true =>
      rw [strip_of_proper rows label type shaped]
      exact Or.inl ((proper_exact rows rowExact rowRefl rowTrans type).mp shaped)
  | false =>
      cases found : headView rows label type with
      | none =>
          rw [strip_of_none rows label type found]
          exact Or.inr found
      | some pair =>
          obtain ⟨value, rest⟩ := pair
          rw [strip_of_head rows shaped found]
          exact strip_stable_or_proper label rest
termination_by depth type
decreasing_by exact headView_depth rows found

theorem strip_idempotent (label : Nat) (type : Ty Row) :
    strip rows label (strip rows label type) = strip rows label type := by
  rcases strip_stable_or_proper rows rowExact rowRefl rowTrans label type with shape | absent
  · exact strip_proper rows rowExact rowRefl rowTrans label shape
  · exact strip_of_none rows label _ absent

theorem strip_not_proper (label : Nat) (type : Ty Row) (absent : ¬ HasProper leRow type) :
    ¬ HasProper leRow (strip rows label type) := by
  have shaped := (proper_false_iff rows rowExact rowRefl rowTrans type).mpr absent
  cases found : headView rows label type with
  | none => simpa only [strip_of_none rows label type found] using absent
  | some pair =>
      obtain ⟨value, rest⟩ := pair
      rw [strip_of_head rows shaped found]
      exact strip_not_proper label rest
        (headView_tail_opaque rows rowExact rowRefl rowTrans absent found)
termination_by depth type
decreasing_by exact headView_depth rows found

theorem strip_proper_iff (label : Nat) (type : Ty Row) :
    HasProper leRow (strip rows label type) ↔ HasProper leRow type := by
  constructor
  · intro shape
    exact Classical.byContradiction (fun absent =>
      strip_not_proper rows rowExact rowRefl rowTrans label type absent shape)
  · intro shape
    simpa only [strip_proper rows rowExact rowRefl rowTrans label shape] using shape

theorem strip_congr (label : Nat) {left right : Ty Row}
    (same : Equivalent leRow left right) :
    Equivalent leRow (strip rows label left) (strip rows label right) := by
  have matching := proper_congr rows rowExact rowRefl rowTrans same
  cases leftShape : proper rows left with
  | true =>
      have rightShape : proper rows right = true := matching.symm.trans leftShape
      simpa only [strip_of_proper rows label left leftShape,
        strip_of_proper rows label right rightShape] using same
  | false =>
      have rightShape : proper rows right = false := matching.symm.trans leftShape
      have leftAbsent := (proper_false_iff rows rowExact rowRefl rowTrans left).mp leftShape
      have rightAbsent := (proper_false_iff rows rowExact rowRefl rowTrans right).mp rightShape
      cases first : headView rows label left with
      | none =>
          cases last : headView rows label right with
          | none =>
              simpa only [strip_of_none rows label left first,
                strip_of_none rows label right last] using same
          | some pair =>
              obtain ⟨value, rest⟩ := pair
              obtain ⟨other, impossible⟩ := headView_complete rows rowExact rowRefl rowTrans leftAbsent
                (same.trans (headView_sound rows rowExact rowRefl rowTrans last))
              rw [first] at impossible
              cases impossible
      | some pair =>
          obtain ⟨a, r⟩ := pair
          cases last : headView rows label right with
          | none =>
              obtain ⟨other, impossible⟩ := headView_complete rows rowExact rowRefl rowTrans rightAbsent
                (same.symm.trans (headView_sound rows rowExact rowRefl rowTrans first))
              rw [last] at impossible
              cases impossible
          | some pair =>
              obtain ⟨b, s⟩ := pair
              rw [strip_of_head rows leftShape first, strip_of_head rows rightShape last]
              exact strip_congr label
                (headView_tails_equivalent rows rowExact rowRefl rowTrans rightAbsent same first last)
termination_by depth left + depth right
decreasing_by
  have firstDepth := headView_depth rows first
  have lastDepth := headView_depth rows last
  omega

theorem strip_record_opaque (label : Nat) (value rest : Ty Row)
    (absent : ¬ HasProper leRow rest) :
    strip rows label (.record label value rest) = strip rows label rest := by
  apply strip_of_head rows
  · apply (proper_false_iff rows rowExact rowRefl rowTrans _).mpr
    intro shape
    exact absent ((hasProper_record_iff label value rest).mp shape)
  · exact headView_record rows rowExact rowRefl rowTrans label value rest

theorem smartRecord_congr (label : Nat) {value value' rest rest' : Ty Row}
    (head : Equivalent leRow value value') (tail : Equivalent leRow rest rest') :
    Equivalent leRow (smartRecord rows label value rest) (smartRecord rows label value' rest') :=
  RigidSemanticRecords.record_congr label head
    (strip_congr rows rowExact rowRefl rowTrans label tail)

theorem smartRecord_proper (label : Nat) (value rest : Ty Row) (shape : HasProper leRow rest) :
    smartRecord rows label value rest = .record label value rest := by
  simp only [smartRecord, strip_proper rows rowExact rowRefl rowTrans label shape]

theorem smartRecord_isRecord (label : Nat) (value rest : Ty Row) (shape : IsRecord rest) :
    IsRecord (smartRecord rows label value rest) := by
  rw [smartRecord_proper rows rowExact rowRefl rowTrans label value rest (hasProper_of_record shape)]
  exact .field shape

omit [DecidableEq Row] rowExact rowRefl rowTrans in
theorem proper_shadow (label : Nat) (visible hidden rest : Ty Row) (shape : HasProper leRow rest) :
    Equivalent leRow (.record label visible (.record label hidden rest)) (.record label visible rest) := by
  obtain ⟨properTail, properShape, same⟩ := shape
  have before := RigidSemanticRecords.record_congr label (.refl visible)
    (RigidSemanticRecords.record_congr label (.refl hidden) same)
  have after := RigidSemanticRecords.record_congr label (.refl visible) same
  have middle : Equivalent leRow (.record label visible (.record label hidden properTail))
      (.record label visible properTail) := by
    apply RigidRecordFields.proper_equivalent_of_lookup_eq (.field (.field properShape)) (.field properShape)
    intro key
    by_cases equal : key = label <;> simp [Ty.lookup, equal]
  exact before.trans (middle.trans after.symm)

/-- The new shadow equation is interpreted by ordinary old equivalence after
the semantic prefix reduction. Proper tails use their existing visible fields. -/
theorem smartRecord_shadow (label : Nat) (visible hidden rest : Ty Row) :
    Equivalent leRow
      (smartRecord rows label visible (smartRecord rows label hidden rest))
      (smartRecord rows label visible rest) := by
  classical
  by_cases shape : HasProper leRow rest
  · rw [smartRecord_proper rows rowExact rowRefl rowTrans label hidden rest shape,
      smartRecord_proper rows rowExact rowRefl rowTrans label visible rest shape,
      smartRecord_proper rows rowExact rowRefl rowTrans label visible _
        ((hasProper_record_iff label hidden rest).mpr shape)]
    exact proper_shadow label visible hidden rest shape
  · change Equivalent leRow
      (.record label visible (strip rows label (.record label hidden (strip rows label rest))))
      (.record label visible (strip rows label rest))
    rw [strip_record_opaque rows rowExact rowRefl rowTrans label hidden _
      (strip_not_proper rows rowExact rowRefl rowTrans label rest shape),
      strip_idempotent rows rowExact rowRefl rowTrans label rest]
    exact .refl _

/-- Prefix reduction changes no comparison with a rigid demanded record.
This uses the existing masked-demand theorem rather than arbitrary-tail
covariance. Visible payload comparison remains the old exact relation. -/
theorem smartRecord_rigid_comparison (label : Nat) (value rest target : Ty Row)
    (rigid : IsRecord target) :
    Subtype leRow (smartRecord rows label value rest) target ↔
      Subtype leRow (.record label value rest) target := by
  cases shaped : proper rows rest with
  | true =>
      rw [smartRecord_proper rows rowExact rowRefl rowTrans label value rest
        ((proper_exact rows rowExact rowRefl rowTrans rest).mp shaped)]
  | false =>
      cases found : headView rows label rest with
      | none => simp only [smartRecord, strip_of_none rows label rest found]
      | some pair =>
          obtain ⟨hidden, tail⟩ := pair
          change Subtype leRow (.record label value (strip rows label rest)) target ↔ _
          rw [strip_of_head rows shaped found]
          have recur := smartRecord_rigid_comparison label value tail target rigid
          have head := RigidSemanticRecords.record_congr label (.refl value)
            (headView_sound rows rowExact rowRefl rowTrans found)
          apply recur.trans
          constructor
          · intro below
            exact .trans head.1
              ((RigidRecordOpaqueBoundary.hidden_field_rigid_comparison label value hidden tail rigid).mpr below)
          · intro below
            exact (RigidRecordOpaqueBoundary.hidden_field_rigid_comparison label value hidden tail rigid).mp
              (.trans head.2 below)
termination_by depth rest
decreasing_by exact headView_depth rows found

theorem smartRecord_tail_mono (label : Nat) (value : Ty Row) {rest target : Ty Row}
    (rigid : IsRecord target) (below : Subtype leRow rest target) :
    Subtype leRow (smartRecord rows label value rest) (smartRecord rows label value target) := by
  rw [smartRecord_proper rows rowExact rowRefl rowTrans label value target (hasProper_of_record rigid)]
  exact (smartRecord_rigid_comparison rows rowExact rowRefl rowTrans label value rest
    (.record label value target) (.field rigid)).mpr (.recordTail rigid below)

/-- Every normalization step is an equality in the requested new relation.
Its semantic-head queries are old comparisons, already preserved in that relation. -/
theorem smartRecord_sound (label : Nat) (value rest : Ty Row) :
    ShadowSemanticRecords.Equivalent leRow (smartRecord rows label value rest)
      (.record label value rest) := by
  cases shaped : proper rows rest with
  | true =>
      rw [smartRecord_proper rows rowExact rowRefl rowTrans label value rest
        ((proper_exact rows rowExact rowRefl rowTrans rest).mp shaped)]
      exact .refl _
  | false =>
      cases found : headView rows label rest with
      | none =>
          simp only [smartRecord, strip_of_none rows label rest found]
          exact .refl _
      | some pair =>
          obtain ⟨hidden, tail⟩ := pair
          change ShadowSemanticRecords.Equivalent leRow
            (.record label value (strip rows label rest)) (.record label value rest)
          rw [strip_of_head rows shaped found]
          have exposed := headView_sound rows rowExact rowRefl rowTrans found
          have moved := ShadowSemanticRecords.record_congr label (.refl value)
            ⟨ShadowSemanticRecords.rigid_subtype exposed.1, ShadowSemanticRecords.rigid_subtype exposed.2⟩
          exact (smartRecord_sound label value tail).trans
            ((ShadowSemanticRecords.shadow_equivalent label value hidden tail).symm.trans moved.symm)
termination_by depth rest
decreasing_by exact headView_depth rows found

end Exact

def normalize [DecidableEq Row] (rows : Row → Row → Bool) : Ty Row → Ty Row
  | .base base => .base base
  | .bottom => .bottom
  | .top => .top
  | .union left right => .union (normalize rows left) (normalize rows right)
  | .inter left right => .inter (normalize rows left) (normalize rows right)
  | .pair left right => .pair (normalize rows left) (normalize rows right)
  | .emptyRecord => .emptyRecord
  | .record label value rest => smartRecord rows label (normalize rows value) (normalize rows rest)
  | .variant label value => .variant label (normalize rows value)
  | .arrow input inputRow output outputRow =>
      .arrow (normalize rows input) inputRow (normalize rows output) outputRow

section NormalizeExact

variable [DecidableEq Row] (rows : Row → Row → Bool)
  (rowExact : ∀ a b, rows a b = true ↔ leRow a b)
  (rowRefl : ∀ row, leRow row row)
  (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)

include rowExact rowRefl rowTrans

theorem normalize_isRecord {type : Ty Row} (shape : IsRecord type) :
    IsRecord (normalize rows type) := by
  induction shape with
  | empty => exact .empty
  | @field rest label value _ ih =>
      exact smartRecord_isRecord rows rowExact rowRefl rowTrans label (normalize rows value) _ ih

theorem normalize_lookup {type : Ty Row} (shape : IsRecord type) (label : Nat) :
    (normalize rows type).lookup label = (type.lookup label).map (normalize rows) := by
  induction shape with
  | empty => rfl
  | @field rest name value shape ih =>
      simp only [normalize]
      rw [smartRecord_proper rows rowExact rowRefl rowTrans name _ _
        (hasProper_of_record (normalize_isRecord rows rowExact rowRefl rowTrans shape))]
      by_cases same : label = name <;> simp [Ty.lookup, same, ih]

/-- The computation never chooses extra language equations: each returned
normal form is equivalent in the independently defined decision-40 relation. -/
theorem normalize_equivalent (type : Ty Row) :
    ShadowSemanticRecords.Equivalent leRow (normalize rows type) type := by
  induction type with
  | base | bottom | top | emptyRecord => exact .refl _
  | union a b first last => exact ShadowSemanticRecords.union_congr first last
  | inter a b first last => exact ShadowSemanticRecords.inter_congr first last
  | pair a b first last => exact ShadowSemanticRecords.pair_congr first last
  | variant label value ih => exact ShadowSemanticRecords.variant_congr label ih
  | arrow input inputRow output outputRow first last =>
      exact ShadowSemanticRecords.arrow_congr inputRow outputRow
        (rowRefl inputRow) (rowRefl outputRow) first last
  | record label value rest first last =>
      exact (smartRecord_sound rows rowExact rowRefl rowTrans label _ _).trans
        (ShadowSemanticRecords.record_congr label first last)

/-- The normalized constructors satisfy every new declarative rule in the
old, completely decided relation. In particular, both shadow directions are
handled by absorption, and rigid-tail covariance uses preserved demands. -/
theorem normalize_subtype {source target : Ty Row}
    (below : ShadowSemanticRecords.Subtype leRow source target) :
    Subtype leRow (normalize rows source) (normalize rows target) := by
  induction below with
  | refl => exact .refl _
  | trans _ _ first last => exact .trans first last
  | bottom => exact .bottom _
  | top => exact .top _
  | unionLeft => exact .unionLeft _ _
  | unionRight => exact .unionRight _ _
  | unionElim _ _ first last => exact .unionElim first last
  | interLeft => exact .interLeft _ _
  | interRight => exact .interRight _ _
  | interIntro _ _ first last => exact .interIntro first last
  | pair _ _ first last => exact .pair first last
  | variant _ value => exact .variant value
  | arrow _ inputRow _ outputRow input output => exact .arrow input inputRow output outputRow
  | @record source target sourceShape targetShape coverage _ values =>
      apply Subtype.record (normalize_isRecord rows rowExact rowRefl rowTrans sourceShape)
        (normalize_isRecord rows rowExact rowRefl rowTrans targetShape)
      · intro label expected found
        rw [normalize_lookup rows rowExact rowRefl rowTrans targetShape] at found
        obtain ⟨original, originalFound, _⟩ := Option.map_eq_some_iff.mp found
        obtain ⟨actual, actualFound⟩ := coverage label original originalFound
        exact ⟨normalize rows actual, by
          rw [normalize_lookup rows rowExact rowRefl rowTrans sourceShape, actualFound]
          rfl⟩
      · intro label actual expected actualFound expectedFound
        rw [normalize_lookup rows rowExact rowRefl rowTrans sourceShape] at actualFound
        rw [normalize_lookup rows rowExact rowRefl rowTrans targetShape] at expectedFound
        obtain ⟨originalActual, originalFound, rfl⟩ := Option.map_eq_some_iff.mp actualFound
        obtain ⟨originalExpected, originalExpectedFound, rfl⟩ := Option.map_eq_some_iff.mp expectedFound
        exact values label originalActual originalExpected originalFound originalExpectedFound
  | @recordCongr value value' rest rest' label _ _ _ _ head backHead tail backTail =>
      exact (smartRecord_congr rows rowExact rowRefl rowTrans label
        ⟨head, backHead⟩ ⟨tail, backTail⟩).1
  | @recordTail rest' rest label value rigid _ tail =>
      exact smartRecord_tail_mono rows rowExact rowRefl rowTrans label (normalize rows value)
        (normalize_isRecord rows rowExact rowRefl rowTrans rigid) tail
  | shadowErase label visible hidden rest =>
      exact (smartRecord_shadow rows rowExact rowRefl rowTrans label
        (normalize rows visible) (normalize rows hidden) (normalize rows rest)).1
  | shadowInsert label visible hidden rest =>
      exact (smartRecord_shadow rows rowExact rowRefl rowTrans label
        (normalize rows visible) (normalize rows hidden) (normalize rows rest)).2

/-- Exact reduction to the previous ground comparison. Neither normalization
nor this theorem enumerates guessed intermediate types or accepts a semantic
comparison oracle for the new relation. -/
theorem normalize_exact (source target : Ty Row) :
    Subtype leRow (normalize rows source) (normalize rows target) ↔
      ShadowSemanticRecords.Subtype leRow source target := by
  constructor
  · intro below
    exact .trans (normalize_equivalent rows rowExact rowRefl rowTrans source).2
      (.trans (ShadowSemanticRecords.rigid_subtype below)
        (normalize_equivalent rows rowExact rowRefl rowTrans target).1)
  · exact normalize_subtype rows rowExact rowRefl rowTrans

end NormalizeExact

end Yulang.ShadowRecordNormalization
