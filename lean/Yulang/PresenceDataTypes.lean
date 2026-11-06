import Yulang.SourceDataRuntime

/-!
# Presence-aware semantic types for the data core

These types are predicates on the existing first-order runtime values.
Subtyping is inclusion. Required fields, optional fields, and known absence
are distinct predicates. In particular `records` accepts every record, while
`exactEmpty` describes precisely the empty record value. The former is the
meaning of the legacy width-supertype `{}`; it is not reinterpreted as absence.

The constructor images below define a separate data typing model. They do not
change `StructuralBase`, the shadow subtype relations, or their principal
inference statements. Literal values still contain only the existing base tag.
-/

namespace Yulang.PresenceDataTypes

open Inference SourceDataRuntime

abbrev Ty := Value → Prop

def Le (left right : Ty) : Prop := ∀ value, left value → right value

def exact (expected : Value) : Ty := fun value => value = expected
def any : Ty := fun _ => True
def never : Ty := fun _ => False
def union (left right : Ty) : Ty := fun value => left value ∨ right value
def inter (left right : Ty) : Ty := fun value => left value ∧ right value
def base (name : Base) : Ty := exact (.base name)
def exactEmpty : Ty := exact (.record [])

def pair (left right : Ty) : Ty
  | .pair first last => left first ∧ right last
  | _ => False

def variant (label : Nat) (payload : Ty) : Ty
  | .variant name value => name = label ∧ payload value
  | _ => False

def records : Ty
  | .record _ => True
  | _ => False

def lookup (label : Nat) : Value → Option Value
  | .record fields => Fields.lookup label fields
  | _ => none

def required (label : Nat) (payload : Ty) : Ty := fun value =>
  records value ∧ ∃ item, lookup label value = some item ∧ payload item

/-- An optional field constrains every present value, without requiring one. -/
def optional (label : Nat) (payload : Ty) : Ty := fun value =>
  records value ∧ ∀ item, lookup label value = some item → payload item

/-- Absence is stronger than simply omitting a field from a width demand. -/
def lacks (label : Nat) : Ty := fun value => records value ∧ lookup label value = none

def record (label : Nat) (head tail : Ty) : Ty := fun result =>
  ∃ value fields, head value ∧ tail (.record fields) ∧
    result = .record (Fields.insert label value fields)

/-- This is the semantic image of the two already evaluated operands. The
source typing rule separately requires both expressions to be well typed. -/
def recordDefault (label : Nat) (source fallback : Ty) : Ty := fun result =>
  ∃ fields value, source (.record fields) ∧ fallback value ∧
    result = .record (Fields.insertDefault label value fields)

theorem le_refl (type : Ty) : Le type type := fun _ valid => valid

theorem le_trans {left middle right : Ty} (first : Le left middle) (last : Le middle right) :
    Le left right := fun value valid => last value (first value valid)

theorem exact_le_iff (value : Value) (type : Ty) : Le (exact value) type ↔ type value :=
  ⟨fun below => below value rfl, fun valid _ same => same ▸ valid⟩

theorem union_is_join (left right target : Ty) :
    Le (union left right) target ↔ Le left target ∧ Le right target :=
  ⟨fun below => ⟨fun value valid => below value (Or.inl valid),
      fun value valid => below value (Or.inr valid)⟩,
    fun below value valid => valid.elim (below.1 value) (below.2 value)⟩

theorem pair_exact (left right : Value) :
    Le (pair (exact left) (exact right)) (exact (.pair left right)) := by
  intro value valid
  cases value with
  | pair first last =>
      obtain ⟨rfl, rfl⟩ := valid
      rfl
  | base | record | variant => cases valid

theorem variant_exact (label : Nat) (value : Value) :
    Le (variant label (exact value)) (exact (.variant label value)) := by
  intro result valid
  cases result with
  | variant name payload =>
      obtain ⟨rfl, rfl⟩ := valid
      rfl
  | base | pair | record => cases valid

theorem record_exact (label : Nat) (head : Value) (tail : List (Nat × Value)) :
    Le (record label (exact head) (exact (.record tail)))
      (exact (.record (Fields.insert label head tail))) := by
  rintro result ⟨value, fields, rfl, same, rfl⟩
  cases Value.record.inj same
  rfl

theorem recordDefault_exact (label : Nat) (source : List (Nat × Value)) (fallback : Value) :
    Le (recordDefault label (exact (.record source)) (exact fallback))
      (exact (.record (Fields.insertDefault label fallback source))) := by
  rintro result ⟨fields, value, same, rfl, rfl⟩
  cases Value.record.inj same
  rfl

theorem exact_record_le_records (fields : List (Nat × Value)) :
    Le (exact (.record fields)) records :=
  (exact_le_iff _ _).mpr trivial

theorem exactEmpty_lacks (label : Nat) : Le exactEmpty (lacks label) := by
  rintro value rfl
  exact ⟨trivial, rfl⟩

theorem lacks_optional (label : Nat) (payload : Ty) : Le (lacks label) (optional label payload) := by
  intro value valid
  refine ⟨valid.1, ?_⟩
  intro item found
  rw [valid.2] at found
  cases found

theorem optional_records (label : Nat) (payload : Ty) : Le (optional label payload) records :=
  fun _ valid => valid.1

theorem required_optional (label : Nat) (payload : Ty) : Le (required label payload) (optional label payload) := by
  rintro value ⟨shape, item, found, valid⟩
  refine ⟨shape, ?_⟩
  intro other otherFound
  have same := Option.some.inj (found.symm.trans otherFound)
  simpa [← same] using valid

/-- Width-supertype information alone cannot justify an absence refinement. -/
theorem records_not_le_lacks (label : Nat) : ¬ Le records (lacks label) := by
  intro below
  have absent := (below (.record [(label, .base .int)]) trivial).2
  simp [lookup, Fields.lookup] at absent

theorem records_not_le_exactEmpty : ¬ Le records exactEmpty := by
  intro below
  have same := below (.record [(0, .base .int)]) trivial
  cases same

/-- In particular an unconstrained record cannot safely acquire an arbitrary
optional payload bound merely because it is accepted by the legacy `{}`. -/
theorem records_not_le_optional_int (label : Nat) : ¬ Le records (optional label (base .int)) := by
  intro below
  have valid := below (.record [(label, .base .str)]) trivial
  have wrong := valid.2 (.base .str) (by simp [lookup, Fields.lookup])
  cases wrong

theorem recordDefault_records (label : Nat) (source fallback : Ty) :
    Le (recordDefault label source fallback) records := by
  rintro value ⟨fields, item, _, _, rfl⟩
  trivial

/-- A known present field wins, even though the fallback expression must
still run. No union with its payload type is needed for this projection. -/
theorem recordDefault_present (label : Nat) (source fallback payload : Ty)
    (present : Le source (required label payload)) :
    Le (recordDefault label source fallback) (required label payload) := by
  rintro result ⟨fields, value, sourceValid, _, rfl⟩
  obtain ⟨_, original, found, valid⟩ := present _ sourceValid
  refine ⟨trivial, original, ?_, valid⟩
  change Fields.lookup label (Fields.insertDefault label value fields) = some original
  rw [Fields.lookup_insertDefault_same]
  change Fields.lookup label fields = some original at found
  rw [found]
  rfl

/-- Known absence selects the fallback payload type. -/
theorem recordDefault_absent (label : Nat) (source fallback : Ty)
    (absent : Le source (lacks label)) :
    Le (recordDefault label source fallback) (required label fallback) := by
  rintro result ⟨fields, value, sourceValid, fallbackValid, rfl⟩
  refine ⟨trivial, value, ?_, fallbackValid⟩
  change Fields.lookup label (Fields.insertDefault label value fields) = some value
  rw [Fields.lookup_insertDefault_same]
  have missing := (absent _ sourceValid).2
  change Fields.lookup label fields = none at missing
  rw [missing]
  rfl

/-- Decision 44: an unknown optional payload and the fallback contribute to
the required result field through union. Both cases are quantified. -/
theorem recordDefault_optional (label : Nat) (source payload fallback : Ty)
    (optionalField : Le source (optional label payload)) :
    Le (recordDefault label source fallback) (required label (union payload fallback)) := by
  rintro result ⟨fields, value, sourceValid, fallbackValid, rfl⟩
  have valid := optionalField _ sourceValid
  refine ⟨trivial, ?_⟩
  cases found : Fields.lookup label fields with
  | none =>
      exact ⟨value, by simp [lookup, found], Or.inr fallbackValid⟩
  | some existing =>
      exact ⟨existing, by simp [lookup, found], Or.inl (valid.2 existing found)⟩

/-- Every observation of an unrelated field is preserved, including absence
and correlations represented by arbitrary predicates of that observation. -/
theorem recordDefault_other (label query : Nat) (different : query ≠ label)
    (source fallback : Ty) (property : Option Value → Prop)
    (original : ∀ value, source value → property (lookup query value)) :
    ∀ value, recordDefault label source fallback value → property (lookup query value) := by
  rintro result ⟨fields, value, valid, _, rfl⟩
  change property (Fields.lookup query (Fields.insertDefault label value fields))
  rw [Fields.lookup_insertDefault_other label query value different]
  exact original (.record fields) valid

theorem recordDefault_other_required (label query : Nat) (different : query ≠ label)
    (source fallback payload : Ty) (present : Le source (required query payload)) :
    Le (recordDefault label source fallback) (required query payload) := by
  intro value valid
  refine ⟨recordDefault_records label source fallback _ valid, ?_⟩
  exact recordDefault_other label query different source fallback
    (fun found => ∃ item, found = some item ∧ payload item)
    (fun original held => (present original held).2) value valid

theorem recordDefault_other_optional (label query : Nat) (different : query ≠ label)
    (source fallback payload : Ty) (bounded : Le source (optional query payload)) :
    Le (recordDefault label source fallback) (optional query payload) := by
  intro value valid
  refine ⟨recordDefault_records label source fallback _ valid, ?_⟩
  exact recordDefault_other label query different source fallback
    (fun found => ∀ item, found = some item → payload item)
    (fun original held => (bounded original held).2) value valid

end Yulang.PresenceDataTypes
