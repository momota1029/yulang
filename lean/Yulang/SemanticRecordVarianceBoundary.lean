import Std

/-!
# Local record laws do not force general tail covariance

This is a finite field-presence algebra with three field names. A record
observation assigns one Boolean to each name, and a type is a predicate on
those eight observations. The type order is inclusion. Union and intersection
therefore have their ordinary bounded-lattice laws, and equality is mutual
inclusion.

Proper record types are principal upper sets of required fields. The local
extension operation acts normally on these principal types and returns the
empty type on every other tail. It preserves semantic equality, head/width
bounds, known field presence, first-field-wins, and distinct-field commutation.
Nevertheless it does not preserve the inclusion of a proper tail into a union
of two proper tails.

This is an independence example for the explicitly listed local laws, not a
model of all Yulang types or record values. Field payload types, evaluation,
and the claim that an inhabited input produces an inhabited output are outside
its statement. In particular it establishes no rejection of a source program.
No rule for the intended language is added by this example.
-/

namespace Yulang.SemanticRecordVarianceBoundary

inductive Field where
  | x | y | z
  deriving DecidableEq, Repr

/-- Exactly three independent field-presence bits. -/
abbrev Record := Field → Bool

/-- An explicit finite presentation of the observation carrier. -/
def observation (x y z : Bool) : Record
  | .x => x
  | .y => y
  | .z => z

def observations : List Record :=
  [observation false false false, observation false false true,
    observation false true false, observation false true true,
    observation true false false, observation true false true,
    observation true true false, observation true true true]

theorem observation_eta (record : Record) :
    observation (record .x) (record .y) (record .z) = record := by
  funext field
  cases field <;> rfl

theorem observations_length : observations.length = 8 := rfl

theorem observations_complete (record : Record) : record ∈ observations := by
  rw [← observation_eta record]
  cases record .x <;> cases record .y <;> cases record .z <;> simp [observations]

/-- A type is a subset of the eight possible record observations. -/
abbrev Ty := Record → Prop

def FieldsLe (required actual : Record) : Prop :=
  ∀ field, required field = true → actual field = true

def noFields : Record := fun _ => false

def insert (field : Field) (required : Record) : Record :=
  fun name => if name = field then true else required name

def singleton (field : Field) : Record := insert field noFields

def common (left right : Record) : Record := fun field => left field && right field

def principal (required : Record) : Ty := fun actual => FieldsLe required actual

def bottom : Ty := fun _ => False
def emptyRecord : Ty := fun _ => True
def union (left right : Ty) : Ty := fun actual => left actual ∨ right actual
def inter (left right : Ty) : Ty := fun actual => left actual ∧ right actual

def Le (left right : Ty) : Prop := ∀ actual, left actual → right actual
def Equivalent (left right : Ty) : Prop := Le left right ∧ Le right left

theorem fieldsLe_refl (required : Record) : FieldsLe required required := fun _ present => present

theorem fieldsLe_trans {first middle last : Record} (left : FieldsLe first middle)
    (right : FieldsLe middle last) : FieldsLe first last :=
  fun field present => right field (left field present)

theorem fieldsLe_antisymm {left right : Record} (forward : FieldsLe left right)
    (backward : FieldsLe right left) : left = right := by
  funext field
  cases first : left field <;> cases last : right field
  · rfl
  · have impossible := backward field last
    rw [first] at impossible
    cases impossible
  · have impossible := forward field first
    rw [last] at impossible
    cases impossible
  · rfl

theorem principal_injective {left right : Record} (same : principal left = principal right) :
    left = right := by
  apply fieldsLe_antisymm
  · have present : principal left right := by rw [same]; exact fieldsLe_refl right
    exact present
  · have present : principal right left := by rw [← same]; exact fieldsLe_refl left
    exact present

theorem principal_self (required : Record) : principal required required := fieldsLe_refl required

theorem principal_noFields : principal noFields = emptyRecord := by
  funext actual
  apply propext
  constructor
  · intro _; trivial
  · intro _ field impossible
    cases impossible

theorem principal_singleton (field : Field) (actual : Record) :
    principal (singleton field) actual ↔ actual field = true := by
  constructor
  · intro present
    exact present field (by simp [singleton, insert])
  · intro present name required
    by_cases same : name = field
    · simpa [same] using present
    · simp [singleton, insert, noFields, same] at required

theorem required_le_insert (field : Field) (required : Record) :
    FieldsLe required (insert field required) := by
  intro name present
  by_cases same : name = field <;> simp [insert, same, present]

theorem insert_idempotent (field : Field) (required : Record) :
    insert field (insert field required) = insert field required := by
  funext name
  by_cases same : name = field <;> simp [insert, same]

theorem insert_commutes (first last : Field) (required : Record) :
    insert first (insert last required) = insert last (insert first required) := by
  funext name
  by_cases isFirst : name = first <;> by_cases isLast : name = last <;>
    simp [insert, isFirst, isLast]

theorem principal_common (required left right : Record)
    (first : principal required left) (last : principal required right) :
    principal required (common left right) := by
  intro field present
  simp only [common, Bool.and_eq_true]
  exact ⟨first field present, last field present⟩

theorem le_refl (type : Ty) : Le type type := fun _ present => present

theorem le_trans {left middle right : Ty} (first : Le left middle) (last : Le middle right) :
    Le left right := fun actual present => last actual (first actual present)

theorem le_antisymm {left right : Ty} (first : Le left right) (last : Le right left) : left = right := by
  funext actual
  exact propext ⟨first actual, last actual⟩

theorem equivalent_iff_eq (left right : Ty) : Equivalent left right ↔ left = right := by
  constructor
  · rintro ⟨first, last⟩; exact le_antisymm first last
  · intro same; subst right; exact ⟨le_refl left, le_refl left⟩

theorem bottom_le (type : Ty) : Le bottom type := fun _ impossible => False.elim impossible
theorem le_emptyRecord (type : Ty) : Le type emptyRecord := fun _ _ => trivial

theorem union_is_join (left right target : Ty) :
    Le (union left right) target ↔ Le left target ∧ Le right target := by
  constructor
  · intro upper
    exact ⟨fun actual present => upper actual (.inl present),
      fun actual present => upper actual (.inr present)⟩
  · rintro ⟨first, last⟩ actual present
    exact present.elim (first actual) (last actual)

theorem inter_is_meet (source left right : Ty) :
    Le source (inter left right) ↔ Le source left ∧ Le source right := by
  constructor
  · intro lower
    exact ⟨fun actual present => (lower actual present).1,
      fun actual present => (lower actual present).2⟩
  · rintro ⟨first, last⟩ actual present
    exact ⟨first actual present, last actual present⟩

theorem union_bottom (type : Ty) : union type bottom = type := by
  funext actual
  exact or_false (type actual)

theorem principal_width (more fewer : Record) (included : FieldsLe fewer more) :
    Le (principal more) (principal fewer) :=
  fun _ present => fieldsLe_trans included present

/-! ## An equality-respecting extension with all the listed local laws -/

def IsPrincipal (tail : Ty) : Prop := ∃ required, tail = principal required

/-- The existential is over only eight possible required-field records.
This is a semantic predicate definition, not an inference algorithm. -/
def extend (field : Field) (tail : Ty) : Ty :=
  fun actual => ∃ required, tail = principal required ∧ principal (insert field required) actual

theorem extend_principal (field : Field) (required : Record) :
    extend field (principal required) = principal (insert field required) := by
  funext actual
  apply propext
  constructor
  · rintro ⟨other, same, present⟩
    have equal := principal_injective same
    subst other
    exact present
  · intro present
    exact ⟨required, rfl, present⟩

theorem bottom_not_principal : ¬ IsPrincipal bottom := by
  rintro ⟨required, same⟩
  have impossible : bottom required := by rw [same]; exact principal_self required
  exact impossible

theorem extend_nonprincipal (field : Field) (tail : Ty) (absent : ¬ IsPrincipal tail) :
    extend field tail = bottom := by
  funext actual
  apply propext
  constructor
  · rintro ⟨required, same, _⟩
    exact absent ⟨required, same⟩
  · intro impossible
    exact False.elim impossible

theorem extend_bottom (field : Field) : extend field bottom = bottom :=
  extend_nonprincipal field bottom bottom_not_principal

theorem extend_emptyRecord (field : Field) :
    extend field emptyRecord = principal (singleton field) := by
  rw [← principal_noFields, extend_principal]
  rfl

theorem extend_congruent (field : Field) {left right : Ty} (same : Equivalent left right) :
    extend field left = extend field right :=
  congrArg (extend field) ((equivalent_iff_eq left right).mp same)

/-- Every output has the newly installed field, for every tail. -/
theorem head_available (field : Field) (tail : Ty) :
    Le (extend field tail) (principal (singleton field)) := by
  rintro actual ⟨required, _, present⟩
  apply (principal_singleton field actual).mpr
  exact present field (by simp [insert])

/-- Every output remains below the empty-record type. -/
theorem record_width (field : Field) (tail : Ty) : Le (extend field tail) emptyRecord :=
  le_emptyRecord _

/-- In particular the already-required empty-tail head bound is satisfied. -/
theorem head_width (field : Field) (tail : Ty) :
    Le (extend field tail) (extend field emptyRecord) := by
  rw [extend_emptyRecord]
  exact head_available field tail

/-- All field-presence facts guaranteed by the input are retained. Payload
types are absent from this observation algebra. -/
theorem known_fields_preserved (field : Field) (tail : Ty) (known : Record)
    (guaranteed : Le tail (principal known)) :
    Le (extend field tail) (principal known) := by
  rintro actual ⟨required, same, present⟩
  have original : tail required := by rw [same]; exact principal_self required
  exact fieldsLe_trans (guaranteed required original)
    (fieldsLe_trans (required_le_insert field required) present)

theorem first_field_wins (field : Field) (tail : Ty) :
    extend field (extend field tail) = extend field tail := by
  classical
  by_cases shape : IsPrincipal tail
  · obtain ⟨required, rfl⟩ := shape
    simp only [extend_principal, insert_idempotent]
  · rw [extend_nonprincipal field tail shape, extend_bottom]

theorem extensions_commute (first last : Field) (tail : Ty) :
    extend first (extend last tail) = extend last (extend first tail) := by
  classical
  by_cases shape : IsPrincipal tail
  · obtain ⟨required, rfl⟩ := shape
    simp only [extend_principal]
    exact congrArg principal (insert_commutes first last required)
  · rw [extend_nonprincipal first tail shape, extend_nonprincipal last tail shape,
      extend_bottom, extend_bottom]

theorem distinct_fields_commute (first last : Field) (_different : first ≠ last) (tail : Ty) :
    extend first (extend last tail) = extend last (extend first tail) :=
  extensions_commute first last tail

/-- The exact hypotheses of the independence result below. -/
structure LocalRecordLaws (operation : Field → Ty → Ty) : Prop where
  congruent : ∀ field left right, Equivalent left right → operation field left = operation field right
  proper : ∀ field required, operation field (principal required) = principal (insert field required)
  head : ∀ field tail, Le (operation field tail) (principal (singleton field))
  width : ∀ field tail, Le (operation field tail) emptyRecord
  headWidth : ∀ field tail, Le (operation field tail) (operation field emptyRecord)
  knownFields : ∀ field tail known, Le tail (principal known) →
    Le (operation field tail) (principal known)
  firstWins : ∀ field tail, operation field (operation field tail) = operation field tail
  distinctCommute : ∀ first last, first ≠ last → ∀ tail,
    operation first (operation last tail) = operation last (operation first tail)

theorem local_record_laws : LocalRecordLaws extend where
  congruent := fun field _ _ same => extend_congruent field same
  proper := extend_principal
  head := head_available
  width := record_width
  headWidth := head_width
  knownFields := known_fields_preserved
  firstWins := first_field_wins
  distinctCommute := distinct_fields_commute

/-! ## The concrete proper-tail / union-tail inclusion -/

def leftTail : Ty := principal (singleton .y)
def rightTail : Ty := union leftTail (principal (singleton .z))

theorem leftTail_le_rightTail : Le leftTail rightTail := fun _ present => Or.inl present
theorem rightTail_le_emptyRecord : Le rightTail emptyRecord := le_emptyRecord _

theorem common_y_z : common (singleton .y) (singleton .z) = noFields := by
  funext field
  cases field <;> rfl

theorem noFields_not_rightTail : ¬ rightTail noFields := by
  intro present
  rcases present with fromY | fromZ
  · have impossible := (principal_singleton .y noFields).mp fromY
    cases impossible
  · have impossible := (principal_singleton .z noFields).mp fromZ
    cases impossible

/-- The union has two incomparable minimal field sets; a principal record
type would also contain their common empty field set. -/
theorem rightTail_not_principal : ¬ IsPrincipal rightTail := by
  rintro ⟨required, same⟩
  have fromY : principal required (singleton .y) := by
    rw [← same]
    exact Or.inl (principal_self (singleton .y))
  have fromZ : principal required (singleton .z) := by
    rw [← same]
    exact Or.inr (principal_self (singleton .z))
  have missing := principal_common required _ _ fromY fromZ
  rw [common_y_z, ← same] at missing
  exact noFields_not_rightTail missing

theorem left_extension : extend .x leftTail = principal (insert .x (singleton .y)) :=
  extend_principal .x (singleton .y)

theorem right_extension : extend .x rightTail = bottom :=
  extend_nonprincipal .x rightTail rightTail_not_principal

theorem extended_tails_not_ordered : ¬ Le (extend .x leftTail) (extend .x rightTail) := by
  rw [left_extension, right_extension]
  intro included
  exact included (insert .x (singleton .y)) (principal_self _)

def TailCovariant (operation : Field → Ty → Ty) : Prop :=
  ∀ field left right, Le left right → Le right emptyRecord →
    Le (operation field left) (operation field right)

theorem not_tail_covariant : ¬ TailCovariant extend := by
  intro covariant
  exact extended_tails_not_ordered
    (covariant .x leftTail rightTail leftTail_le_rightTail rightTail_le_emptyRecord)

/-- Semantic equality, all listed record observations, and the empty-tail
width case hold, while general covariance of admissible tails fails. -/
theorem local_laws_without_tail_covariance :
    ∃ operation : Field → Ty → Ty, LocalRecordLaws operation ∧ ¬ TailCovariant operation :=
  ⟨extend, local_record_laws, not_tail_covariant⟩

end Yulang.SemanticRecordVarianceBoundary
