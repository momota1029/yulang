import Yulang.RigidSemanticRecords

/-!
# Visible fields of rigid-target semantic records

The observation functions are sound for the decision-39 relation. Proper
records still compare exactly by visible field coverage and field subtyping.
The first occurrence of a label wins; later occurrences are not compared.

Erasure below removes a specified label from a rigid demanded spine. Only
facts derivable from the declarative rules are proved: no extra covariance,
record distribution or arbitrary-tail masking equation is assumed.
-/

namespace Yulang.RigidRecordFields

open StructuralBase (Ty IsRecord)
open RigidSemanticRecords (Subtype Equivalent)

universe u

variable {Row : Type u} {leRow : Row → Row → Prop}

def missing (label : Nat) : Ty Row → Prop
  | .bottom => False
  | .top => True
  | .union a b => missing label a ∨ missing label b
  | .inter a b => missing label a ∧ missing label b
  | .record name _ rest => label ≠ name ∧ missing label rest
  | _ => True

theorem missing_record {type : Ty Row} (shape : IsRecord type) (label : Nat) :
    missing label type ↔ type.lookup label = none := by
  induction shape with
  | empty => simp [missing, Ty.lookup]
  | @field rest name value shape ih =>
      by_cases same : label = name <;> simp [missing, Ty.lookup, same, ih]

theorem missing_mono {a b : Ty Row} (subtype : Subtype leRow a b) (label : Nat) :
    missing label a → missing label b := by
  induction subtype with
  | refl => exact id
  | trans _ _ first last => exact fun h => last (first h)
  | bottom => exact False.elim
  | top => exact fun _ => trivial
  | unionLeft => exact Or.inl
  | unionRight => exact Or.inr
  | unionElim _ _ first last => exact fun h => h.elim first last
  | interLeft => exact And.left
  | interRight => exact And.right
  | interIntro _ _ first last => exact fun h => ⟨first h, last h⟩
  | pair => exact id
  | variant => exact id
  | arrow => exact id
  | @record source target sourceShape targetShape fields values _ =>
      intro absent
      apply (missing_record targetShape label).mpr
      cases found : target.lookup label with
      | none => rfl
      | some value =>
          obtain ⟨actual, actualFound⟩ := fields label value found
          have impossible := (missing_record sourceShape label).mp absent
          rw [actualFound] at impossible
          cases impossible
  | @recordCongr value value' rest rest' name _ _ _ _ _ _ tail _ =>
      exact fun h => ⟨h.1, tail h.2⟩
  | recordTail _ _ tail => exact fun h => ⟨h.1, tail h.2⟩

def fieldType (label : Nat) : Ty Row → Ty Row
  | .bottom => .bottom
  | .top => .top
  | .union a b => .union (fieldType label a) (fieldType label b)
  | .inter a b => .inter (fieldType label a) (fieldType label b)
  | .record name value rest => if label = name then value else fieldType label rest
  | _ => .top

theorem fieldType_record {type : Ty Row} (shape : IsRecord type) (label : Nat) :
    fieldType label type = (type.lookup label).getD .top := by
  induction shape with
  | empty => rfl
  | @field rest name value shape ih =>
      by_cases same : label = name <;> simp [fieldType, Ty.lookup, same, ih]

theorem fieldType_mono {a b : Ty Row} (subtype : Subtype leRow a b) (label : Nat) :
    Subtype leRow (fieldType label a) (fieldType label b) := by
  induction subtype with
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
  | pair => exact .refl _
  | variant => exact .refl _
  | arrow => exact .refl _
  | @record source target sourceShape targetShape fields values _ =>
      rw [fieldType_record sourceShape, fieldType_record targetShape]
      cases targetFound : target.lookup label with
      | none => exact .top _
      | some expected =>
          obtain ⟨actual, actualFound⟩ := fields label expected targetFound
          simpa [targetFound, actualFound] using values label actual expected actualFound targetFound
  | @recordCongr value value' rest rest' name head _ _ _ _ _ tail _ =>
      by_cases same : label = name
      · simpa [fieldType, same] using head
      · simpa [fieldType, same] using tail
  | @recordTail rest' rest name value _ _ tail =>
      by_cases same : label = name
      · simp only [fieldType, same, ↓reduceIte]
        exact .refl _
      · simpa [fieldType, same] using tail

theorem proper_fields {source target : Ty Row}
    (sourceShape : IsRecord source) (targetShape : IsRecord target)
    (subtype : Subtype leRow source target) :
    (∀ label expected, target.lookup label = some expected →
      ∃ actual, source.lookup label = some actual) ∧
    (∀ label actual expected, source.lookup label = some actual →
      target.lookup label = some expected → Subtype leRow actual expected) := by
  constructor
  · intro label expected found
    cases actualFound : source.lookup label with
    | some actual => exact ⟨actual, rfl⟩
    | none =>
        have absent := missing_mono subtype label ((missing_record sourceShape label).mpr actualFound)
        have impossible := (missing_record targetShape label).mp absent
        rw [found] at impossible
        cases impossible
  · intro label actual expected actualFound expectedFound
    have below := fieldType_mono subtype label
    simpa [fieldType_record sourceShape, fieldType_record targetShape, actualFound, expectedFound] using below

theorem proper_record_exact {source target : Ty Row}
    (sourceShape : IsRecord source) (targetShape : IsRecord target) :
    Subtype leRow source target ↔
    (∀ label expected, target.lookup label = some expected →
      ∃ actual, source.lookup label = some actual) ∧
    (∀ label actual expected, source.lookup label = some actual →
      target.lookup label = some expected → Subtype leRow actual expected) :=
  ⟨proper_fields sourceShape targetShape, fun h => .record sourceShape targetShape h.1 h.2⟩

/-- Remove every hidden occurrence of a label from a demanded spine.
This function is only used with a proper-spine premise in the comparison laws. -/
def erase (label : Nat) : Ty Row → Ty Row
  | .record name value rest =>
      if label = name then erase label rest else .record name value (erase label rest)
  | type => type

theorem erase_record (label : Nat) {type : Ty Row} (shape : IsRecord type) :
    IsRecord (erase label type) := by
  induction shape with
  | empty => exact .empty
  | @field rest name value _ ih =>
      by_cases same : label = name
      · simpa [erase, same] using ih
      · simpa [erase, same] using IsRecord.field (label := name) (value := value) ih

@[simp] theorem lookup_erase (label key : Nat) (type : Ty Row) :
    (erase label type).lookup key = if key = label then none else type.lookup key := by
  induction type with
  | record name value rest _ ih =>
      by_cases drop : label = name
      · subst name
        by_cases same : key = label
        · subst key
          simpa [erase] using ih
        · simp [erase, Ty.lookup, same, ih]
      · by_cases same : key = label
        · subst key
          simp [erase, drop, ih]
        · simp [erase, Ty.lookup, drop, same, ih]
  | _ => simp [erase, Ty.lookup]

/-- Forgetting fields of a proper spine is an ordinary width comparison. -/
theorem erase_subtype (label : Nat) {type : Ty Row} (shape : IsRecord type) :
    Subtype leRow type (erase label type) := by
  apply Subtype.record shape (erase_record label shape)
  · intro key expected found
    by_cases same : key = label
    · simp [lookup_erase, same] at found
    · exact ⟨expected, by simpa [lookup_erase, same] using found⟩
  · intro key actual expected actualFound expectedFound
    by_cases same : key = label
    · simp [lookup_erase, same] at expectedFound
    · have equal : actual = expected := by
        simpa [lookup_erase, same, actualFound] using expectedFound
      subst expected
      exact .refl _

/-- Raw differences in hidden fields cannot affect proper record equality. -/
theorem proper_equivalent_of_lookup_eq {source target : Ty Row}
    (sourceShape : IsRecord source) (targetShape : IsRecord target)
    (lookups : ∀ label, source.lookup label = target.lookup label) :
    Equivalent leRow source target := by
  have below : ∀ {a b : Ty Row}, IsRecord a → IsRecord b →
      (∀ label, a.lookup label = b.lookup label) → Subtype leRow a b := by
    intro a b aShape bShape same
    apply Subtype.record aShape bShape
    · intro label expected found
      exact ⟨expected, (same label).trans found⟩
    · intro label actual expected actualFound expectedFound
      have equal : actual = expected := by
        simpa [actualFound, expectedFound] using same label
      subst expected
      exact .refl _
  exact ⟨below sourceShape targetShape lookups,
    below targetShape sourceShape (fun label => (lookups label).symm)⟩

/-- Once the head is fixed, every same-labelled field of a rigid tail is
hidden, independently of its payload type. -/
theorem record_erase_equivalent (label : Nat) (value : Ty Row) {rest : Ty Row}
    (shape : IsRecord rest) :
    Equivalent leRow (.record label value rest) (.record label value (erase label rest)) := by
  apply proper_equivalent_of_lookup_eq (.field shape) (.field (erase_record label shape))
  intro key
  by_cases same : key = label <;> simp [Ty.lookup, same]

/-- A sufficient comparison to a rigid demanded record checks only its
visible, non-shadowed fields in the supplied tail. It never compares a
hidden tail field against the new head's demanded payload. -/
theorem record_mask_sufficient (label : Nat) (value : Ty Row) {rest target : Ty Row}
    (rigid : IsRecord target) (tail : Subtype leRow rest (erase label target))
    (head : ∀ expected, target.lookup label = some expected → Subtype leRow value expected) :
    Subtype leRow (.record label value rest) target := by
  refine .trans (.recordTail (erase_record label rigid) tail) ?_
  apply Subtype.record (.field (erase_record label rigid)) rigid
  · intro key expected found
    by_cases same : key = label
    · exact ⟨value, by simp [Ty.lookup, same]⟩
    · exact ⟨expected, by simpa [Ty.lookup, same] using found⟩
  · intro key actual expected actualFound expectedFound
    by_cases same : key = label
    · subst key
      have equal : value = actual := by simpa [Ty.lookup] using actualFound
      subst actual
      exact head expected expectedFound
    · have equal : actual = expected := by
        have found : target.lookup key = some actual := by simpa [Ty.lookup, same] using actualFound
        simpa [expectedFound] using found.symm
      subst expected
      exact .refl _

end Yulang.RigidRecordFields
