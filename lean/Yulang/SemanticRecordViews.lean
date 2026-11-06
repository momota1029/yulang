import Yulang.SemanticRecordAtoms

/-!
# Semantic views of proper records

A raw record atom has a finite field view when its tail is semantically
equivalent to a proper spine. Views preserve every field type; they do not
distribute record construction across joins or meets. The observations below
show that comparisons of proper records still have exactly the old width and
field obligations, with the new semantic relation on field values.
-/

namespace Yulang.SemanticRecordViews

open StructuralBase (Ty IsRecord)
open SemanticRecords (Subtype Equivalent)
open SemanticRecordAtoms (Atomic Step Chain)

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

abbrev Fields (Row : Type u) := List (Nat × Ty Row)

def spine : Fields Row → Ty Row
  | [] => .emptyRecord
  | (label, value) :: rest => .record label value (spine rest)

theorem spine_record (fields : Fields Row) : IsRecord (spine fields) := by
  induction fields with
  | nil => exact .empty
  | cons field rest ih => exact .field ih

inductive View (leRow : Row → Row → Prop) : Ty Row → Fields Row → Prop where
  | empty : View leRow .emptyRecord []
  | field : Equivalent leRow rest (spine tail) →
      View leRow (.record label value rest) ((label, value) :: tail)

theorem View.atomic {type : Ty Row} {fields : Fields Row}
    (view : View leRow type fields) : Atomic type := by
  cases view <;> trivial

theorem View.equivalent {type : Ty Row} {fields : Fields Row}
    (view : View leRow type fields) : Equivalent leRow type (spine fields) := by
  cases view with
  | empty => exact .refl _
  | field tail => exact SemanticRecords.record_congr _ (.refl _) tail

theorem record_has_view {type : Ty Row} (shape : IsRecord type) :
    ∃ fields, View leRow type fields := by
  induction shape with
  | empty => exact ⟨[], .empty⟩
  | @field rest label value shape ih =>
      obtain ⟨tail, view⟩ := ih
      exact ⟨(label, value) :: tail, .field view.equivalent⟩

theorem Step.view_forward {source target : Ty Row} (step : Step leRow source target)
    (view : ∃ fields, View leRow source fields) : ∃ fields, View leRow target fields := by
  obtain ⟨fields, view⟩ := view
  cases step with
  | pair => cases view
  | variant => cases view
  | arrow => cases view
  | record _ target => exact record_has_view target
  | recordCongr head tail =>
      cases view with
      | field previous => exact ⟨_, .field (tail.symm.trans previous)⟩

theorem Step.view_backward {source target : Ty Row} (step : Step leRow source target)
    (view : ∃ fields, View leRow target fields) : ∃ fields, View leRow source fields := by
  obtain ⟨fields, view⟩ := view
  cases step with
  | pair => cases view
  | variant => cases view
  | arrow => cases view
  | record source => exact record_has_view source
  | recordCongr head tail =>
      cases view with
      | field previous => exact ⟨_, .field (tail.trans previous)⟩

theorem Chain.view_iff {source target : Ty Row} (chain : Chain leRow source target) :
    (∃ fields, View leRow source fields) ↔ ∃ fields, View leRow target fields := by
  induction chain with
  | refl => exact Iff.rfl
  | step one => exact ⟨Step.view_forward one, Step.view_backward one⟩
  | trans _ _ first last => exact first.trans last

theorem View.comparison_exact {source target : Ty Row} {left right : Fields Row}
    (sourceView : View leRow source left) (targetView : View leRow target right) :
    Subtype leRow source target ↔ Subtype leRow (spine left) (spine right) :=
  ⟨fun below => .trans sourceView.equivalent.2 (.trans below targetView.equivalent.1),
    fun below => .trans sourceView.equivalent.1 (.trans below targetView.equivalent.2)⟩

end Yulang.SemanticRecordViews
