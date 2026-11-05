import Yulang.InfiniteOperationalTransport

/-!
# Boundary transport preserves and reflects structural constraints

`InfiniteOperationalTransport.type` maps every row in the existing structural
type algebra by the runtime request bijection. This module proves that it is an
automorphism of the existing `StructuralBase.Subtype Included` relation. The
proof covers the whole inductive preorder, including transitivity, unions,
intersections, record width with first-field-wins lookup, variants, and both
contravariant input and covariant output rows of arrows.

Rows are arbitrary occurrence predicates, with no finite-support restriction.
The relation is not replaced by runtime interpretation or checker success:
records and variants are covered even though the resolved operational fragment
does not provide runtime values for those constructors. The resulting exact
constraint equivalence does not itself solve unknown type bounds or establish
source elaboration.
-/

namespace Yulang.OperationalTransportSubtyping

open Directed
open StructuralBase (Ty IsRecord Subtype)
open InfiniteRowHygiene (Included)
open InfiniteOperationalCorrespondence (CoreType CoreComp Model)
open OperationalTransport (Direction)
open InfiniteOperationalTransport (type comp row row_included_iff type_opposite)

/-- Lookup keeps the same first field; a hidden duplicate stays hidden. -/
@[simp] theorem type_lookup (scope : Fin n) (permission : Permission Key)
    (direction : Direction) (label : Nat) (original : CoreType n Key) :
    (type scope permission direction original).lookup label =
      (original.lookup label).map (type scope permission direction) := by
  induction original <;> simp_all [type, Ty.lookup]
  split <;> simp_all

theorem isRecord_preserved (scope : Fin n) (permission : Permission Key)
    (direction : Direction) {original : CoreType n Key} (shape : IsRecord original) :
    IsRecord (type scope permission direction original) := by
  induction shape with
  | empty => exact .empty
  | field _ ih => exact .field ih

@[simp] theorem isRecord_iff (scope : Fin n) (permission : Permission Key)
    (direction : Direction) (original : CoreType n Key) :
    IsRecord (type scope permission direction original) ↔ IsRecord original := by
  constructor
  · intro shape
    have restored := isRecord_preserved scope permission direction.opposite shape
    simpa only [type_opposite] using restored
  · exact isRecord_preserved scope permission direction

/-- Every rule of the existing structural relation is carried to the same
rule, with record lookup evidence and row inclusions transported explicitly. -/
theorem subtype_preserved (scope : Fin n) (permission : Permission Key)
    (direction : Direction) {left right : CoreType n Key}
    (subtype : Subtype Included left right) :
    Subtype Included (type scope permission direction left)
      (type scope permission direction right) := by
  induction subtype with
  | refl => exact .refl _
  | trans _ _ ihl ihr => exact .trans ihl ihr
  | bottom => exact .bottom _
  | unionLeft => exact .unionLeft _ _
  | unionRight => exact .unionRight _ _
  | unionElim _ _ ihl ihr => exact .unionElim ihl ihr
  | interLeft => exact .interLeft _ _
  | interRight => exact .interRight _ _
  | interIntro _ _ ihl ihr => exact .interIntro ihl ihr
  | pair _ _ ihl ihr => exact .pair ihl ihr
  | variant _ ih => exact .variant ih
  | arrow _ inputRow _ outputRow ihi iho =>
      exact .arrow ihi ((row_included_iff scope permission direction _ _).mpr inputRow)
        iho ((row_included_iff scope permission direction _ _).mpr outputRow)
  | record sourceShape targetShape fields _ ih =>
      apply Subtype.record (isRecord_preserved scope permission direction sourceShape)
        (isRecord_preserved scope permission direction targetShape)
      · intro label mappedValue lookedUp
        rw [type_lookup] at lookedUp
        obtain ⟨original, lookup, _⟩ := Option.map_eq_some_iff.mp lookedUp
        obtain ⟨actual, present⟩ := fields label original lookup
        exact ⟨type scope permission direction actual, by simp only [type_lookup, present, Option.map_some]⟩
      · intro label actual expected actualLookup expectedLookup
        rw [type_lookup] at actualLookup expectedLookup
        obtain ⟨originalActual, actualPresent, rfl⟩ := Option.map_eq_some_iff.mp actualLookup
        obtain ⟨originalExpected, expectedPresent, rfl⟩ := Option.map_eq_some_iff.mp expectedLookup
        exact ih label originalActual originalExpected actualPresent expectedPresent

/-- Reflection uses the matching inverse boundary action, so no subtype fact
can be created merely by wrapping its effect rows. -/
theorem subtype_iff (scope : Fin n) (permission : Permission Key)
    (direction : Direction) (left right : CoreType n Key) :
    Subtype Included (type scope permission direction left)
      (type scope permission direction right) ↔ Subtype Included left right := by
  constructor
  · intro subtype
    have restored := subtype_preserved scope permission direction.opposite subtype
    simpa only [type_opposite] using restored
  · exact subtype_preserved scope permission direction

/-- This is the computation-subtype relation used by the existing infinite-row
inference model, not a separately defined approximation. -/
theorem comp_subtype_iff (scope : Fin n) (permission : Permission Key)
    (direction : Direction) (left right : CoreComp n Key) :
    Inference.Comp.le (Model n Key) (comp scope permission direction left)
      (comp scope permission direction right) ↔ Inference.Comp.le (Model n Key) left right := by
  change (Subtype Included (type scope permission direction left.1)
      (type scope permission direction right.1) ∧
      Included (row scope permission direction left.2) (row scope permission direction right.2)) ↔
    (Subtype Included left.1 right.1 ∧ Included left.2 right.2)
  exact and_congr (subtype_iff scope permission direction left.1 right.1)
    (row_included_iff scope permission direction left.2 right.2)

end Yulang.OperationalTransportSubtyping
