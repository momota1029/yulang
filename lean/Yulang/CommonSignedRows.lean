import Yulang.Common
import Yulang.SignedStructural

/-!
# Signed finite rows inside the arbitrary Common row carrier

The scope interface is fixed by the declaration environment. Encoding retains
exactly its `n` integer coordinates, including trailing zeros. A finite row is
embedded as a set; arbitrary Common row parameters need not have a finite
representation or a uniform coordinate length.
-/

namespace Yulang.CommonSignedRows

def encodeOccurrence (occurrence : Directed.Occurrence n Nat) : Common.Occurrence :=
  (occurrence.key, List.ofFn occurrence.weights)

theorem encodeOccurrence_injective {first last : Directed.Occurrence n Nat}
    (same : encodeOccurrence first = encodeOccurrence last) : first = last := by
  apply Directed.Occurrence.ext
  · exact congrArg Prod.fst same
  intro coordinate
  have weights := congrArg Prod.snd same
  have entry := congrArg (fun xs : List Int => xs[coordinate.val]?) weights
  simpa [encodeOccurrence, List.getElem?_ofFn, coordinate.isLt] using entry

def embedRow (row : Directed.Row n Nat) : Common.Row :=
  fun occurrence => ∃ source ∈ row, encodeOccurrence source = occurrence

@[simp] theorem embedRow_encode (row : Directed.Row n Nat)
    (occurrence : Directed.Occurrence n Nat) :
    embedRow row (encodeOccurrence occurrence) ↔ occurrence ∈ row := by
  constructor
  · rintro ⟨source, member, same⟩
    exact encodeOccurrence_injective same ▸ member
  · intro member
    exact ⟨occurrence, member, rfl⟩

theorem embedRow_le_iff (first last : Directed.Row n Nat) :
    SignedStructural.RowLe first last ↔ Common.rowLe (embedRow first) (embedRow last) := by
  constructor
  · intro below occurrence member
    obtain ⟨source, present, rfl⟩ := member
    exact ⟨source, below source present, rfl⟩
  · intro below occurrence present
    exact (embedRow_encode last occurrence).mp
      (below (encodeOccurrence occurrence) ((embedRow_encode first occurrence).mpr present))

@[simp] theorem embedRow_empty : embedRow ([] : Directed.Row n Nat) = Common.rowEmpty := by
  funext occurrence
  apply propext
  simp [embedRow, Common.rowEmpty]

theorem embedRow_join (first last : Directed.Row n Nat) :
    embedRow (first ++ last) = Common.rowJoin (embedRow first) (embedRow last) := by
  funext occurrence
  apply propext
  simp only [embedRow, List.mem_append, Common.rowJoin]
  constructor
  · rintro ⟨source, present, same⟩
    exact present.elim (fun h => Or.inl ⟨source, h, same⟩)
      (fun h => Or.inr ⟨source, h, same⟩)
  · rintro (⟨source, present, same⟩ | ⟨source, present, same⟩)
    · exact ⟨source, Or.inl present, same⟩
    · exact ⟨source, Or.inr present, same⟩

theorem embedRow_coordinate_length (row : Directed.Row n Nat)
    (occurrence : Common.Occurrence) (member : embedRow row occurrence) :
    occurrence.2.length = n := by
  obtain ⟨source, _, rfl⟩ := member
  exact List.length_ofFn

end Yulang.CommonSignedRows
