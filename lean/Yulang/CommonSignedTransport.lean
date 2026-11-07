import Yulang.CommonSignedRows

/-!
# Total signed transport on arbitrary Common rows

Coordinates already present in an occurrence are shifted; an absent coordinate
is left absent. No zero padding, scope quotient, finite-row premise or restriction
on free row parameters is used. On the length-`n` declaration interface these
operations agree with the existing `Directed` operations.
-/

namespace Yulang.CommonSignedRows

def shiftOccurrence (scope : Nat) (permission : Nat → Bool) (delta : Int)
    (occurrence : Common.Occurrence) : Common.Occurrence :=
  (occurrence.1, occurrence.2.mapIdx fun coordinate weight =>
    if coordinate = scope ∧ permission occurrence.1 = false then weight + delta else weight)

@[simp] theorem shiftOccurrence_key (scope : Nat) (permission : Nat → Bool)
    (delta : Int) (occurrence : Common.Occurrence) :
    (shiftOccurrence scope permission delta occurrence).1 = occurrence.1 := rfl

@[simp] theorem shiftOccurrence_length (scope : Nat) (permission : Nat → Bool)
    (delta : Int) (occurrence : Common.Occurrence) :
    (shiftOccurrence scope permission delta occurrence).2.length = occurrence.2.length := by
  simp [shiftOccurrence]

@[simp] theorem shiftOccurrence_zero (scope : Nat) (permission : Nat → Bool)
    (occurrence : Common.Occurrence) : shiftOccurrence scope permission 0 occurrence = occurrence := by
  apply Prod.ext
  · rfl
  apply List.ext_getElem
  · simp [shiftOccurrence]
  · intro i hi hj
    simp [shiftOccurrence]

theorem shiftOccurrence_add (scope : Nat) (permission : Nat → Bool)
    (first last : Int) (occurrence : Common.Occurrence) :
    shiftOccurrence scope permission last (shiftOccurrence scope permission first occurrence) =
      shiftOccurrence scope permission (first + last) occurrence := by
  apply Prod.ext
  · rfl
  apply List.ext_getElem
  · simp [shiftOccurrence]
  · intro i hi hj
    simp only [shiftOccurrence, List.getElem_mapIdx]
    split <;> rename_i h
    · simp [h, Int.add_assoc]
    · simp

@[simp] theorem shiftOccurrence_inverse (scope : Nat) (permission : Nat → Bool)
    (delta : Int) (occurrence : Common.Occurrence) :
    shiftOccurrence scope permission (-delta) (shiftOccurrence scope permission delta occurrence) =
      occurrence := by
  have cancel : delta + -delta = 0 := by omega
  rw [shiftOccurrence_add, cancel, shiftOccurrence_zero]

theorem encode_shift (scope : Fin n) (permission : Nat → Bool) (delta : Int)
    (occurrence : Directed.Occurrence n Nat) :
    encodeOccurrence (Directed.shift scope permission delta occurrence) =
      shiftOccurrence scope.val permission delta (encodeOccurrence occurrence) := by
  apply Prod.ext
  · rfl
  apply List.ext_getElem
  · simp [encodeOccurrence, shiftOccurrence]
  · intro i hi hj
    simp only [encodeOccurrence, shiftOccurrence, List.getElem_ofFn, List.getElem_mapIdx]
    simp [Directed.shift, Fin.ext_iff]

/-- Pulling membership back through the inverse is the exact image of a row. -/
def transport (scope : Nat) (permission : Nat → Bool) (delta : Int)
    (row : Common.Row) : Common.Row :=
  fun occurrence => row (shiftOccurrence scope permission (-delta) occurrence)

theorem transport_member_iff (scope : Nat) (permission : Nat → Bool) (delta : Int)
    (row : Common.Row) (occurrence : Common.Occurrence) :
    transport scope permission delta row occurrence ↔
      ∃ source, row source ∧ shiftOccurrence scope permission delta source = occurrence := by
  constructor
  · intro present
    refine ⟨shiftOccurrence scope permission (-delta) occurrence, present, ?_⟩
    simpa using shiftOccurrence_inverse scope permission (-delta) occurrence
  · rintro ⟨source, present, rfl⟩
    simpa [transport] using present

theorem transport_inverse (scope : Nat) (permission : Nat → Bool) (delta : Int)
    (row : Common.Row) :
    transport scope permission (-delta) (transport scope permission delta row) = row := by
  funext occurrence
  simp [transport]

def commonProtect (scope : Nat) (permission : Nat → Bool) : Common.Row → Common.Row :=
  transport scope permission 1

def commonRelease (scope : Nat) (permission : Nat → Bool) : Common.Row → Common.Row :=
  transport scope permission (-1)

theorem commonRelease_protect (scope : Nat) (permission : Nat → Bool) (row : Common.Row) :
    commonRelease scope permission (commonProtect scope permission row) = row :=
  transport_inverse scope permission 1 row

theorem commonProtect_release (scope : Nat) (permission : Nat → Bool) (row : Common.Row) :
    commonProtect scope permission (commonRelease scope permission row) = row := by
  simpa [commonProtect, commonRelease] using transport_inverse scope permission (-1) row

theorem embedRow_transport (scope : Fin n) (permission : Nat → Bool) (delta : Int)
    (row : Directed.Row n Nat) :
    embedRow (row.map (Directed.shift scope permission delta)) =
      transport scope.val permission delta (embedRow row) := by
  funext occurrence
  apply propext
  rw [transport_member_iff]
  constructor
  · rintro ⟨shifted, member, rfl⟩
    obtain ⟨source, present, rfl⟩ := List.mem_map.mp member
    exact ⟨encodeOccurrence source, ⟨source, present, rfl⟩, (encode_shift _ _ _ _).symm⟩
  · rintro ⟨encoded, ⟨source, present, rfl⟩, rfl⟩
    exact ⟨Directed.shift scope permission delta source,
      List.mem_map.mpr ⟨source, present, rfl⟩, encode_shift _ _ _ _⟩

theorem embedRow_protect (scope : Fin n) (permission : Nat → Bool) (row : Directed.Row n Nat) :
    embedRow (row.map (Directed.protect scope permission)) =
      commonProtect scope.val permission (embedRow row) :=
  embedRow_transport scope permission 1 row

theorem embedRow_release (scope : Fin n) (permission : Nat → Bool) (row : Directed.Row n Nat) :
    embedRow (row.map (Directed.release scope permission)) =
      commonRelease scope.val permission (embedRow row) :=
  embedRow_transport scope permission (-1) row

end Yulang.CommonSignedRows
