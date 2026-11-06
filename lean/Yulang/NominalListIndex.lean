import Yulang.NominalListViews
import Yulang.ErrorEffects

/-!
# Integer list indices and abortive error effects

The answers to Q9 and Q10 fix the valid interval to `0 ≤ i < length` and
make failure an error effect.  The declaration's spelling and payload remain
a draft, so the effect adapter takes an existing error encoding and a map
from the rejected integer to its payload.  It does not choose an effect key.
No machine integer bound is introduced.
-/

namespace Yulang.NominalListViews

open Directed SignatureRequests ErrorEffects

/-- Conversion to the internal natural index rejects every negative integer. -/
def integerIndex (values : List Value) : Int → Option Value
  | .ofNat position => index values position
  | .negSucc _ => none

def ValidIndex (values : List Value) (position : Int) : Prop :=
  0 ≤ position ∧ position < (values.length : Int)

theorem integerIndex_exact (values : List Value) (position : Int) (value : Value) :
    integerIndex values position = some value ↔
      ∃ natural, position = Int.ofNat natural ∧ At values natural value := by
  cases position with
  | ofNat natural =>
      rw [integerIndex, index_exact]
      constructor
      · exact fun found => ⟨natural, rfl, found⟩
      · rintro ⟨other, same, found⟩
        cases same
        exact found
  | negSucc natural => simp [integerIndex]

theorem integerIndex_some_iff (values : List Value) (position : Int) :
    (∃ value, integerIndex values position = some value) ↔ ValidIndex values position := by
  cases position with
  | ofNat natural =>
      simp only [integerIndex, index, List.getElem?_eq_some_iff]
      change (∃ value, ∃ within : natural < values.length, values[natural] = value) ↔
        0 ≤ (natural : Int) ∧ (natural : Int) < (values.length : Int)
      constructor
      · rintro ⟨_, within, _⟩
        exact ⟨by omega, by exact_mod_cast within⟩
      · intro valid
        have within : natural < values.length := by
          have bound := valid.2
          omega
        exact ⟨values[natural], within, rfl⟩
  | negSucc natural => simp [integerIndex, ValidIndex]

theorem integerIndex_none_iff (values : List Value) (position : Int) :
    integerIndex values position = none ↔ ¬ ValidIndex values position := by
  rw [← integerIndex_some_iff]
  cases integerIndex values position <;> simp

theorem negative_index_invalid (values : List Value) (position : Int) (negative : position < 0) :
    integerIndex values position = none :=
  (integerIndex_none_iff values position).mpr (fun valid => by
    have nonnegative := valid.1
    omega)

theorem integerIndex_cursor (values : List Value) (position : Nat) :
    nextItem (values.drop position) =
      (integerIndex values (Int.ofNat position)).map
        (fun value => (value, values.drop (position + 1))) := cursor_index values position

/-- Failure is an abortive request, not an interpreter error or an optional
source result.  The caller supplies the still-draft declaration encoding. -/
def effectIndex {signature : Signature Key} {cases : Cases signature Error}
    (encoding : Encoding cases) (outOfRange : Int → Error)
    (values : List Value) (position : Int) : Tree n signature Value :=
  match integerIndex values position with
  | some value => .pure value
  | none => raise encoding (outOfRange position)

theorem effectIndex_returns_iff {signature : Signature Key} {cases : Cases signature Error}
    (encoding : Encoding cases) (outOfRange : Int → Error)
    (values : List Value) (position : Int) (value : Value) :
    effectIndex (n := n) encoding outOfRange values position = .pure value ↔
      ∃ natural, position = Int.ofNat natural ∧ At values natural value := by
  rw [← integerIndex_exact]
  cases found : integerIndex values position <;> simp [effectIndex, found, raise]

theorem effectIndex_invalid {signature : Signature Key} {cases : Cases signature Error}
    (encoding : Encoding cases) (outOfRange : Int → Error)
    (values : List Value) (position : Int) (invalid : ¬ ValidIndex values position) :
    effectIndex (n := n) encoding outOfRange values position = raise encoding (outOfRange position) := by
  simp [effectIndex, (integerIndex_none_iff values position).mpr invalid]

theorem effectIndex_bounded {signature : Signature Key} (cases : Cases signature Error)
    (encoding : Encoding cases) (outOfRange : Int → Error)
    (values : List Value) (position : Int) :
    Tree.BoundedBy (cases.keys.map (raw (n := n)))
      (effectIndex encoding outOfRange values position) := by
  cases found : integerIndex values position with
  | none => simpa [effectIndex, found] using raise_bounded cases encoding (outOfRange position)
  | some value => simp [effectIndex, found, Tree.BoundedBy, Tree.AllRequests]

/-- The existing source-error wrapper observes exactly success or the encoded
out-of-range error; failure can never resume into an arbitrary value. -/
theorem wrap_effectIndex [DecidableEq Key] {signature : Signature Key}
    (cases : Cases signature Error) (encoding : Encoding cases) (outOfRange : Int → Error)
    (values : List Value) (position : Int) :
    wrap (n := n) cases (effectIndex encoding outOfRange values position) =
      .pure (match integerIndex values position with
        | some value => .ok value
        | none => .error (outOfRange position)) := by
  cases found : integerIndex values position with
  | none => simp [effectIndex, found]
  | some value => simp [effectIndex, found]

end Yulang.NominalListViews
