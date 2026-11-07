import Yulang.CommonPurePatternMatching

/-! Finite extraction of every default-free actual source pattern. Erasure
retains all constructors, binding names/order and literal contents; an
executable default makes extraction fail rather than being evaluated. -/

namespace Yulang.CommonPurePatternErasure

open CasePatterns (Pattern)
open CaseValues (Value Bindings)
open EvaluationTrace (Logged)

def both (construct : A → B → C) (first : Option A) (last : Option B) : Option C :=
  match first, last with
  | some left, some right => some (construct left right)
  | _, _ => none

theorem both_some (construct : A → B → C) (first : Option A) (last : Option B) (result : C) :
    both construct first last = some result ↔ ∃ left right,
      first = some left ∧ last = some right ∧ construct left right = result := by
  cases first <;> cases last <;> simp [both]

theorem mapped_some (map : A → B) (first : Option A) (result : B) :
    first.map map = some result ↔ ∃ value, first = some value ∧ map value = result := by
  cases first <;> simp

def erase : Pattern F D → Option (Pattern F Empty)
  | .wildcard => some .wildcard
  | .bind name => some (.bind name)
  | .literal value => some (.literal value)
  | .intRange lower upper => some (.intRange lower upper)
  | .pair p q => both Pattern.pair (erase p) (erase q)
  | .recordEnd => some .recordEnd
  | .field name p rest => both (Pattern.field name) (erase p) (erase rest)
  | .defaultField _ _ _ _ => none
  | .nil => some .nil
  | .cons p rest => both Pattern.cons (erase p) (erase rest)
  | .snoc initial p => both Pattern.snoc (erase initial) (erase p)
  | .variant tag p => (erase p).map (.variant tag)
  | .nominal typeId ctorId p => (erase p).map (.nominal typeId ctorId)
  | .or p q => both Pattern.or (erase p) (erase q)
  | .as p name => (erase p).map (fun child => .as child name)

theorem erase_embed (pattern : Pattern F Empty) : erase (Core.Patterns.map (Empty.elim : Empty → D) pattern) = some pattern := by
  induction pattern with
  | defaultField name impossible p rest ihp ihr => exact impossible.elim
  | _ => simp_all [erase, Core.Patterns.map, both]

theorem reflected (pattern : Pattern F D) (pure : Pattern F Empty) (compiled : erase pattern = some pure) :
    Core.Patterns.map Empty.elim pure = pattern := by
  induction pattern generalizing pure with
  | wildcard | bind | literal | intRange | recordEnd | nil =>
      cases compiled
      rfl
  | defaultField => cases compiled
  | pair p q ihp ihq =>
      obtain ⟨left, right, first, last, rfl⟩ := (both_some _ _ _ _).mp compiled
      simp only [Core.Patterns.map, ihp _ first, ihq _ last]
  | field name p rest ihp ihr =>
      obtain ⟨left, right, first, last, rfl⟩ := (both_some _ _ _ _).mp compiled
      simp only [Core.Patterns.map, ihp _ first, ihr _ last]
  | cons p rest ihp ihr =>
      obtain ⟨left, right, first, last, rfl⟩ := (both_some _ _ _ _).mp compiled
      simp only [Core.Patterns.map, ihp _ first, ihr _ last]
  | snoc initial p ihi ihp =>
      obtain ⟨left, right, first, last, rfl⟩ := (both_some _ _ _ _).mp compiled
      simp only [Core.Patterns.map, ihi _ first, ihp _ last]
  | or p q ihp ihq =>
      obtain ⟨left, right, first, last, rfl⟩ := (both_some _ _ _ _).mp compiled
      simp only [Core.Patterns.map, ihp _ first, ihq _ last]
  | variant tag p ih =>
      obtain ⟨child, first, rfl⟩ := (mapped_some _ _ _).mp compiled
      simp only [Core.Patterns.map, ih _ first]
  | nominal typeId ctorId p ih =>
      obtain ⟨child, first, rfl⟩ := (mapped_some _ _ _).mp compiled
      simp only [Core.Patterns.map, ih _ first]
  | as p name ih =>
      obtain ⟨child, first, rfl⟩ := (mapped_some _ _ _).mp compiled
      simp only [Core.Patterns.map, ih _ first]

/-- Exact extraction for an arbitrarily prescribed pure result, rather than
an unspecified equivalent pattern. No source pattern is replaced or weakened. -/
theorem erase_exact (pattern : Pattern F D) (pure : Pattern F Empty) :
    erase pattern = some pure ↔ Core.Patterns.map Empty.elim pure = pattern := by
  constructor
  · exact reflected pattern pure
  · intro same
    rw [← same]
    exact erase_embed pure

theorem actual_match_exact (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F)) (environment : Bindings F)
    (pattern : Pattern F D) (pure : Pattern F Empty) (compiled : erase pattern = some pure) (value : Value F) :
    ScopedCasePatterns.run floatCheck defaultEval environment pattern value =
      Logged.ofResult (.ok (CommonPurePatternMatching.bindings floatCheck pure value)) := by
  rw [← reflected pattern pure compiled]
  exact CommonPurePatternMatching.run_embed_exact floatCheck defaultEval environment pure value

end Yulang.CommonPurePatternErasure
