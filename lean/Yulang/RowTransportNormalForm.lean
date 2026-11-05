import Yulang.RecursiveRowGraph

/-!
# Transport edges are translations with finitely many excluded inputs

For a fixed operation key, every finite program emitted by the row-graph
compiler has an effective normal form: one integer displacement vector and a
finite list of excluded input occurrences. Every intermediate residual guard
becomes the inverse image of the zero-weight point at its own position.

The normal form is exact for each edge. It does not replace a guarded recursive
path by its net displacement: each successive edge still checks its own finite
exclusion list. Thus it supplies the finite translation/point-guard interface
for a reachability algorithm, without asserting semilinearity or decidability
of its transitive closure.
-/

namespace Yulang.RowTransportNormalForm

open Directed
open RecursiveRowGraph (Action Program)

variable {n : Nat} {Key : Type}

abbrev Weights (n : Nat) := Fin n → Int

def translate (displacement : Weights n) (input : Occurrence n Key) : Occurrence n Key :=
  ⟨input.key, fun coordinate => input.weights coordinate + displacement coordinate⟩

def shiftVector (scope : Fin n) (permission : Permission Key) (amount : Int) (key : Key) : Weights n :=
  fun coordinate => if coordinate = scope ∧ permission key = false then amount else 0

theorem translate_shift (scope : Fin n) (permission : Permission Key) (amount : Int)
    (key : Key) (next : Weights n) (input : Occurrence n Key) (sameKey : input.key = key) :
    translate (fun coordinate => shiftVector scope permission amount key coordinate + next coordinate) input =
      translate next (shift scope permission amount input) := by
  apply Occurrence.ext
  · rfl
  intro coordinate
  by_cases moved : coordinate = scope ∧ permission key = false
  · simp [translate, shiftVector, shift, sameKey, moved]
    omega
  · simp [translate, shiftVector, shift, sameKey, moved]

theorem inverse_shift_mem (scope : Fin n) (permission : Permission Key) (amount : Int)
    (excluded : List (Occurrence n Key)) (input : Occurrence n Key) :
    input ∈ excluded.map (shift scope permission (-amount)) ↔
      shift scope permission amount input ∈ excluded := by
  constructor
  · intro member
    obtain ⟨original, originalMember, equality⟩ := List.mem_map.mp member
    have shifted : shift scope permission amount input = original := by
      rw [← equality, shift_add]
      have cancellation : -amount + amount = 0 := by omega
      rw [cancellation, shift_zero]
    exact shifted ▸ originalMember
  · intro member
    exact List.mem_map.mpr ⟨shift scope permission amount input, member, by
      rw [shift_add]
      have cancellation : amount + -amount = 0 := by omega
      rw [cancellation, shift_zero]⟩

theorem capturable_iff_raw (handled : List Key) (input : Occurrence n Key) :
    Capturable handled input ↔ input.key ∈ handled ∧ input = raw input.key := by
  constructor
  · rintro ⟨key, zero⟩
    exact ⟨key, Occurrence.ext rfl zero⟩
  · rintro ⟨key, equality⟩
    exact ⟨key, fun coordinate => congrFun (congrArg Occurrence.weights equality) coordinate⟩

structure NormalForm (n : Nat) (Key : Type) where
  displacement : Weights n
  excluded : List (Occurrence n Key)

def NormalForm.run [DecidableEq Key] (normal : NormalForm n Key)
    (input : Occurrence n Key) : Option (Occurrence n Key) :=
  if input ∈ normal.excluded then none else some (translate normal.displacement input)

def NormalForm.prependShift (key : Key) (scope : Fin n) (permission : Permission Key)
    (amount : Int) (next : NormalForm n Key) : NormalForm n Key :=
  ⟨fun coordinate => shiftVector scope permission amount key coordinate + next.displacement coordinate,
    next.excluded.map (shift scope permission (-amount))⟩

theorem NormalForm.prependShift_run [DecidableEq Key] (key : Key) (scope : Fin n)
    (permission : Permission Key) (amount : Int) (next : NormalForm n Key)
    (input : Occurrence n Key) (sameKey : input.key = key) :
    (next.prependShift key scope permission amount).run input =
      next.run (shift scope permission amount input) := by
  simp only [NormalForm.prependShift, NormalForm.run, inverse_shift_mem]
  by_cases blocked : shift scope permission amount input ∈ next.excluded
  · simp [blocked]
  · simp only [blocked, ↓reduceIte]
    exact congrArg some (translate_shift scope permission amount key next.displacement input sameKey)

def NormalForm.prependGuard [DecidableEq Key] (key : Key) (handled : List Key)
    (next : NormalForm n Key) : NormalForm n Key :=
  ⟨next.displacement, if key ∈ handled then raw key :: next.excluded else next.excluded⟩

theorem NormalForm.prependGuard_run [DecidableEq Key] (key : Key) (handled : List Key)
    (next : NormalForm n Key) (input : Occurrence n Key) (sameKey : input.key = key) :
    (next.prependGuard key handled).run input =
      ((Action.residual handled).run input).bind next.run := by
  subst key
  by_cases handledKey : input.key ∈ handled
  · by_cases zero : input = raw input.key
    · have capture := (capturable_iff_raw handled input).mpr ⟨handledKey, zero⟩
      have excluded : input ∈ (next.prependGuard input.key handled).excluded := by
        simp only [NormalForm.prependGuard, handledKey, ↓reduceIte]
        exact List.mem_cons.mpr (Or.inl zero)
      rw [NormalForm.run, ite_eq_left excluded, Action.run, ite_eq_left capture]
      rfl
    · have blocked : ¬ Capturable handled input := fun capture =>
        zero ((capturable_iff_raw handled input).mp capture).2
      simp [NormalForm.prependGuard, NormalForm.run, Action.run, handledKey, zero, blocked]
  · have blocked : ¬ Capturable handled input := fun capture => handledKey capture.1
    simp [NormalForm.prependGuard, NormalForm.run, Action.run, handledKey, blocked]

/-- Normalize a program backwards. A translation pulls all later forbidden
points back by its inverse; a guard adds the current zero-weight point. -/
def normalize [DecidableEq Key] (key : Key) : Program n Key → NormalForm n Key
  | [] => ⟨fun _ => 0, []⟩
  | .protect scope permission :: rest =>
      (normalize key rest).prependShift key scope permission 1
  | .release scope permission :: rest =>
      (normalize key rest).prependShift key scope permission (-1)
  | .residual handled :: rest => (normalize key rest).prependGuard key handled

/-- No information about intermediate residuals is lost by normalization. -/
theorem normalize_run [DecidableEq Key] (program : Program n Key) (input : Occurrence n Key) :
    (normalize input.key program).run input = Program.run program input := by
  induction program generalizing input with
  | nil => simp [normalize, NormalForm.run, Program.run, translate]
  | cons action rest ih =>
      cases action with
      | protect scope permission =>
          rw [normalize, NormalForm.prependShift_run _ _ _ _ _ _ rfl]
          exact ih (protect scope permission input)
      | release scope permission =>
          rw [normalize, NormalForm.prependShift_run _ _ _ _ _ _ rfl]
          exact ih (release scope permission input)
      | residual handled =>
          rw [normalize, NormalForm.prependGuard_run _ _ _ _ rfl]
          by_cases capture : Capturable handled input <;>
            simp [Program.run, Action.run, capture, ih]

theorem execution_normal_form [DecidableEq Key] (key : Key) (program : Program n Key)
    (input output : Occurrence n Key) (sameKey : input.key = key) :
    Program.run program input = some output ↔
      input ∉ (normalize key program).excluded ∧
        output = translate (normalize key program).displacement input := by
  rw [← normalize_run, sameKey]
  unfold NormalForm.run
  by_cases blocked : input ∈ (normalize key program).excluded <;> simp [blocked, eq_comm]

/-- Every forbidden occurrence really is a point in the fixed key's integer
weight space. Other keys are not accidentally inserted into the guard list. -/
theorem excluded_keys [DecidableEq Key] (key : Key) (program : Program n Key)
    (input : Occurrence n Key) (member : input ∈ (normalize key program).excluded) : input.key = key := by
  induction program generalizing input with
  | nil => simp [normalize] at member
  | cons action rest ih =>
      cases action with
      | protect scope permission =>
          obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
          exact ih original originalMember
      | release scope permission =>
          obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
          exact ih original originalMember
      | residual handled =>
          by_cases handledKey : key ∈ handled
          · simp only [normalize, NormalForm.prependGuard, handledKey, ↓reduceIte] at member
            cases List.mem_cons.mp member with
            | inl equality => exact equality ▸ rfl
            | inr member => exact ih input member
          · simp only [normalize, NormalForm.prependGuard, handledKey, ↓reduceIte] at member
            exact ih input member

namespace Examples

open RecursiveRowGraph.Examples (scope guardBefore guardAfter)

theorem guard_before_excludes_zero : (normalize 0 guardBefore).excluded = [raw 0] := rfl

theorem guard_after_excludes_negative :
    (normalize 0 guardAfter).excluded = [release scope allowNone (raw 0)] := rfl

def roundtripGuard : Program 1 Nat :=
  [.protect scope allowNone, .residual [0], .release scope allowNone]

/-- A net displacement of zero does not justify erasing a residual inside it. -/
theorem roundtrip_displacement_zero : (normalize 0 roundtripGuard).displacement = fun _ => 0 := by
  funext coordinate
  have same : coordinate = scope := by
    apply Fin.ext
    have bound := coordinate.isLt
    change coordinate.val = 0
    omega
  subst coordinate
  simp [normalize, roundtripGuard, NormalForm.prependShift, NormalForm.prependGuard,
    shiftVector, allowNone]

theorem roundtrip_keeps_raw : Program.run roundtripGuard (raw 0) = some (raw 0) := by decide

theorem roundtrip_rejects_debt :
    Program.run roundtripGuard (release scope allowNone (raw 0)) = none := by decide

end Examples

end Yulang.RowTransportNormalForm
