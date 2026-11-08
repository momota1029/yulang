import Yulang.CommonEffectMixedKinds
import Yulang.CommonEffectFamilyRowSlots

/-!
Finite allocation for resolved invariant effect-family argument occurrences.
The input retains each original occurrence ID and its row/family/argument
position. Only occurrences at the exact same position and of the same kind
share a fresh slot. Value and row slots have separate finite namespaces.

This module allocates the slots itself: no source-to-slot callback is an
input. Family lookup, source name resolution and the discovery of invariant
positions are separate from allocation. In particular this does not impose
invariance on covariant nominal arguments.
-/
namespace Yulang.CommonEffectMixedFamilyAllocation
open CommonEffectRequestGeneration (Computation)
open CommonEffectInvariantIntervals (ValueTerms)
open CommonEffectRowIntervalConstraints (Bounds)
open CommonEffectKindedFormula (Locals)
export CommonEffectMixedKinds (Kind)
export CommonEffectFamilyRowSlots (Slot)

inductive Argument (scopes : Nat) (α : Type) where
  | value : ValueTerms α → Argument scopes α
  | row : Bounds scopes α → Argument scopes α

def Argument.kind : Argument scopes α → Kind
  | .value _ => .value
  | .row _ => .row

structure Occurrence (scopes : Nat) (α : Type) where
  slot : Slot
  origin : Nat
  argument : Argument scopes α

/-- The first occurrence determines only the fresh index. All occurrences
remain in the original input and later contribute their endpoint checks. -/
def slots (kind : Kind) (occurrences : List (Occurrence scopes α)) : List Slot :=
  ((occurrences.filter (fun occurrence => occurrence.argument.kind == kind)).map (·.slot)).eraseDups

theorem mem_slots (kind : Kind) (occurrences : List (Occurrence scopes α)) (slot : Slot) :
    slot ∈ slots kind occurrences ↔
      ∃ occurrence ∈ occurrences, occurrence.argument.kind = kind ∧ occurrence.slot = slot := by
  simp only [slots, List.mem_eraseDups, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨occurrence, ⟨included, kinded⟩, same⟩
    exact ⟨occurrence, included, kinded, same⟩
  · rintro ⟨occurrence, included, kinded, same⟩
    exact ⟨occurrence, ⟨included, kinded⟩, same⟩

theorem occurrence_slot (occurrences : List (Occurrence scopes α))
    (occurrence : Occurrence scopes α) (included : occurrence ∈ occurrences) :
    occurrence.slot ∈ slots occurrence.argument.kind occurrences :=
  (mem_slots _ _ _).mpr ⟨occurrence, included, rfl, rfl⟩

private theorem dedup_nodup (pool : List Slot) : pool.eraseDups.Nodup := by
  cases pool with
  | nil => exact List.nodup_nil
  | cons first rest =>
    rw [List.eraseDups_cons]
    apply List.nodup_cons.mpr
    exact ⟨by simp, dedup_nodup (rest.filter (fun slot => !slot == first))⟩
termination_by pool.length
decreasing_by exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem slots_nodup (kind : Kind) (occurrences : List (Occurrence scopes α)) :
    (slots kind occurrences).Nodup := dedup_nodup _

def reference (pool : List Slot) (slot : Slot) (included : slot ∈ pool) : Fin pool.length :=
  ⟨pool.idxOf slot, List.idxOf_lt_length_of_mem included⟩

@[simp] theorem slot_at_reference (pool : List Slot) (slot : Slot) (included : slot ∈ pool) :
    pool[reference pool slot included] = slot :=
  List.getElem_idxOf (List.idxOf_lt_length_of_mem included)

/-- Equality of allocated indices reflects equality of original positions;
unrelated rows, families, and argument positions cannot become unified. -/
theorem reference_eq_iff (pool : List Slot) (first last : Slot)
    (firstIn : first ∈ pool) (lastIn : last ∈ pool) :
    reference pool first firstIn = reference pool last lastIn ↔ first = last := by
  constructor
  · intro same
    have positions := congrArg (fun index : Fin pool.length => pool[index]) same
    simpa only [slot_at_reference] using positions
  · rintro rfl
    rfl

/-- The finite lookup is also defined for a query which is not in the input.
Missing positions are rejected rather than redirected to a default slot. -/
def locate (pool : List Slot) (slot : Slot) : Option (Fin pool.length) :=
  if included : slot ∈ pool then some (reference pool slot included) else none

theorem locate_present (pool : List Slot) (slot : Slot) (included : slot ∈ pool) :
    locate pool slot = some (reference pool slot included) := by
  simp only [locate, dite_eq_left included]

theorem locate_eq_none (pool : List Slot) (slot : Slot) :
    locate pool slot = none ↔ slot ∉ pool := by
  by_cases included : slot ∈ pool <;> simp [locate, included]

abbrev Values (occurrences : List (Occurrence scopes α)) :=
  Fin (slots .value occurrences).length

abbrev Effects (occurrences : List (Occurrence scopes α)) :=
  Fin (slots .row occurrences).length

abbrev Assignment (occurrences : List (Occurrence scopes α)) :=
  Locals (slots .value occurrences).length (slots .row occurrences).length

/-- A semantic source assignment is represented by precisely the finite
occurring slots. No support condition is placed on its arbitrary values. -/
def encode (occurrences : List (Occurrence scopes α))
    (values : Slot → Common.Ty) (effects : Slot → Common.Row) : Assignment occurrences where
  values index := values ((slots .value occurrences)[index])
  effects index := effects ((slots .row occurrences)[index])

def valueAt (occurrences : List (Occurrence scopes α)) (assignment : Assignment occurrences)
    (slot : Slot) : Common.Ty :=
  match locate (slots .value occurrences) slot with
  | some index => assignment.values index
  | none => .bottom

def rowAt (occurrences : List (Occurrence scopes α)) (assignment : Assignment occurrences)
    (slot : Slot) : Common.Row :=
  match locate (slots .row occurrences) slot with
  | some index => assignment.effects index
  | none => Common.rowEmpty

theorem valueAt_present (occurrences : List (Occurrence scopes α)) (assignment : Assignment occurrences)
    (slot : Slot) (included : slot ∈ slots .value occurrences) :
    valueAt occurrences assignment slot = assignment.values (reference _ slot included) := by
  simp only [valueAt, locate_present _ _ included]

theorem rowAt_present (occurrences : List (Occurrence scopes α)) (assignment : Assignment occurrences)
    (slot : Slot) (included : slot ∈ slots .row occurrences) :
    rowAt occurrences assignment slot = assignment.effects (reference _ slot included) := by
  simp only [rowAt, locate_present _ _ included]

theorem valueAt_encode (occurrences : List (Occurrence scopes α))
    (values : Slot → Common.Ty) (effects : Slot → Common.Row) (slot : Slot)
    (included : slot ∈ slots .value occurrences) :
    valueAt occurrences (encode occurrences values effects) slot = values slot := by
  simp only [valueAt_present _ _ _ included, encode, slot_at_reference]

theorem rowAt_encode (occurrences : List (Occurrence scopes α))
    (values : Slot → Common.Ty) (effects : Slot → Common.Row) (slot : Slot)
    (included : slot ∈ slots .row occurrences) :
    rowAt occurrences (encode occurrences values effects) slot = effects slot := by
  simp only [rowAt_present _ _ _ included, encode, slot_at_reference]

/-- There are no unused allocated locals. Decoding and re-encoding any
unrestricted local assignment recovers exactly that same assignment. -/
theorem encode_decode (occurrences : List (Occurrence scopes α)) (assignment : Assignment occurrences) :
    encode occurrences (valueAt occurrences assignment) (rowAt occurrences assignment) = assignment := by
  cases assignment with
  | mk values effects =>
    unfold encode
    congr 1 <;> funext index
    · rw [valueAt_present occurrences ⟨values, effects⟩ ((slots .value occurrences)[index])
        (List.getElem_mem index.isLt)]
      apply congrArg values
      apply Fin.ext
      exact (slots_nodup .value occurrences).idxOf_getElem index.val index.isLt
    · rw [rowAt_present occurrences ⟨values, effects⟩ ((slots .row occurrences)[index])
        (List.getElem_mem index.isLt)]
      apply congrArg effects
      apply Fin.ext
      exact (slots_nodup .row occurrences).idxOf_getElem index.val index.isLt

end Yulang.CommonEffectMixedFamilyAllocation
