import Yulang.PresenceFiniteBounds

/-!
# Complete implication under every outer field mask

Unmasked implication cannot be substituted for implication under shadowing:
`present l ∩ absent l` is empty, but hiding `l` turns both demands into records.
This module decides the stronger relation for the explicitly finite bound
grammar, by enumerating only the masks on labels used by the two bounds.
The exactness theorem quantifies every hidden-label list, including arbitrary
extra labels and repetitions. No parameter predicates are enumerated.
-/

namespace Yulang.PresenceMaskedBounds

open PresenceFiniteBounds (Bound denote labels profiles checkLe)
open PresenceDataTypes (Le)

def mask (hidden : List Nat) : Bound → Bound
  | .present label => if label ∈ hidden then .records else .present label
  | .absent label => if label ∈ hidden then .records else .absent label
  | .union left right => .union (mask hidden left) (mask hidden right)
  | .inter left right => .inter (mask hidden left) (mask hidden right)
  | bound => bound

/-- This operation is the existing presence-layer mask, not a new semantic
choice about shadowing or the legacy width type. -/
theorem toLayer_mask (hidden : List Nat) (bound : Bound) :
    PresenceFiniteBounds.toLayer (mask hidden bound) =
      (PresenceFiniteBounds.toLayer bound).mask hidden := by
  induction bound with
  | present label | absent label =>
      by_cases hiddenLabel : label ∈ hidden <;>
        simp [mask, PresenceFiniteBounds.toLayer, PresenceLayers.Layer.mask, hiddenLabel]
  | union left right ihl ihr | inter left right ihl ihr =>
      simp [mask, PresenceFiniteBounds.toLayer, PresenceLayers.Layer.mask, ihl, ihr]
  | _ => rfl

theorem denote_mask (hidden : List Nat) (bound : Bound) (value : SourceDataRuntime.Value) :
    denote (mask hidden bound) value ↔
      (PresenceFiniteBounds.toLayer bound).meaning (fun _ => PresenceDataTypes.any) hidden value := by
  rw [← PresenceFiniteBounds.toLayer_exact, toLayer_mask]
  exact PresenceLayers.Layer.mask_exact _ hidden _ value

/-- Only membership of the bound's finite syntactic label support matters. -/
theorem mask_congr (first last : List Nat) (bound : Bound)
    (same : ∀ label ∈ labels bound, label ∈ first ↔ label ∈ last) :
    mask first bound = mask last bound := by
  induction bound with
  | present label | absent label =>
      simp only [mask, same label (List.mem_singleton_self label)]
  | union left right ihl ihr | inter left right ihl ihr =>
      have left := ihl (fun label member => same label (List.mem_append_left _ member))
      have right := ihr (fun label member => same label (List.mem_append_right _ member))
      simp only [mask, left, right]
  | _ => rfl

def relevantMask (observed hidden : List Nat) : List Nat :=
  observed.filter fun label => label ∈ hidden

theorem relevantMask_mem_profiles (observed hidden : List Nat) :
    relevantMask observed hidden ∈ profiles observed :=
  PresenceFiniteBounds.filter_mem_profiles observed _

theorem relevantMask_exact (observed hidden : List Nat) (bound : Bound)
    (covers : ∀ label ∈ labels bound, label ∈ observed) :
    mask (relevantMask observed hidden) bound = mask hidden bound := by
  apply mask_congr
  intro label member
  simp [relevantMask, covers label member]

/-- A total finite scan, with no caller-supplied inclusion decision. -/
def checkMaskedLe (left right : Bound) : Bool :=
  (profiles (labels left ++ labels right)).all fun hidden =>
    checkLe (mask hidden left) (mask hidden right)

theorem checkMaskedLe_exact (left right : Bound) :
    checkMaskedLe left right = true ↔
      ∀ hidden : List Nat, Le (denote (mask hidden left)) (denote (mask hidden right)) := by
  simp only [checkMaskedLe, List.all_eq_true]
  constructor
  · intro checked hidden
    have first := relevantMask_exact (labels left ++ labels right) hidden left
      (fun label member => List.mem_append_left _ member)
    have last := relevantMask_exact (labels left ++ labels right) hidden right
      (fun label member => List.mem_append_right _ member)
    have accepted := checked (relevantMask (labels left ++ labels right) hidden)
      (relevantMask_mem_profiles _ hidden)
    rw [first, last] at accepted
    exact (PresenceFiniteBounds.checkLe_exact _ _).mp accepted
  · intro below hidden _
    exact (PresenceFiniteBounds.checkLe_exact _ _).mpr (below hidden)

theorem checkMaskedLe_rejects (left right : Bound) :
    checkMaskedLe left right = false ↔
      ¬ ∀ hidden : List Nat, Le (denote (mask hidden left)) (denote (mask hidden right)) := by
  rw [← checkMaskedLe_exact]
  cases checkMaskedLe left right <;> simp

namespace Examples

def contradiction : Bound := .inter (.present 7) (.absent 7)

theorem unmasked_contradiction_empty : checkLe contradiction .bottom = true := by
  decide +kernel

theorem masked_contradiction_not_empty : checkMaskedLe contradiction .bottom = false := by
  decide +kernel

end Examples

end Yulang.PresenceMaskedBounds
