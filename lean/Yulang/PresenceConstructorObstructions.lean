import Yulang.PresenceMaskedCoalescing

/-!
# A constructor obligation cannot be silently strengthened to all child masks

The mask-indexed candidate compares each root under every outer mask, but
`PresenceLayers` observes constructor payloads without a mask. In this model,
same-tag variant subtyping does not imply all-mask subtyping of its payloads.

The example below is stronger than a failed decomposition rule: it is an
independent solution of a finite constructor graph which satisfies no closed
cache on that same graph. Therefore no finite family of the current `Closed`
caches can exactly cover its original independent solution space. A complete
constructor solver needs a different certificate/obligation representation;
the existing coalescing theorems are not weakened here.
-/

namespace Yulang.PresenceConstructorObstructions

open PresenceLayers (Layer)
open PresenceDataTypes (Le never records)
open PresenceRegularObservations (observe)
open PresenceMaskedCoalescing (observeMasked NodeSubtype Models)
open PresenceRegularCoalescing (Graph Edge Closed)
open SourceDataRuntime (Value)

namespace MaskedPayload

/-- Slots: 0 = bottom, 1 = required 7 bottom, 2 = variant 11 slot1,
3 = variant 11 bottom. Slots 1 and 0 are unmasked-equal, not mask-equal. -/
def original : PresenceRegularObservations.Graph (Fin 4) := fun index =>
  match index.val with
  | 0 => .bottom
  | 1 => .required 7 0
  | 2 => .variant 11 1
  | _ => .variant 11 0

def graph : Graph 4 := fun index => some (original index)
def constraints : List (Edge 4) := [(2, 3)]

theorem bottom_observe (depth : Nat) : observe original depth 0 = never := by
  cases depth <;> rfl

theorem payload_observe (depth : Nat) : observe original depth 1 = never := by
  funext item
  apply propext
  cases depth with
  | zero => rfl
  | succ depth =>
      simp [observe, original, Layer.denote, Layer.meaning,
        bottom_observe, PresenceDataTypes.required, never]

/-- Every root mask and every finite observation accepts the parent edge. -/
theorem parent_subtype : NodeSubtype original 2 3 := by
  intro depth hidden item valid
  cases depth with
  | zero => exact False.elim valid
  | succ depth =>
      cases item <;>
        simp_all [observeMasked, original, Layer.meaning, PresenceDataTypes.variant,
          payload_observe, never]

/-- But masking the payload's field distinguishes the two children. -/
theorem child_not_subtype : ¬ NodeSubtype original 1 0 := by
  intro below
  have valid : observeMasked original 1 [7] 1 (.record []) := by
    simp [observeMasked, original, Layer.meaning, records]
  exact below 1 [7] (.record []) valid

/-- The original constructor equations and input edge are simultaneously
satisfied; no satisfiability assumption is supplied by the caller. -/
theorem input_model : Models graph constraints original id := by
  constructor
  · intro index layer rigid depth hidden item
    have same : layer = original index := (Option.some.inj rigid).symm
    subst layer
    rfl
  · intro edge member
    have same : edge = (2, 3) := by simpa only [constraints, List.mem_singleton] using member
    subst edge
    exact parent_subtype

theorem adding_payload_edge_loses_model :
    ¬ Models graph ((1, 0) :: constraints) original id := by
  intro model
  exact child_not_subtype (model.2 (1, 0) (List.mem_cons_self))

/-- Even arbitrary extra cache edges cannot repair this loss: every cache
closed under the current rigid certificate rules excludes this input model.
The witness child predicates are the independent solution observed under
one fixed mask; the `Derives` certificate is sound for these predicates too. -/
theorem no_closed_cache_preserves_model (cache : List (Edge 4))
    (closed : Closed graph constraints cache) : ¬ Models graph cache original id := by
  intro model
  have input : (2, 3) ∈ cache := closed.inputs _ (by simp [constraints])
  have derived := closed.rigid 2 3 (.variant 11 1) (.variant 11 0) rfl rfl input
  have below := derived.sound (fun index => observeMasked original 1 [7] index)
    (fun edge member => model.2 edge member 1 [7])
  have valid : (Layer.variant 11 (1 : Fin 4)).denote
      (fun index => observeMasked original 1 [7] index) (.variant 11 (.record [])) := by
    simp [Layer.denote, Layer.meaning, PresenceDataTypes.variant, observeMasked, original, records]
  exact (below (.variant 11 (.record [])) valid).2

/-- A family of accepted branches consisting only of current closed caches
on the unchanged graph cannot be complete for all independent input models.
This is quantified over every finite list, not one particular inspector. -/
theorem no_exact_closed_alternatives (alternatives : List (List (Edge 4)))
    (closed : ∀ cache ∈ alternatives, Closed graph constraints cache) :
    ¬ (Models graph constraints original id ↔
      ∃ cache ∈ alternatives, Models graph cache original id) := by
  intro exact
  obtain ⟨cache, member, model⟩ := exact.mp input_model
  exact no_closed_cache_preserves_model cache (closed cache member) model

end MaskedPayload

end Yulang.PresenceConstructorObstructions
