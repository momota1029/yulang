import Yulang.CommonNominalConstructors
import Yulang.CommonNominalFiniteMaskOrder

/-!
# Mask congruence on arbitrary regular common types

Fresh-label reasoning at each finite observation depth makes every outer
mask monotone for the concrete common demand order. The type parameters,
recursive blocks, negative contexts and effect rows are unrestricted.
-/

namespace Yulang.CommonNominalCarrier

open Common (rowLe)

theorem common_mask_mono (hidden : List Nat) {source target : Ty}
    (below : Subtype source target) : Subtype (mask hidden source) (mask hidden target) :=
  fun depth => CommonNominalFinite.producerLe_mask hidden (below depth)

theorem common_mask_type_congr (hidden : List Nat) {first last : Ty}
    (same : Equivalent first last) : Equivalent (mask hidden first) (mask hidden last) :=
  ⟨common_mask_mono hidden same.1, common_mask_mono hidden same.2⟩

/-- Requiring all outer masks does not strengthen this complete demand order.
There is no extra mask-stability condition on a type or a solved parameter. -/
theorem common_subtype_iff_masked (source target : Ty) :
    Subtype source target ↔ ∀ hidden, Subtype (mask hidden source) (mask hidden target) := by
  constructor
  · intro below hidden
    exact common_mask_mono hidden below
  · intro allMasks depth
    have first := CommonNominalFinite.mask_nil (leRow := rowLe) (observeTy depth source)
    have last := CommonNominalFinite.mask_nil (leRow := rowLe) (observeTy depth target)
    exact CommonNominalFinite.producerLe_trans first.2
      (CommonNominalFinite.producerLe_trans (allMasks [] depth) last.1)

theorem common_equivalent_iff_masked (first last : Ty) :
    Equivalent first last ↔ ∀ hidden, Equivalent (mask hidden first) (mask hidden last) := by
  constructor
  · intro same hidden
    exact common_mask_type_congr hidden same
  · intro same
    exact ⟨(common_subtype_iff_masked first last).mpr (fun hidden => (same hidden).1),
      (common_subtype_iff_masked last first).mpr (fun hidden => (same hidden).2)⟩

end Yulang.CommonNominalCarrier
