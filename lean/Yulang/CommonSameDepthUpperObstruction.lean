import Yulang.CommonOrdinaryEdgeClosure

/-!
# Same-depth recursive equations do not by themselves enforce an upper bound

For distinct labels `a` and `b`, the width record `W = required a P` solves
`X = record a P X | (bottom & required b Q)`, yet `W` does not satisfy the
upper bound `required b Q`. The common regular equation family actually
recovers this model when it is used as the recursive parameter.

This rejects an unconditional inference from independent coalesced equations
to their original upper constraints. It does not contradict the existing
bound theorems, which retain rigid consistency, or symbolic inspection, whose
unresolved field-profile constraint rejects this model. No claim is made here
that this one-slot graph is the complete output of a particular source term.
-/

namespace Yulang.CommonSameDepthUpperObstruction

open Common (Ty Subtype Equivalent)

theorem union_inter_bottom (source target : Ty) :
    Equivalent (.union source (.inter .bottom target)) source := by
  constructor
  · apply (Common.common_union_is_join _ _ _).mpr
    exact ⟨Common.subtype_refl _, Common.subtype_trans
      (CommonBoundCoalescing.inter_le_left _ _) (CommonBoundCoalescing.bottom_le _)⟩
  · exact CommonBoundCoalescing.le_union_left _ _

theorem shadowed_tail_fixedpoint (first last : Nat) (payload target : Ty) :
    Equivalent
      (.union (Common.record first payload (Common.required first payload))
        (.inter .bottom (Common.required last target)))
      (Common.required first payload) :=
  Common.equivalent_trans (union_inter_bottom _ _)
    (Common.common_shadowed_head_equivalent first payload payload Common.emptyRecord)

theorem missing_label (first last : Nat) (different : first ≠ last) (payload target : Ty) :
    ¬ Subtype (Common.required first payload) (Common.required last target) := by
  rw [CommonRecordTargetProfiles.subtype_required_iff]
  simp [CommonPayloadProjection.ProfileBelow, CommonPayloadProjection.fieldType,
    CommonPayloadProjection.fieldProject, Common.required, Common.record, Common.emptyRecord,
    Ne.symm different]

/-- A single original variable with a same-depth record tail. The payloads
are quoted external common syntax, so they remain arbitrary regular types. -/
def graph (first last : Nat) (payload target : Ty) : CommonPresenceTailRegular.Graph 1 0 :=
  fun _ => .union (.record first (.inr (.node payload)) (.ref 0))
    (.inter (.atom .bottom) (.atom (.record last (.inr (.node target)) .emptyRecord)))

theorem independent_model (first last : Nat) (payload target : Ty) :
    CommonPresenceTailRegular.Models (graph first last payload target)
      (fun _ => Common.required first payload) := by
  intro index
  change Equivalent
    (.union (Common.record first payload (Common.required first payload))
      (.inter .bottom (Common.required last target))) (Common.required first payload)
  exact shadowed_tail_fixedpoint first last payload target

/-- The current equation-family constructor recovers the offending model
from an unrestricted recursive parameter; this is not a hypothetical model. -/
theorem solver_recovers_counterexample (first last : Nat) (different : first ≠ last)
    (payload target : Ty) :
    let solution := CommonPresenceTailRegular.solveBlock (graph first last payload target)
      (fun _ => Common.required first payload)
    CommonPresenceTailRegular.Models (graph first last payload target) solution ∧
      Equivalent (solution 0) (Common.required first payload) ∧
      ¬ Subtype (solution 0) (Common.required last target) := by
  dsimp only
  have same := CommonPresenceTailRegular.solveBlock_retract (graph first last payload target)
    (fun _ => Common.required first payload) (independent_model first last payload target) 0
  refine ⟨CommonPresenceTailRegular.solveBlock_models _ _, same, ?_⟩
  intro below
  exact missing_label first last different payload target (Common.subtype_trans same.2 below)

end Yulang.CommonSameDepthUpperObstruction
