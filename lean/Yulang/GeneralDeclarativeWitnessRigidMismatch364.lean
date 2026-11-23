import Yulang.GeneralDeclarativeWitnessRealMismatchedRival364

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 94000
set_option maxHeartbeats 131000000
namespace Yulang.GeneralDeclarativeWitnessRigidMismatch364
open GeneralDeclarativeWitnessSeparateEndpointAuthors362 (Ordered)
open GeneralDeclarativeWitnessSelectedNonpointRoot363 (Root)
open GeneralDeclarativeWitnessOriginalEndpointProjection364 (Projection)
open GeneralDeclarativeWitnessSeparateAuthorOrder362 (lo hi)
open GeneralDeclarativeWitnessOrientedNativeRange364 (boxed point)
open GeneralDeclarativeWitnessInheritedModeFixture357 (table)
open GeneralDeclarativeWitnessFullIntervals357 (ContextDerives context_derives_nominal_exact)
open GeneralDeclarativeWitnessNativeOrder362 (node)
open GeneralNominalCommonBridge (Assignment)

/-- A wrong rigid unary constructor is excluded by the exact declared
context relation at each original endpoint, even if any ordinary
payload names or values coincide. This is not a language-wide refusal
judgment for arbitrary unions, open patterns, or pending heads. -/
theorem mismatched_code_cannot_be_typed_at_either_origin {contra} {x : Ordered contra} {e}
    {r : Root x e} (p : Projection r) (m : Assignment) (key lowPayload upPayload : Nat)
    (different : key ≠ p.a.head) :
    ¬ContextDerives table m false (lo x) (boxed key lowPayload) ∧
    ¬ContextDerives table m false (hi x) (boxed key upPayload) := by
  constructor
  · intro assumed
    unfold lo at assumed
    rw [p.a.exact] at assumed
    have h := (context_derives_nominal_exact table m false p.a.head key
      [.inl (.point (point p.a.payload))] [.inl (.point (point lowPayload))]).mp assumed
    exact different h.1.symm
  · intro assumed
    unfold hi at assumed
    rw [p.b.exact] at assumed
    have h := (context_derives_nominal_exact table m false p.b.head key
      [.inl (.point (point p.b.payload))] [.inl (.point (point upPayload))]).mp assumed
    exact different (h.1.symm.trans p.same.symm)

end Yulang.GeneralDeclarativeWitnessRigidMismatch364
