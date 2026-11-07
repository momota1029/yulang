import Yulang.CommonBoundCoalescing

/-!
# Independent rigid-head inspection in the common carrier

Role observations separate distinct rigid constructors even when their
payloads and record tails are arbitrary regular common types. Bottom and top
are the exact two exceptional heads. These facts justify the static failure
branches of the symbolic source inspector; no concrete assignment is used by
that compiler to decide a head mismatch.

Union/intersection elimination uses the already-proved lattice laws. The
head theorem intentionally does not pretend that a mixed-head lattice is a
rigid constructor or that source intersections / target unions can be
replaced by a disjunction of subtype comparisons.
-/

namespace Yulang.CommonRigidHeadInspection

open Common (Ty Subtype)

inductive Head where
  | bottom | top | base (scalar : Inference.Base) | pair | arrow | records | variant (label : Nat) | lattice
  deriving DecidableEq

def head : Ty → Head
  | .bottom => .bottom
  | .top => .top
  | .base scalar => .base scalar
  | .pair _ _ => .pair
  | .arrow _ _ _ _ => .arrow
  | .emptyRecord | .exactEmpty | .record _ _ _ | .recordDefault _ _ _ => .records
  | .variant label _ => .variant label
  | .union _ _ | .inter _ _ | .mask _ _ => .lattice

def rigid : Ty → Bool
  | .union _ _ | .inter _ _ | .mask _ _ => false
  | _ => true

def roleHead : Ty → ProducerContextual.Head
  | .base scalar => .base scalar
  | .pair _ _ => .pair
  | .arrow _ _ _ _ => .arrow
  | .variant label _ => .variant label
  | _ => .records

/-- All payloads and rows are arbitrary. The separating demand is an actual
role environment, and the bottom separation is the impossible observation. -/
theorem rigid_heads {source target : Ty}
    (sourceRigid : rigid source = true) (targetRigid : rigid target = true)
    (below : Subtype source target) :
    head source = .bottom ∨ head target = .top ∨ head source = head target := by
  let env : CommonFinite.Environment Common.Row := ⟨fun _ => .bottom, fun _ => [roleHead target]⟩
  have impossible := (CommonFinite.producerLe_iff_probe _ _).mp (below 0) 0 env .impossible
  have role := (CommonFinite.producerLe_iff_probe _ _).mp (below 0) 0 env (.role 0)
  cases source <;> cases target <;>
    simp_all [rigid, head, roleHead, env, Common.observeTy, CommonSyntax.Layer.evalAt,
      CommonFinite.ProbeAt, CommonFinite.ProbeStep, CommonFinite.MaskedProbeStep]

theorem rigid_mismatch {source target : Ty}
    (sourceRigid : rigid source = true) (targetRigid : rigid target = true)
    (sourceNotBottom : head source ≠ .bottom) (targetNotTop : head target ≠ .top)
    (different : head source ≠ head target) : ¬ Subtype source target := by
  intro below
  rcases rigid_heads sourceRigid targetRigid below with bottom | top | same
  · exact sourceNotBottom bottom
  · exact targetNotTop top
  · exact different same

theorem base_iff (first last : Inference.Base) :
    Subtype (.base first) (.base last) ↔ first = last := by
  constructor
  · intro below
    have same := rigid_heads rfl rfl below
    simpa [head] using same
  · intro same
    subst last
    exact Common.subtype_refl _

/-- Variant tags are statically compared; payloads retain the full common
order and may contain masks, roles, arrows, defaults or regular graphs. -/
theorem variant_iff (first last : Nat) (source target : Ty) :
    Subtype (Common.variant first source) (Common.variant last target) ↔
      first = last ∧ Subtype source target := by
  constructor
  · intro below
    have shape := rigid_heads rfl rfl below
    have same : first = last := by
      simpa [Common.variant, head] using shape
    subst last
    exact ⟨rfl, (Common.common_variant_iff first source target).mp below⟩
  · rintro ⟨same, payload⟩
    subst last
    exact (Common.common_variant_iff first source target).mpr payload

end Yulang.CommonRigidHeadInspection
