import Yulang.CommonGeneratedRigidInspection

/-!
# Proper-child provenance of symbolic rigid inspection

The generic inspector has variable cases for use outside the generated rigid
pass. Those cases cannot be reached by `rigidComparisons`: both endpoints
are original constructor nodes. Every child comparison that the actual pass
emits uses original shared IDs and strictly decreases the sum of the two
source-term weights. Every profile comparison uses a proper target child.
Static discharge preserves this provenance for every returned branch.

This is a local descent statement for one inspection step. It does not assert
closure of the generated endpoint grammar under negative arrow children, or
termination of interleaved variable propagation and profile saturation.
-/

namespace Yulang.CommonGeneratedRigidDescent

open Core.PresenceGeneration (TyTerm RowTerm)
open PresenceOpenTailGenerationLowering (Pool)
open CommonSymbolicConstraints (Check Branch Alternatives)
open CommonPayloadProjection (Payload)
open CommonGeneratedRigidInspection (inspect inspectSource inspectSlot saturate)

variable {m : Nat}

/-- Only type constructors contribute. Row syntax and labels do not change
the proper-child relation measured by this finite syntax weight. -/
def weight : TyTerm α → Nat
  | .var _ | .base _ | .bottom | .top | .emptyRecord | .exactEmpty => 1
  | .union first last | .inter first last | .pair first last
  | .arrow first _ last _ | .record _ first last | .recordDefault _ first last =>
      1 + weight first + weight last
  | .required _ payload | .variant _ payload => 1 + weight payload

def rigid : TyTerm α → Prop
  | .var _ => False
  | _ => True

/-- A child comparison refers to original IDs and decreases the joint
weight. A profile comparison has an original proper target payload. -/
def Descends (pool : Pool m) (source target : TyTerm (Fin m)) :
    Check (RowTerm (Fin m)) (Fin pool.size) (Fin pool.size) → Prop
  | .childBelow (.ref first) (.ref last) =>
      weight (pool.termAt first) + weight (pool.termAt last) < weight source + weight target
  | .childBelow _ _ => False
  | .profileBelow _ (.ref payload) => weight (pool.termAt payload) < weight target
  | .profileBelow _ _ => False
  | .rowBelow _ _ | .flag _ => True

theorem inspect_descends (pool : Pool m) (source target : TyTerm (Fin m))
    (sourceMember : source ∈ pool.terms) (targetMember : target ∈ pool.terms)
    (sourceRigid : rigid source) (targetRigid : rigid target) :
    ∀ check ∈ inspect pool source target sourceMember targetMember,
      Descends pool source target check := by
  cases source <;> cases target
  all_goals simp only [rigid] at sourceRigid targetRigid
  all_goals try contradiction
  all_goals simp [inspect, inspectSource, CommonSymbolicRigidInspection.inspect,
    CommonSymbolicRigidInspection.unionLeft, CommonSymbolicRigidInspection.interRight,
    Descends, Pool.child, weight]
  all_goals omega

theorem rigid_termAt (pool : Pool m) (slot : Fin pool.size)
    (constructorNode : CommonPresenceVariableBounds.inputAt pool slot = none) :
    rigid (pool.termAt slot) := by
  unfold CommonPresenceVariableBounds.inputAt at constructorNode
  cases found : pool.termAt slot <;> simp_all [rigid]

/-- This theorem applies to the actual bound-propagated comparisons of any
finite edge set. Neither endpoint can enter a generic variable fallback. -/
theorem residual_inspect_descends (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (edge : Fin pool.size × Fin pool.size)
    (member : edge ∈ CommonBoundCoalescing.rigidComparisons
      (CommonPresenceVariableBounds.template pool edges)) :
    ∀ check ∈ inspectSlot pool edge,
      Descends pool (pool.termAt edge.1) (pool.termAt edge.2) check := by
  have endpoints := CommonPresenceVariableBounds.residuals_rigid pool edges edge member
  exact inspect_descends pool _ _ _ _ (rigid_termAt pool _ endpoints.1)
    (rigid_termAt pool _ endpoints.2)

/-- One rigid input is never merely wrapped back into a child comparison
with the same two endpoints. -/
theorem residual_omits_original (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (edge : Fin pool.size × Fin pool.size)
    (member : edge ∈ CommonBoundCoalescing.rigidComparisons
      (CommonPresenceVariableBounds.template pool edges)) :
    .childBelow (.ref edge.1) (.ref edge.2) ∉ inspectSlot pool edge := by
  intro present
  exact Nat.lt_irrefl _ (residual_inspect_descends pool edges edge member _ present)

/-- Static discharge removes checks or branches; it never invents a check. -/
theorem discharge_subset (checks : Branch Rows Node Child)
    (branch : Branch Rows Node Child)
    (returned : branch ∈ CommonSymbolicConstraints.discharge checks) :
    ∀ check ∈ branch, check ∈ checks := by
  induction checks generalizing branch with
  | nil =>
      have same : branch = [] := by simpa [CommonSymbolicConstraints.discharge] using returned
      subst branch
      simp
  | cons head rest ih =>
      have prepend : ∀ result ∈ (CommonSymbolicConstraints.discharge rest).map (head :: ·),
          ∀ check ∈ result, check ∈ head :: rest := by
        intro result included check present
        obtain ⟨original, member, rfl⟩ := List.mem_map.mp included
        rcases List.mem_cons.mp present with same | inside
        · exact List.mem_cons.mpr (Or.inl same)
        · exact List.mem_cons.mpr (Or.inr (ih original member check inside))
      cases head with
      | childBelow | rowBelow | profileBelow => exact prepend branch returned
      | flag expression =>
          cases expression with
          | literal value =>
              cases value with
              | false => cases returned
              | true =>
                  intro check present
                  exact List.mem_cons.mpr (Or.inr (ih branch returned check present))
          | atom | and | or | not => exact prepend branch returned

/-- Every check in every returned branch retains a rigid input comparison
as its origin and satisfies its local proper-child bound. -/
theorem saturate_residual_descends (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (branch : CommonGeneratedRigidInspection.Checks pool)
    (returned : branch ∈ saturate pool (CommonBoundCoalescing.rigidComparisons
      (CommonPresenceVariableBounds.template pool edges)))
    (check : Check (RowTerm (Fin m)) (Fin pool.size) (Fin pool.size))
    (present : check ∈ branch) :
    ∃ edge ∈ CommonBoundCoalescing.rigidComparisons
        (CommonPresenceVariableBounds.template pool edges),
      Descends pool (pool.termAt edge.1) (pool.termAt edge.2) check := by
  have original := discharge_subset _ branch returned check present
  obtain ⟨edge, member, emitted⟩ := List.mem_flatMap.mp original
  exact ⟨edge, member, residual_inspect_descends pool edges edge member check emitted⟩

/-- In particular all emitted child payloads are original pool references,
and their combined source weight is strictly smaller than their origin. -/
theorem residual_child_decreases (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (branch : CommonGeneratedRigidInspection.Checks pool)
    (returned : branch ∈ saturate pool (CommonBoundCoalescing.rigidComparisons
      (CommonPresenceVariableBounds.template pool edges)))
    (source target : Payload (Fin pool.size))
    (present : .childBelow source target ∈ branch) :
    ∃ edge ∈ CommonBoundCoalescing.rigidComparisons
        (CommonPresenceVariableBounds.template pool edges),
      ∃ first last, source = .ref first ∧ target = .ref last ∧
        weight (pool.termAt first) + weight (pool.termAt last) <
          weight (pool.termAt edge.1) + weight (pool.termAt edge.2) := by
  obtain ⟨edge, member, descent⟩ := saturate_residual_descends pool edges branch returned _ present
  cases source <;> cases target <;> simp only [Descends] at descent
  all_goals try contradiction
  exact ⟨edge, member, _, _, rfl, rfl, descent⟩

/-- Every profile target is an original proper target child as well. -/
theorem residual_profile_decreases (pool : Pool m) (edges : List (Fin pool.size × Fin pool.size))
    (branch : CommonGeneratedRigidInspection.Checks pool)
    (returned : branch ∈ saturate pool (CommonBoundCoalescing.rigidComparisons
      (CommonPresenceVariableBounds.template pool edges)))
    (profile : CommonSymbolicRecordProfiles.ProfileExpr (Fin pool.size) (Fin pool.size))
    (target : Payload (Fin pool.size))
    (present : .profileBelow profile target ∈ branch) :
    ∃ edge ∈ CommonBoundCoalescing.rigidComparisons
        (CommonPresenceVariableBounds.template pool edges),
      ∃ child, target = .ref child ∧ weight (pool.termAt child) < weight (pool.termAt edge.2) := by
  obtain ⟨edge, member, descent⟩ := saturate_residual_descends pool edges branch returned _ present
  cases target <;> simp only [Descends] at descent
  all_goals try contradiction
  exact ⟨edge, member, _, rfl, descent⟩

end Yulang.CommonGeneratedRigidDescent
