import Yulang.CommonFiniteOptionalInspection
import Yulang.CommonGeneratedBoundInspection

/-!
# Finite soundness of the actual symbolic bound branches

Each theorem reads a branch returned by the fixed symbolic inspector. The
compiler receives no rows or type values. Guarded children use the preceding
constructor observation; record tails and default sources use the current
observation. No full ordinary-child subtype or local-width premise is used.

For non-rigid source layers both finite child interpretations are available.
The proof uses only the appropriate one at each emitted edge. This interface
allows a depth induction to supply guarded children while a strict source
syntax induction supplies the same-depth children. It does not infer a
previous-depth comparison from a current-depth comparison.
-/

namespace Yulang.CommonFiniteBoundInspection

open Common (Ty Row)
open CommonFiniteChildInspection (BelowAt GuardedAt CheckAt BranchAt)
open CommonFiniteOptionalInspection
open CommonSymbolicBoundInspection
open CommonSymbolicConstraints (Check Branch)
open CommonPayloadProjection (Payload)

universe u v

abbrev BoundBranch (Rows : Type u) (Node : Type v) := Branch Rows Node (BoundRef Node)

/-- Rigid constructor children are guarded. Other source layers may also
contain same-depth ordinary edges. -/
def NeedsCurrent : Source Rows Node → Bool
  | .rigid _ => false
  | _ => true

def BranchAtSource (depth : Nat) (rows : Rows → Row) (values : Node → Ty)
    (source : Source Rows Node) (branch : BoundBranch Rows Node) : Prop :=
  BranchAt false depth rows values (BoundRef.eval values) branch ∧
    (NeedsCurrent source = true → BranchAt true depth rows values (BoundRef.eval values) branch)

private theorem one_at (sameDepth : Bool) (depth : Nat) (rows : Rows → Row) (values : Node → Ty)
    (first last : BoundRef Node) :
    BranchAt sameDepth depth rows values (BoundRef.eval values) [edge first last] ↔
      if sameDepth then BelowAt depth (first.eval values) (last.eval values)
      else GuardedAt depth (first.eval values) (last.eval values) := by
  simp only [CommonFiniteChildInspection.branchAt_cons, CommonFiniteChildInspection.branchAt_nil,
    edge, CheckAt, Payload.evalLayer, and_true]

private theorem two_at (sameDepth : Bool) (depth : Nat) (rows : Rows → Row) (values : Node → Ty)
    (first last first' last' : BoundRef Node) :
    BranchAt sameDepth depth rows values (BoundRef.eval values)
        [edge first last, edge first' last'] ↔
      (if sameDepth then BelowAt depth (first.eval values) (last.eval values)
        else GuardedAt depth (first.eval values) (last.eval values)) ∧
      (if sameDepth then BelowAt depth (first'.eval values) (last'.eval values)
        else GuardedAt depth (first'.eval values) (last'.eval values)) := by
  simp only [CommonFiniteChildInspection.branchAt_cons, CommonFiniteChildInspection.branchAt_nil,
    edge, CheckAt, Payload.evalLayer, and_true]

theorem default_branch_at_sound (depth : Nat) (rows : Rows → Row) (values : Node → Ty)
    (label : Nat) (source fallback : BoundRef Node) (payload : Option Node)
    (branch : BoundBranch Rows Node) (returned : branch ∈ defaultBranches label source fallback payload)
    (current : BranchAt true depth rows values (BoundRef.eval values) branch)
    (guarded : BranchAt false depth rows values (BoundRef.eval values) branch) :
    BelowAt depth (Common.recordDefault label (source.eval values) (fallback.eval values))
      (Common.required label (payloadValue values payload)) := by
  apply default_branches_at_sound
  simp only [defaultBranches, List.mem_cons, List.not_mem_nil, or_false] at returned
  rcases returned with rfl | rfl | rfl
  · have first := (two_at false depth rows values _ _ _ _).mp guarded
    have last := (two_at true depth rows values _ _ _ _).mp current
    have top : GuardedAt depth (.top : Ty) ((payloadRef payload).eval values) := first.1
    rw [payloadRef_eval] at top
    exact Or.inl ⟨top, last.2⟩
  · have both := (two_at true depth rows values _ _ _ _).mp current
    exact Or.inr (Or.inl both)
  · have first := (two_at true depth rows values _ _ _ _).mp current
    have last := (two_at false depth rows values _ _ _ _).mp guarded
    exact Or.inr (Or.inr ⟨first.1, by simpa only [Bool.false_eq_true, ↓reduceIte, payloadRef_eval] using last.2⟩)

theorem required_at_sound (depth : Nat) (rows : Rows → Row) (values : Node → Ty)
    (source : Source Rows Node) (label : Nat) (payload : Option Node)
    (branch : BoundBranch Rows Node) (returned : branch ∈ inspectRequired source label payload)
    (valid : BranchAtSource depth rows values source branch) :
    BelowAt depth (source.eval rows values) ((BoundRef.required label payload).eval values) := by
  cases source with
  | reference node =>
      simp only [inspectRequired, List.mem_singleton] at returned
      subst branch
      exact (one_at true depth rows values _ _).mp (valid.2 rfl)
  | union first last =>
      simp only [inspectRequired, List.mem_singleton] at returned
      subst branch
      exact (CommonFinite.producerLe_union_iff _ _ _).mpr
        ((two_at true depth rows values _ _ _ _).mp (valid.2 rfl))
  | record current head tail =>
      by_cases same : label = current
      · subst current
        simp only [inspectRequired, ↓reduceIte, List.mem_singleton] at returned
        subst branch
        apply (record_same_required_at_iff depth label _ _ _).mpr
        simpa only [Bool.false_eq_true, ↓reduceIte, payloadRef_eval] using (one_at false depth rows values _ _).mp valid.1
      · simp only [inspectRequired, same, ↓reduceIte, List.mem_singleton] at returned
        subst branch
        exact (record_other_required_at_iff depth current label _ _ _ same).mpr
          ((one_at true depth rows values _ _).mp (valid.2 rfl))
  | recordDefault current base fallback =>
      by_cases same : label = current
      · subst current
        exact default_branch_at_sound depth rows values label base fallback payload branch
          (by simpa only [inspectRequired, ↓reduceIte] using returned) (valid.2 rfl) valid.1
      · simp only [inspectRequired, same, ↓reduceIte, List.mem_singleton] at returned
        subst branch
        exact (default_other_required_at_iff depth current label _ _ _ same).mpr
          ((one_at true depth rows values _ _).mp (valid.2 rfl))
  | width | exactEmpty => simp only [inspectRequired, List.not_mem_nil] at returned
  | rigid node =>
      cases node with
      | bottom => exact CommonBoundCoalescing.bottom_le _ depth
      | top | base | pair | variant | arrow => simp only [inspectRequired, List.not_mem_nil] at returned

theorem optional_at_sound (depth : Nat) (rows : Rows → Row) (values : Node → Ty)
    (source : Source Rows Node) (label : Nat) (payload : Option Node)
    (branch : BoundBranch Rows Node) (returned : branch ∈ inspectOptional source label payload)
    (valid : BranchAtSource depth rows values source branch) :
    BelowAt depth (source.eval rows values) ((BoundRef.optional label payload).eval values) := by
  cases source with
  | reference node =>
      simp only [inspectOptional, List.mem_singleton] at returned
      subst branch
      exact (one_at true depth rows values _ _).mp (valid.2 rfl)
  | union first last =>
      simp only [inspectOptional, List.mem_singleton] at returned
      subst branch
      exact (CommonFinite.producerLe_union_iff _ _ _).mpr
        ((two_at true depth rows values _ _ _ _).mp (valid.2 rfl))
  | record current head tail =>
      by_cases same : label = current
      · subst current
        simp only [inspectOptional, ↓reduceIte, List.mem_singleton] at returned
        subst branch
        apply (record_same_optional_at_iff depth label _ _ _).mpr
        simpa only [Bool.false_eq_true, ↓reduceIte, payloadRef_eval] using (one_at false depth rows values _ _).mp valid.1
      · simp only [inspectOptional, same, ↓reduceIte, List.mem_singleton] at returned
        subst branch
        exact record_other_optional_at_sound depth current label _ _ _ same
          ((one_at true depth rows values _ _).mp (valid.2 rfl))
  | recordDefault current base fallback =>
      by_cases same : label = current
      · subst current
        exact CommonFinite.producerLe_trans
          (default_branch_at_sound depth rows values label base fallback payload branch
            (by simpa only [inspectOptional, ↓reduceIte] using returned) (valid.2 rfl) valid.1)
          (CommonBoundCoalescing.le_union_right _ _ depth)
      · simp only [inspectOptional, same, ↓reduceIte, List.mem_singleton] at returned
        subst branch
        exact default_other_optional_at_sound depth current label _ _ _ same
          ((one_at true depth rows values _ _).mp (valid.2 rfl))
  | width => simp only [inspectOptional, List.not_mem_nil] at returned
  | exactEmpty => exact CommonBoundCoalescing.le_union_left _ _ depth
  | rigid node =>
      cases node with
      | bottom => exact CommonBoundCoalescing.bottom_le _ depth
      | top | base | pair | variant | arrow => simp only [inspectOptional, List.not_mem_nil] at returned

theorem width_at_sound (depth : Nat) (rows : Rows → Row) (values : Node → Ty)
    (source : Source Rows Node) (branch : BoundBranch Rows Node)
    (returned : branch ∈ inspectWidth source)
    (valid : BranchAtSource depth rows values source branch) :
    BelowAt depth (source.eval rows values) Common.emptyRecord := by
  cases source with
  | reference node =>
      simp only [inspectWidth, List.mem_singleton] at returned
      subst branch
      exact (one_at true depth rows values _ _).mp (valid.2 rfl)
  | union first last =>
      simp only [inspectWidth, List.mem_singleton] at returned
      subst branch
      exact (CommonFinite.producerLe_union_iff _ _ _).mpr
        ((two_at true depth rows values _ _ _ _).mp (valid.2 rfl))
  | width | exactEmpty | record | recordDefault =>
      exact ((CommonRecordTargetProfiles.subtype_emptyRecord_iff _).mpr rfl) depth
  | rigid node =>
      cases node with
      | bottom => exact CommonBoundCoalescing.bottom_le _ depth
      | top | base | pair | variant | arrow => simp only [inspectWidth, List.not_mem_nil] at returned

theorem rigid_at_sound (depth : Nat) (rows : Rows → Row) (values : Node → Ty)
    (source : Source Rows Node) (target : Rigid Rows Node) (targetRef : BoundRef Node)
    (targetSame : Common.Equivalent (target.eval rows (BoundRef.eval values)) (targetRef.eval values))
    (branch : BoundBranch Rows Node) (returned : branch ∈ inspectRigid source target targetRef)
    (valid : BranchAtSource depth rows values source branch) :
    BelowAt depth (source.eval rows values) (target.eval rows (BoundRef.eval values)) := by
  cases source with
  | reference node =>
      simp only [inspectRigid, List.mem_singleton] at returned
      subst branch
      exact CommonFinite.producerLe_trans
        ((one_at true depth rows values _ _).mp (valid.2 rfl)) (targetSame.2 depth)
  | union first last =>
      simp only [inspectRigid, List.mem_singleton] at returned
      subst branch
      exact CommonFinite.producerLe_trans
        ((CommonFinite.producerLe_union_iff _ _ _).mpr
          ((two_at true depth rows values _ _ _ _).mp (valid.2 rfl))) (targetSame.2 depth)
  | rigid node =>
      simp only [inspectRigid, List.mem_singleton] at returned
      subst branch
      exact CommonFiniteChildInspection.node_inspect_at_sound depth rows values
        (BoundRef.eval values) node target valid.1
  | width | exactEmpty | record | recordDefault =>
      cases target
      all_goals first
        | exact CommonBoundCoalescing.le_top _ depth
        | simp only [inspectRigid, List.not_mem_nil] at returned

end Yulang.CommonFiniteBoundInspection
