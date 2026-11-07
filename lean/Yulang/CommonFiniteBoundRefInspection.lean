import Yulang.CommonBoundRefExact
import Yulang.CommonOptionalBoundEncoding
import Yulang.CommonBoundInspectionDescent

/-!
# Finite soundness of the fixed bound-reference dispatcher

These are finite-observation laws for the actual pruned dispatcher, not for
an abstract relation on arbitrary endpoints. Original constructor equations
identify the shared source and target layers. A rigid target cannot use the
variable fallback. Optional inspection needs no pool-width assumption in
this soundness direction.
-/

namespace Yulang.CommonFiniteBoundRefInspection

open Common (Ty Row Equivalent)
open Core.PresenceGeneration (TyTerm)
open PresenceOpenTailGenerationLowering (Pool subterms)
open CommonPresenceConstraintGraph (rowEval lowerNode Realizes)
open CommonSymbolicBoundInspection
open CommonBoundRefInspection
open CommonGeneratedBoundInspection (PoolSource PoolOutput)
open CommonFiniteChildInspection (BelowAt GuardedAt BranchAt)
open CommonFiniteBoundInspection (NeedsCurrent BranchAtSource)
open CommonGeneratedRigidDescent (weight rigid)
open CommonOptionalBoundEncoding (term)

variable {m : Nat}

def RigidRef (pool : Pool m) (reference : Ref pool) : Prop := rigid (term pool reference)

def current (pool : Pool m) (source : Ref pool) : Bool :=
  match sourceLayer pool source with
  | none => false
  | some layer => NeedsCurrent layer

def BranchAtRef (depth : Nat) (pool : Pool m) (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (source : Ref pool) (branch : List (InputCheck pool)) : Prop :=
  BranchAt false depth (rowEval rows) values (BoundRef.eval values) branch ∧
    (current pool source = true →
      BranchAt true depth (rowEval rows) values (BoundRef.eval values) branch)

theorem below_congr (depth : Nat) {source source' target target' : Ty}
    (first : Equivalent source source') (last : Equivalent target target') :
    BelowAt depth source target ↔ BelowAt depth source' target' :=
  ⟨fun below => CommonFinite.producerLe_trans (first.2 depth)
      (CommonFinite.producerLe_trans below (last.1 depth)),
    fun below => CommonFinite.producerLe_trans (first.1 depth)
      (CommonFinite.producerLe_trans below (last.2 depth))⟩

theorem guarded_congr (depth : Nat) {source source' target target' : Ty}
    (first : Equivalent source source') (last : Equivalent target target') :
    GuardedAt depth source target ↔ GuardedAt depth source' target' := by
  cases depth with
  | zero => exact ⟨fun _ => CommonFiniteChildInspection.guarded_zero _ _,
      fun _ => CommonFiniteChildInspection.guarded_zero _ _⟩
  | succ depth => exact below_congr depth first last

theorem dispatchOriginal_at_sound (depth : Nat) (pool : Pool m)
    (sourceRef : Ref pool) (source : PoolSource pool)
    (target : TyTerm (Fin m)) (member : target ∈ pool.terms) (targetRef : Ref pool)
    (targetRigid : rigid target) (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (sourceSame : Equivalent (source.eval (rowEval rows) values) (sourceRef.eval values))
    (targetSame : Equivalent ((lowerNode pool target member).eval rows values) (targetRef.eval values))
    (branch : List (InputCheck pool))
    (returned : branch ∈ dispatchOriginal pool sourceRef source target member targetRef)
    (valid : BranchAtSource depth (rowEval rows) values source branch) :
    BelowAt depth (sourceRef.eval values) (targetRef.eval values) := by
  apply (below_congr depth sourceSame targetSame).mp
  cases target with
  | var => cases targetRigid
  | emptyRecord => exact CommonFiniteBoundInspection.width_at_sound _ _ _ _ _ returned valid
  | required label payload => exact CommonFiniteBoundInspection.required_at_sound _ _ _ _ _ _ _ returned valid
  | base scalar =>
      exact CommonFiniteBoundInspection.rigid_at_sound depth (rowEval rows) values source
        (.base scalar) targetRef targetSame branch returned valid
  | pair first last =>
      exact CommonFiniteBoundInspection.rigid_at_sound depth (rowEval rows) values source
        (.pair (.original (pool.child _ member first (by simp [subterms])))
          (.original (pool.child _ member last (by simp [subterms]))))
        targetRef targetSame branch returned valid
  | arrow input incoming output outgoing =>
      exact CommonFiniteBoundInspection.rigid_at_sound depth (rowEval rows) values source
        (.arrow (.original (pool.child _ member input (by simp [subterms]))) incoming
          (.original (pool.child _ member output (by simp [subterms]))) outgoing)
        targetRef targetSame branch returned valid
  | _ => simp only [dispatchOriginal, List.not_mem_nil] at returned

theorem dispatch_at_sound (depth : Nat) (pool : Pool m) (sourceRef : Ref pool)
    (source : PoolSource pool) (target : Ref pool) (targetRigid : RigidRef pool target)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) (realizes : Realizes pool rows values)
    (sourceSame : Equivalent (source.eval (rowEval rows) values) (sourceRef.eval values))
    (branch : List (InputCheck pool)) (returned : branch ∈ dispatch pool sourceRef source target)
    (valid : BranchAtSource depth (rowEval rows) values source branch) :
    BelowAt depth (sourceRef.eval values) (target.eval values) := by
  cases target with
  | original index =>
      exact dispatchOriginal_at_sound depth pool sourceRef source
        (pool.termAt index) (pool.at_mem index) (.original index) targetRigid rows values sourceSame
        (realizes index) branch returned valid
  | top => exact CommonBoundCoalescing.le_top _ depth
  | width =>
      exact (below_congr depth sourceSame (Common.equivalent_refl _)).mp
        (CommonFiniteBoundInspection.width_at_sound _ _ _ _ _ returned valid)
  | required label payload =>
      exact (below_congr depth sourceSame (Common.equivalent_refl _)).mp
        (CommonFiniteBoundInspection.required_at_sound _ _ _ _ _ _ _ returned valid)
  | optional label payload =>
      exact (below_congr depth sourceSame (Common.equivalent_refl _)).mp
        (CommonFiniteBoundInspection.optional_at_sound _ _ _ _ _ _ _ returned valid)
  | exactEmpty => simp only [dispatch, List.not_mem_nil] at returned

/-- Every returned branch of the actual fixed dispatcher is sound at each
finite observation. Values are arbitrary original constructor realizers;
there is no pool-width, solution-family or full child-subtyping premise. -/
theorem inspect_at_sound (depth : Nat) (pool : Pool m) (source target : Ref pool)
    (targetRigid : RigidRef pool target) (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (realizes : Realizes pool rows values) (branch : List (InputCheck pool))
    (returned : branch ∈ inspect pool source target)
    (valid : BranchAtRef depth pool rows values source branch) :
    BelowAt depth (source.eval values) (target.eval values) := by
  have original := mem_prune (rawInspect pool source target) branch returned
  cases found : sourceLayer pool source with
  | none => simp only [rawInspect, found, List.not_mem_nil] at original
  | some layer =>
      apply dispatch_at_sound depth pool source layer target targetRigid rows values realizes
        (sourceLayer_exact pool source layer found rows values realizes) branch
        (by simpa only [rawInspect, found] using original)
      simpa only [BranchAtRef, current, found, BranchAtSource] using valid

theorem dispatchOriginal_current_sources (pool : Pool m) (sourceRef : Ref pool)
    (source : PoolSource pool) (target : TyTerm (Fin m)) (member : target ∈ pool.terms)
    (targetRef : Ref pool) (targetRigid : rigid target) (requested : NeedsCurrent source = true) :
    ∀ branch ∈ dispatchOriginal pool sourceRef source target member targetRef,
      ∀ first last, edge first last ∈ branch →
        first ∈ CommonBoundInspectionDescent.currentSources source := by
  cases target with
  | var => cases targetRigid
  | emptyRecord => exact CommonBoundInspectionDescent.width_current_sources source
  | required label payload => exact CommonBoundInspectionDescent.required_current_sources source label _
  | base scalar => exact CommonBoundInspectionDescent.rigid_current_sources source (.base scalar) targetRef requested
  | pair first last =>
      exact CommonBoundInspectionDescent.rigid_current_sources source
        (.pair (.original (pool.child _ member first (by simp [subterms])))
          (.original (pool.child _ member last (by simp [subterms])))) targetRef requested
  | arrow input incoming output outgoing =>
      exact CommonBoundInspectionDescent.rigid_current_sources source
        (.arrow (.original (pool.child _ member input (by simp [subterms]))) incoming
          (.original (pool.child _ member output (by simp [subterms]))) outgoing) targetRef requested
  | _ => simp only [dispatchOriginal, List.not_mem_nil, false_implies, implies_true]

theorem dispatch_current_sources (pool : Pool m) (sourceRef : Ref pool)
    (source : PoolSource pool) (target : Ref pool) (targetRigid : RigidRef pool target)
    (requested : NeedsCurrent source = true) :
    ∀ branch ∈ dispatch pool sourceRef source target,
      ∀ first last, edge first last ∈ branch →
        first ∈ CommonBoundInspectionDescent.currentSources source := by
  cases target with
  | original index =>
      exact dispatchOriginal_current_sources pool sourceRef source
        (pool.termAt index) (pool.at_mem index) (.original index) targetRigid requested
  | width => exact CommonBoundInspectionDescent.width_current_sources source
  | required label payload => exact CommonBoundInspectionDescent.required_current_sources source label payload
  | optional label payload => exact CommonBoundInspectionDescent.optional_current_sources source label payload
  | top | exactEmpty => simp [dispatch]

theorem smaller_term (pool : Pool m) (source : TyTerm (Fin m)) (child : Ref pool)
    (smaller : CommonBoundInspectionDescent.SmallerSource pool source child) :
    weight (term pool child) < weight source := by
  cases child <;> first | exact smaller | cases smaller

/-- The actual dispatcher preserves strict source syntax descent at every
same-depth child, including default branches and dedicated optional targets.
No instantiated type shape or well-foundedness of a common graph is used. -/
theorem inspect_current_decreases (pool : Pool m) (source target : Ref pool)
    (sourceRigid : RigidRef pool source) (targetRigid : RigidRef pool target)
    (requested : current pool source = true) (branch : List (InputCheck pool))
    (returned : branch ∈ inspect pool source target) (first last : Ref pool)
    (included : edge first last ∈ branch) :
    weight (term pool first) < weight (term pool source) := by
  have original := mem_prune (rawInspect pool source target) branch returned
  cases found : sourceLayer pool source with
  | none => simp only [rawInspect, found, List.not_mem_nil] at original
  | some layer =>
      have requestedLayer : NeedsCurrent layer = true := by
        simpa only [current, found] using requested
      have inside := dispatch_current_sources pool source layer target targetRigid requestedLayer branch
        (by simpa only [rawInspect, found] using original) first last included
      cases source with
      | original index =>
          exact smaller_term pool (pool.termAt index) first
            (CommonBoundInspectionDescent.node_current_sources_smaller pool
              (pool.termAt index) (pool.at_mem index) layer found sourceRigid requestedLayer first inside)
      | top =>
          cases found
          cases requestedLayer
      | _ => cases found

end Yulang.CommonFiniteBoundRefInspection
