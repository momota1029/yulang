import Yulang.CommonPatternBoundInspection

/-! Syntax provenance for child comparisons emitted by the pattern inspector.
Lower endpoints retain the original source grammar; only root upper bounds
gain variant and dedicated optional heads. -/

namespace Yulang.CommonPatternBoundInspection

open Core.PresenceGeneration (TyTerm)
open PresenceOpenTailGenerationLowering (Pool subterms)
open CommonSymbolicBoundInspection
open CommonGeneratedBoundInspection (PoolSource PoolRigid PoolOutput)
open CommonBoundRefInspection (Ref InputCheck LowerRef SourceGrammar RigidGrammar
  OriginalUpper PayloadUpper blocked)
open CommonOptionalPoolQueries (queries)

variable {m : Nat}

theorem upper_of_old (pool : Pool m) (reference : Ref pool)
    (good : CommonBoundRefInspection.UpperRef pool reference) : UpperRef pool reference := by
  cases reference with
  | original index => exact .old good
  | _ => exact good

def PolarCheck (pool : Pool m) : InputCheck pool → Prop
  | .childBelow (.ref source) (.ref target) => LowerRef pool source ∧ UpperRef pool target
  | .rowBelow _ _ | .flag (.literal _) => True
  | _ => False

def WeakCheck (pool : Pool m) (check : InputCheck pool) : Prop :=
  PolarCheck pool check ∨ blocked check = true

def OutputWeak (pool : Pool m) (output : PoolOutput pool) : Prop :=
  ∀ branch ∈ output, ∀ check ∈ branch, WeakCheck pool check

theorem lift_old_polar (pool : Pool m) (check : InputCheck pool)
    (good : CommonBoundRefInspection.PolarCheck pool check) : PolarCheck pool check := by
  cases check with
  | childBelow first last =>
      cases first <;> cases last <;> first
      | exact ⟨good.1, upper_of_old pool _ good.2⟩
      | cases good
  | flag expression => cases expression <;> first | trivial | cases good
  | rowBelow => trivial
  | profileBelow => cases good

theorem lift_old_weak (pool : Pool m) (output : PoolOutput pool)
    (good : CommonBoundRefInspection.OutputWeak pool output) : OutputWeak pool output := by
  intro branch member check included
  exact ((good branch member check included)).elim
    (fun polar => Or.inl (lift_old_polar pool check polar)) Or.inr

private theorem weak_edge (pool : Pool m) (source target : Ref pool)
    (first : LowerRef pool source) (last : UpperRef pool target) :
    WeakCheck pool (edge source target) := Or.inl ⟨first, last⟩

theorem rigid_weak (pool : Pool m) (source : PoolSource pool) (sourceGood : SourceGrammar pool source)
    (target : PoolRigid pool) (targetGood : RigidGrammar pool target) (targetRef : Ref pool)
    (referenceGood : UpperRef pool targetRef) : OutputWeak pool (inspectRigid source target targetRef) := by
  cases source with
  | reference node =>
      simpa [inspectRigid, OutputWeak] using weak_edge pool node targetRef sourceGood referenceGood
  | union first last =>
      have left := weak_edge pool first targetRef (sourceGood.1.lower pool first) referenceGood
      have right := weak_edge pool last targetRef (sourceGood.2.lower pool last) referenceGood
      simpa [inspectRigid, OutputWeak] using And.intro left right
  | _ =>
      apply lift_old_weak
      simpa only [inspectRigid] using
        CommonBoundRefInspection.rigid_weak pool _ sourceGood target targetGood .top trivial

theorem dispatchOriginal_weak (pool : Pool m) (sourceRef : Ref pool) (source : PoolSource pool)
    (sourceLower : LowerRef pool sourceRef) (sourceGood : SourceGrammar pool source)
    (target : TyTerm (Fin m)) (member : target ∈ pool.terms) (targetRef : Ref pool)
    (targetGrammar : Upper target) (targetGood : UpperRef pool targetRef) :
    OutputWeak pool (dispatchOriginal pool sourceRef source target member targetRef) := by
  cases targetGrammar with
  | old good =>
    rw [dispatchOriginal_old pool sourceRef source target member targetRef good]
    cases target with
    | var => simpa [CommonBoundRefInspection.dispatchOriginal, OutputWeak] using
        weak_edge pool sourceRef targetRef sourceLower targetGood
    | emptyRecord => exact lift_old_weak pool _ (CommonBoundRefInspection.width_weak pool source sourceGood)
    | required label payload =>
        apply lift_old_weak
        apply CommonBoundRefInspection.required_weak pool source sourceGood
        exact ⟨CommonOptionalPoolQueries.required_query pool label payload member,
          by simpa only [PayloadUpper, Pool.child, Pool.termAt_reference,
            PresenceGeneratedChildGrammar.upper] using good⟩
    | base scalar => exact rigid_weak pool source sourceGood (.base scalar) trivial targetRef targetGood
    | pair first last =>
        apply rigid_weak pool source sourceGood _ _ targetRef targetGood
        simpa only [RigidGrammar, OriginalUpper, Pool.child, Pool.termAt_reference,
          PresenceGeneratedChildGrammar.upper, Bool.and_eq_true] using good
    | arrow input incoming output outgoing =>
        apply rigid_weak pool source sourceGood _ _ targetRef targetGood
        simpa only [RigidGrammar, OriginalUpper, Pool.child, Pool.termAt_reference,
          PresenceGeneratedChildGrammar.upper, Bool.and_eq_true] using good
    | _ => cases good
  | variant good =>
      apply rigid_weak pool source sourceGood _ _ targetRef targetGood
      exact CommonBoundRefInspection.child_original_upper pool _ member _ (by simp [subterms]) good
  | @optional payload label good =>
      apply lift_old_weak
      apply CommonBoundRefInspection.optional_weak pool source sourceGood
      have requiredMember : .required label payload ∈ pool.terms :=
        pool.closed _ member _ (by simp [subterms])
      exact ⟨CommonOptionalPoolQueries.required_query pool label payload requiredMember,
        by simpa only [PayloadUpper, Pool.child, Pool.termAt_reference] using good⟩

theorem dispatch_weak (pool : Pool m) (sourceRef : Ref pool) (source : PoolSource pool)
    (sourceLower : LowerRef pool sourceRef) (sourceGood : SourceGrammar pool source)
    (target : Ref pool) (targetGood : UpperRef pool target) :
    OutputWeak pool (dispatch pool sourceRef source target) := by
  cases target with
  | original index =>
      exact dispatchOriginal_weak pool sourceRef source sourceLower sourceGood _ _ _ targetGood targetGood
  | _ =>
      simp only [dispatch]
      apply lift_old_weak
      apply CommonBoundRefInspection.dispatch_weak pool sourceRef source sourceLower sourceGood
      exact targetGood

theorem inspected_child_polarity (pool : Pool m) (source target : Ref pool)
    (first : LowerRef pool source) (last : UpperRef pool target)
    (branch : List (InputCheck pool)) (returned : branch ∈ inspect pool source target)
    (childSource childTarget : Ref pool) (included : edge childSource childTarget ∈ branch) :
    LowerRef pool childSource ∧ UpperRef pool childTarget := by
  obtain ⟨layer, found⟩ := CommonBoundRefInspection.sourceLayer_some pool source first
  have weak := dispatch_weak pool source layer first
    (CommonBoundRefInspection.sourceLayer_grammar pool source first layer found) target last
  have original := CommonBoundRefInspection.mem_prune _ branch returned
  simp only [found] at original
  rcases weak branch original _ included with good | dead
  · exact good
  · have alive := CommonBoundRefInspection.prune_unblocked _ branch returned _ included
    rw [alive] at dead
    cases dead

end Yulang.CommonPatternBoundInspection
