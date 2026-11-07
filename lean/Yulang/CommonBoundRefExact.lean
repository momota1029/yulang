import Yulang.CommonBoundRefPolarity

/-!
# Exactness of fixed bound-reference inspection

The interpretation is the same arbitrary original constructor realizer used
by the earlier source adapter. The explicit pool width invariant discharges
optional-tail premises. Static pruning removes only universally false edges.
The grammar hypotheses describe original syntax provenance and do not
restrict the common types assigned to variables, including regular graphs.

These are internal inspector theorems. Their grammar and width hypotheses
must be supplied from actual generation and preserved branch invariants;
they are not additional premises of a final public inference theorem.
-/

namespace Yulang.CommonBoundRefInspection

open Common (Ty Row Equivalent Subtype)
open Core.PresenceGeneration (TyTerm)
open PresenceOpenTailGenerationLowering (Pool subterms)
open CommonSymbolicBoundInspection
open CommonGeneratedBoundInspection (PoolSource)
open CommonPresenceConstraintGraph (rowEval lowerNode Realizes)
open CommonGeneratedWidth (PoolWidth)

variable {m : Nat}

theorem sourceLayer_exact (pool : Pool m) (reference : Ref pool) (source : PoolSource pool)
    (found : sourceLayer pool reference = some source)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) (realizes : Realizes pool rows values) :
    Equivalent (source.eval (rowEval rows) values) (reference.eval values) := by
  cases reference with
  | original index =>
      rw [CommonGeneratedBoundInspection.ofNode_eval pool (pool.termAt index) (pool.at_mem index)
        source found rows values]
      exact realizes index
  | top => cases found; exact Common.equivalent_refl _
  | _ => cases found

theorem sourceLayer_width (pool : Pool m) (reference : Ref pool) (source : PoolSource pool)
    (good : LowerRef pool reference) (found : sourceLayer pool reference = some source)
    (values : Fin pool.size → Ty) (widths : PoolWidth pool values) : LocalWidth values source := by
  cases reference with
  | original index =>
      have width := CommonGeneratedBoundWidth.nodeWidth_of_poolWidth pool values widths
        (pool.termAt index) (pool.at_mem index) (PresenceGeneratedChildGrammar.lower_head _ good)
      change CommonGeneratedBoundInspection.ofNode pool (pool.termAt index) (pool.at_mem index) = some source at found
      simpa only [CommonGeneratedBoundInspection.NodeWidth, found] using width
  | top => cases found; trivial
  | _ => cases good

theorem dispatchOriginal_exact (pool : Pool m) (sourceRef : Ref pool) (source : PoolSource pool)
    (target : TyTerm (Fin m)) (member : target ∈ pool.terms) (targetRef : Ref pool)
    (targetGrammar : PresenceGeneratedChildGrammar.upper target = true)
    (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (sourceSame : Equivalent (source.eval (rowEval rows) values) (sourceRef.eval values))
    (targetSame : Equivalent ((lowerNode pool target member).eval rows values) (targetRef.eval values)) :
    Holds (rowEval rows) values (dispatchOriginal pool sourceRef source target member targetRef) ↔
      Subtype (sourceRef.eval values) (targetRef.eval values) := by
  cases target with
  | var => exact holds_edge _ _ _ _
  | emptyRecord =>
      exact (inspect_width_exact (rowEval rows) values source).trans (subtype_congr sourceSame targetSame)
  | required label payload =>
      exact (inspect_required_exact (rowEval rows) values source label
        (some (pool.child _ member payload (by simp [subterms])))).trans
        (subtype_congr sourceSame targetSame)
  | base scalar =>
      exact (inspect_rigid_exact (rowEval rows) values source (.base scalar) targetRef targetSame).trans
        (subtype_congr sourceSame targetSame)
  | pair first last =>
      exact (inspect_rigid_exact (rowEval rows) values source
        (.pair (.original (pool.child _ member first (by simp [subterms])))
          (.original (pool.child _ member last (by simp [subterms])))) targetRef targetSame).trans
        (subtype_congr sourceSame targetSame)
  | arrow input incoming output outgoing =>
      exact (inspect_rigid_exact (rowEval rows) values source
        (.arrow (.original (pool.child _ member input (by simp [subterms]))) incoming
          (.original (pool.child _ member output (by simp [subterms]))) outgoing) targetRef targetSame).trans
        (subtype_congr sourceSame targetSame)
  | _ => cases targetGrammar

theorem dispatch_exact (pool : Pool m) (sourceRef : Ref pool) (source : PoolSource pool)
    (target : Ref pool) (targetGood : UpperRef pool target)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) (realizes : Realizes pool rows values)
    (sourceSame : Equivalent (source.eval (rowEval rows) values) (sourceRef.eval values))
    (sourceWidth : LocalWidth values source) :
    Holds (rowEval rows) values (dispatch pool sourceRef source target) ↔
      Subtype (sourceRef.eval values) (target.eval values) := by
  cases target with
  | original index =>
      exact dispatchOriginal_exact pool sourceRef source (pool.termAt index) (pool.at_mem index)
        (.original index) targetGood rows values sourceSame (realizes index)
  | top =>
      simp only [dispatch, holds_success, BoundRef.eval, true_iff]
      exact CommonBoundCoalescing.le_top _
  | width =>
      exact (inspect_width_exact (rowEval rows) values source).trans
        (subtype_congr sourceSame (Common.equivalent_refl _))
  | required label payload =>
      exact (inspect_required_exact (rowEval rows) values source label payload).trans
        (subtype_congr sourceSame (Common.equivalent_refl _))
  | optional label payload =>
      exact (inspect_optional_exact (rowEval rows) values source label payload sourceWidth).trans
        (subtype_congr sourceSame (Common.equivalent_refl _))
  | exactEmpty => cases targetGood

/-- Exact for every independent row assignment and every original common
constructor realizer with the explicit pool width invariant. No inference
success, solver output, fuel, or previous worklist closure is a premise. -/
theorem inspect_exact (pool : Pool m) (source target : Ref pool)
    (first : LowerRef pool source) (last : UpperRef pool target)
    (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (realizes : Realizes pool rows values) (widths : PoolWidth pool values) :
    Holds (rowEval rows) values (inspect pool source target) ↔
      Subtype (source.eval values) (target.eval values) := by
  obtain ⟨layer, found⟩ := sourceLayer_some pool source first
  rw [inspect, prune_exact, rawInspect, found]
  exact dispatch_exact pool source layer target last rows values realizes
    (sourceLayer_exact pool source layer found rows values realizes)
    (sourceLayer_width pool source layer first found values widths)

end Yulang.CommonBoundRefInspection
