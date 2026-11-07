import Yulang.CommonPatternBoundWorklist
import Yulang.CommonFiniteBoundEncoding

/-! Finite-observation soundness and same-depth source descent for the actual
pattern dispatcher. These feed the clamped all-parameter proof. -/

namespace Yulang.CommonPatternFiniteInspection

open Common (Ty Row Equivalent)
open Core.PresenceGeneration (TyTerm)
open PresenceOpenTailGenerationLowering (Pool subterms)
open CommonPresenceConstraintGraph (rowEval lowerNode Realizes)
open CommonSymbolicBoundInspection
open CommonBoundRefInspection (Ref InputCheck sourceLayer)
open CommonGeneratedBoundInspection (PoolSource)
open CommonFiniteChildInspection (BelowAt)
open CommonFiniteBoundInspection (NeedsCurrent BranchAtSource)
open CommonFiniteBoundRefInspection (RigidRef current BranchAtRef below_congr)
open CommonGeneratedRigidDescent (weight rigid)
open CommonOptionalBoundEncoding (term)

variable {m : Nat}

theorem optional_layer_equivalent (pool : Pool m) (label : Nat) (payload : TyTerm (Fin m))
    (member : .union .exactEmpty (.required label payload) ∈ pool.terms)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) (realizes : Realizes pool rows values) :
    Equivalent
      ((BoundRef.optional label (some (pool.child _ member payload (by simp [subterms])))).eval values)
      ((lowerNode pool _ member).eval rows values) := by
  have empty := CommonPresenceConstraintGraph.realizes_reference pool rows values realizes .exactEmpty
    (pool.closed _ member _ (by simp [subterms]))
  have required := CommonPresenceConstraintGraph.realizes_reference pool rows values realizes
    (.required label payload) (pool.closed _ member _ (by simp [subterms]))
  exact ⟨Common.common_union_mono empty.1 required.1, Common.common_union_mono empty.2 required.2⟩

theorem dispatchOriginal_at_sound (depth : Nat) (pool : Pool m)
    (sourceRef : Ref pool) (source : PoolSource pool)
    (target : TyTerm (Fin m)) (member : target ∈ pool.terms) (targetRef : Ref pool)
    (targetRigid : rigid target) (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (realizes : Realizes pool rows values)
    (sourceSame : Equivalent (source.eval (rowEval rows) values) (sourceRef.eval values))
    (targetSame : Equivalent ((lowerNode pool target member).eval rows values) (targetRef.eval values))
    (branch : List (InputCheck pool))
    (returned : branch ∈ CommonPatternBoundInspection.dispatchOriginal pool sourceRef source target member targetRef)
    (valid : BranchAtSource depth (rowEval rows) values source branch) :
    BelowAt depth (sourceRef.eval values) (targetRef.eval values) := by
  unfold CommonPatternBoundInspection.dispatchOriginal at returned
  split at returned
  · rename_i tag payload equal
    apply (below_congr depth sourceSame targetSame).mp
    exact CommonFiniteBoundInspection.rigid_at_sound depth (rowEval rows) values source
      (.variant tag (.original (pool.child (.variant tag payload) (by assumption) payload
        (by simp [subterms])))) targetRef targetSame branch returned valid
  · rename_i label payload equal
    have layer := optional_layer_equivalent pool label payload equal rows values realizes
    exact (below_congr depth sourceSame (Common.equivalent_trans layer targetSame)).mp
      (CommonFiniteBoundInspection.optional_at_sound _ _ _ _ _ _ _ returned valid)
  · exact CommonFiniteBoundRefInspection.dispatchOriginal_at_sound depth pool sourceRef source
      target member targetRef targetRigid rows values sourceSame targetSame branch returned valid

theorem dispatch_at_sound (depth : Nat) (pool : Pool m) (sourceRef : Ref pool)
    (source : PoolSource pool) (target : Ref pool) (targetRigid : RigidRef pool target)
    (rows : Fin m → Row) (values : Fin pool.size → Ty) (realizes : Realizes pool rows values)
    (sourceSame : Equivalent (source.eval (rowEval rows) values) (sourceRef.eval values))
    (branch : List (InputCheck pool))
    (returned : branch ∈ CommonPatternBoundInspection.dispatch pool sourceRef source target)
    (valid : BranchAtSource depth (rowEval rows) values source branch) :
    BelowAt depth (sourceRef.eval values) (target.eval values) := by
  cases target with
  | original index =>
      exact dispatchOriginal_at_sound depth pool sourceRef source
        (pool.termAt index) (pool.at_mem index) (.original index) targetRigid rows values realizes
        sourceSame (realizes index) branch returned valid
  | _ =>
      simp only [CommonPatternBoundInspection.dispatch] at returned
      exact CommonFiniteBoundRefInspection.dispatch_at_sound depth pool sourceRef source _ targetRigid
        rows values realizes sourceSame branch returned valid

theorem inspect_at_sound (depth : Nat) (pool : Pool m) (source target : Ref pool)
    (targetRigid : RigidRef pool target) (rows : Fin m → Row) (values : Fin pool.size → Ty)
    (realizes : Realizes pool rows values) (branch : List (InputCheck pool))
    (returned : branch ∈ CommonPatternBoundInspection.inspect pool source target)
    (valid : BranchAtRef depth pool rows values source branch) :
    BelowAt depth (source.eval values) (target.eval values) := by
  have original := CommonBoundRefInspection.mem_prune _ branch returned
  cases found : sourceLayer pool source with
  | none => simp only [found, List.not_mem_nil] at original
  | some layer =>
      apply dispatch_at_sound depth pool source layer target targetRigid rows values realizes
        (CommonBoundRefInspection.sourceLayer_exact pool source layer found rows values realizes) branch
        (by simpa only [found] using original)
      simpa only [BranchAtRef, current, found, BranchAtSource] using valid

theorem dispatchOriginal_current_sources (pool : Pool m) (sourceRef : Ref pool)
    (source : PoolSource pool) (target : TyTerm (Fin m)) (member : target ∈ pool.terms)
    (targetRef : Ref pool) (targetRigid : rigid target) (requested : NeedsCurrent source = true)
    (branch : List (InputCheck pool))
    (returned : branch ∈ CommonPatternBoundInspection.dispatchOriginal pool sourceRef source target member targetRef)
    (first last : Ref pool) (included : edge first last ∈ branch) :
    first ∈ CommonBoundInspectionDescent.currentSources source := by
  unfold CommonPatternBoundInspection.dispatchOriginal at returned
  split at returned
  · exact CommonBoundInspectionDescent.rigid_current_sources source _ targetRef requested
      branch returned first last included
  · exact CommonBoundInspectionDescent.optional_current_sources source _ _ branch returned first last included
  · exact CommonFiniteBoundRefInspection.dispatchOriginal_current_sources pool sourceRef source target member
      targetRef targetRigid requested branch returned first last included

theorem dispatch_current_sources (pool : Pool m) (sourceRef : Ref pool)
    (source : PoolSource pool) (target : Ref pool) (targetRigid : RigidRef pool target)
    (requested : NeedsCurrent source = true) (branch : List (InputCheck pool))
    (returned : branch ∈ CommonPatternBoundInspection.dispatch pool sourceRef source target)
    (first last : Ref pool) (included : edge first last ∈ branch) :
    first ∈ CommonBoundInspectionDescent.currentSources source := by
  cases target with
  | original index =>
      exact dispatchOriginal_current_sources pool sourceRef source
        (pool.termAt index) (pool.at_mem index) (.original index) targetRigid requested branch returned first last included
  | _ =>
      simp only [CommonPatternBoundInspection.dispatch] at returned
      exact CommonFiniteBoundRefInspection.dispatch_current_sources pool sourceRef source _ targetRigid
        requested branch returned first last included

theorem inspect_current_decreases (pool : Pool m) (source target : Ref pool)
    (sourceRigid : RigidRef pool source) (targetRigid : RigidRef pool target)
    (requested : current pool source = true) (branch : List (InputCheck pool))
    (returned : branch ∈ CommonPatternBoundInspection.inspect pool source target) (first last : Ref pool)
    (included : edge first last ∈ branch) :
    weight (term pool first) < weight (term pool source) := by
  have original := CommonBoundRefInspection.mem_prune _ branch returned
  cases found : sourceLayer pool source with
  | none => simp only [found, List.not_mem_nil] at original
  | some layer =>
      have requestedLayer : NeedsCurrent layer = true := by
        simpa only [current, found] using requested
      have inside := dispatch_current_sources pool source layer target targetRigid requestedLayer branch
        (by simpa only [found] using original) first last included
      cases source with
      | original index =>
          exact CommonFiniteBoundRefInspection.smaller_term pool (pool.termAt index) first
            (CommonBoundInspectionDescent.node_current_sources_smaller pool
              (pool.termAt index) (pool.at_mem index) layer found sourceRigid requestedLayer first inside)
      | top => cases found; cases requestedLayer
      | _ => cases found

open CommonOptionalPool (Query extend restrictValues)
open CommonOptionalBoundEncoding (encode encodeBranch encodeCheck)
open CommonSymbolicBoundSupport (Supported BranchSupported)
open CommonFiniteChildInspection (BranchAt)
open CommonSymbolicConstraints (Check)

theorem encoded_inspect_at_sound (depth : Nat) (pool : Pool m) (queries : List (Query pool))
    (source target : Ref pool)
    (sourceSupported : Supported queries source) (targetSupported : Supported queries target)
    (targetRigid : RigidRef pool target) (rows : Fin m → Row)
    (values : Fin (extend pool queries).size → Ty) (realizes : Realizes (extend pool queries) rows values)
    (branch : List (InputCheck pool)) (returned : branch ∈ CommonPatternBoundInspection.inspect pool source target)
    (supported : BranchSupported queries branch)
    (guarded : BranchAt false depth (rowEval rows) values values (encodeBranch pool queries branch supported))
    (sameDepth : current pool source = true →
      BranchAt true depth (rowEval rows) values values (encodeBranch pool queries branch supported)) :
    BelowAt depth (values (encode pool queries source sourceSupported))
      (values (encode pool queries target targetSupported)) := by
  apply (below_congr depth (CommonOptionalBoundEncoding.encode_exact pool queries rows values realizes source sourceSupported)
    (CommonOptionalBoundEncoding.encode_exact pool queries rows values realizes target targetSupported)).mpr
  apply inspect_at_sound depth pool source target targetRigid rows
    (restrictValues pool queries values) (CommonOptionalPool.restrict_realizes pool queries rows values realizes)
    branch returned
  exact ⟨(CommonFiniteBoundEncoding.encodeBranch_at_exact false depth pool queries rows values realizes branch supported).mp guarded,
    fun requested => (CommonFiniteBoundEncoding.encodeBranch_at_exact true depth pool queries rows values realizes branch supported).mp
      (sameDepth requested)⟩

theorem encoded_inspect_current_decreases (pool : Pool m) (queries : List (Query pool))
    (source target : Ref pool) (sourceSupported : Supported queries source)
    (sourceRigid : RigidRef pool source) (targetRigid : RigidRef pool target)
    (requested : current pool source = true)
    (branch : List (InputCheck pool)) (returned : branch ∈ CommonPatternBoundInspection.inspect pool source target)
    (supported : BranchSupported queries branch) (first last : Fin (extend pool queries).size)
    (included : Check.childBelow (.ref first) (.ref last) ∈ encodeBranch pool queries branch supported) :
    weight ((extend pool queries).termAt first) <
      weight ((extend pool queries).termAt (encode pool queries source sourceSupported)) := by
  obtain ⟨⟨check, member⟩, _, same⟩ := List.mem_map.mp included
  have allowed := supported check member
  cases check with
  | childBelow firstPayload lastPayload =>
      cases firstPayload with
      | ref childSource =>
          cases lastPayload with
          | ref childTarget =>
              simp only [encodeCheck, Check.childBelow.injEq, CommonPayloadProjection.Payload.ref.injEq] at same
              rcases same with ⟨rfl, rfl⟩
              simpa only [CommonOptionalBoundEncoding.termAt_encode] using
                inspect_current_decreases pool source target sourceRigid targetRigid requested
                  branch returned childSource childTarget member
          | _ => cases allowed
      | _ => cases allowed
  | rowBelow => cases same
  | flag expression =>
      cases expression
      case literal => cases same
      all_goals cases allowed
  | profileBelow => cases allowed

end Yulang.CommonPatternFiniteInspection
