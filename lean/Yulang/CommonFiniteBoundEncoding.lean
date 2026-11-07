import Yulang.CommonFiniteBoundRefInspection
import Yulang.CommonClampedSelectedSoundness

/-!
# Finite bound inspection on actual extended-pool IDs

Supported symbolic references are encoded by the existing actual-pool
encoder. Both finite child interpretations commute with this encoding for
every independent constructor realizer. The same selected branch therefore
supplies finite inspection and strict source descent to the clamped proof.

The measure is exactly the weight of the extended pool's source term.
Neither an assigned regular type nor a constructor-equation unfolding is
used as a measure. The encoder may share equal constructor terms; none of
the arguments require injectivity of symbolic bound references.
-/

namespace Yulang.CommonFiniteBoundEncoding

open Common (Ty Row)
open PresenceOpenTailGenerationLowering (Pool)
open CommonPresenceConstraintGraph (Realizes rowEval)
open CommonOptionalPool (Query extend restrictValues)
open CommonOptionalBoundEncoding
open CommonSymbolicBoundInspection (BoundRef)
open CommonSymbolicBoundSupport (Supported CheckSupported BranchSupported)
open CommonSymbolicConstraints (Check)
open CommonFiniteChildInspection (BelowAt CheckAt BranchAt)
open CommonFiniteBoundRefInspection (RigidRef current below_congr guarded_congr)
open CommonGeneratedRigidDescent (weight)

variable {m : Nat}

theorem encodeCheck_at_exact (sameDepth : Bool) (depth : Nat) (pool : Pool m)
    (queries : List (Query pool)) (rows : Fin m → Row)
    (values : Fin (extend pool queries).size → Ty) (realizes : Realizes (extend pool queries) rows values)
    (check : InputCheck pool) (supported : CheckSupported queries check) :
    CheckAt sameDepth depth (rowEval rows) values values (encodeCheck pool queries check supported) ↔
      CheckAt sameDepth depth (rowEval rows) (restrictValues pool queries values)
        (BoundRef.eval (restrictValues pool queries values)) check := by
  cases check with
  | childBelow source target =>
      cases source <;> cases target
      all_goals first
      | exact False.elim supported
      | cases sameDepth with
        | false =>
            exact guarded_congr depth
              (encode_exact pool queries rows values realizes _ supported.1)
              (encode_exact pool queries rows values realizes _ supported.2)
        | true =>
            exact below_congr depth
              (encode_exact pool queries rows values realizes _ supported.1)
              (encode_exact pool queries rows values realizes _ supported.2)
  | rowBelow => rfl
  | flag expression =>
      cases expression
      case literal => rfl
      all_goals exact False.elim supported
  | profileBelow => cases supported

theorem encodeBranch_at_exact (sameDepth : Bool) (depth : Nat) (pool : Pool m)
    (queries : List (Query pool)) (rows : Fin m → Row)
    (values : Fin (extend pool queries).size → Ty) (realizes : Realizes (extend pool queries) rows values)
    (branch : List (InputCheck pool)) (supported : BranchSupported queries branch) :
    BranchAt sameDepth depth (rowEval rows) values values (encodeBranch pool queries branch supported) ↔
      BranchAt sameDepth depth (rowEval rows) (restrictValues pool queries values)
        (BoundRef.eval (restrictValues pool queries values)) branch := by
  constructor
  · intro accepted check included
    exact (encodeCheck_at_exact sameDepth depth pool queries rows values realizes check (supported check included)).mp
      (accepted _ (List.mem_map.mpr ⟨⟨check, included⟩, List.mem_attach _ _, rfl⟩))
  · intro accepted check included
    obtain ⟨⟨original, member⟩, _, rfl⟩ := List.mem_map.mp included
    exact (encodeCheck_at_exact sameDepth depth pool queries rows values realizes original
      (supported original member)).mpr (accepted original member)

/-- Every actual returned bound branch, interpreted on actual extended IDs.
The two finite branch hypotheses are later discharged by the clamped depth
and source-measure induction, rather than imposed on free parameters. -/
theorem encoded_inspect_at_sound (depth : Nat) (pool : Pool m) (queries : List (Query pool))
    (source target : CommonBoundRefInspection.Ref pool)
    (sourceSupported : Supported queries source) (targetSupported : Supported queries target)
    (targetRigid : RigidRef pool target) (rows : Fin m → Row)
    (values : Fin (extend pool queries).size → Ty) (realizes : Realizes (extend pool queries) rows values)
    (branch : List (InputCheck pool)) (returned : branch ∈ CommonBoundRefInspection.inspect pool source target)
    (supported : BranchSupported queries branch)
    (guarded : BranchAt false depth (rowEval rows) values values (encodeBranch pool queries branch supported))
    (sameDepth : current pool source = true →
      BranchAt true depth (rowEval rows) values values (encodeBranch pool queries branch supported)) :
    BelowAt depth (values (encode pool queries source sourceSupported))
      (values (encode pool queries target targetSupported)) := by
  apply (below_congr depth (encode_exact pool queries rows values realizes source sourceSupported)
    (encode_exact pool queries rows values realizes target targetSupported)).mpr
  apply CommonFiniteBoundRefInspection.inspect_at_sound depth pool source target targetRigid rows
    (restrictValues pool queries values) (CommonOptionalPool.restrict_realizes pool queries rows values realizes)
    branch returned
  exact ⟨(encodeBranch_at_exact false depth pool queries rows values realizes branch supported).mp guarded,
    fun requested => (encodeBranch_at_exact true depth pool queries rows values realizes branch supported).mp
      (sameDepth requested)⟩

theorem encodeCheck_ordinary (pool : Pool m) (queries : List (Query pool))
    (check : InputCheck pool) (supported : CheckSupported queries check) :
    CommonClampedSelectedSoundness.OrdinaryCheck (encodeCheck pool queries check supported) := by
  cases check with
  | childBelow source target =>
      cases source <;> cases target <;> first | trivial | cases supported
  | rowBelow => trivial
  | flag expression => cases expression <;> first | trivial | cases supported
  | profileBelow => cases supported

theorem encodeBranch_ordinary (pool : Pool m) (queries : List (Query pool))
    (branch : List (InputCheck pool)) (supported : BranchSupported queries branch) :
    ∀ check ∈ encodeBranch pool queries branch supported, CommonClampedSelectedSoundness.OrdinaryCheck check := by
  intro check included
  obtain ⟨⟨original, member⟩, _, rfl⟩ := List.mem_map.mp included
  exact encodeCheck_ordinary pool queries original (supported original member)

/-- Strict descent uses the exact syntax measure expected by the actual
extended-pool clamped solver. All returned encoded children are covered. -/
theorem encoded_inspect_current_decreases (pool : Pool m) (queries : List (Query pool))
    (source target : CommonBoundRefInspection.Ref pool)
    (sourceSupported : Supported queries source)
    (sourceRigid : RigidRef pool source) (targetRigid : RigidRef pool target)
    (requested : current pool source = true)
    (branch : List (InputCheck pool)) (returned : branch ∈ CommonBoundRefInspection.inspect pool source target)
    (supported : BranchSupported queries branch)
    (first last : Fin (extend pool queries).size)
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
              simpa only [termAt_encode] using
                CommonFiniteBoundRefInspection.inspect_current_decreases pool source target
                  sourceRigid targetRigid requested branch returned childSource childTarget member
          | _ => cases allowed
      | _ => cases allowed
  | rowBelow => cases same
  | flag expression =>
      cases expression
      case literal => cases same
      all_goals cases allowed
  | profileBelow => cases allowed

end Yulang.CommonFiniteBoundEncoding
