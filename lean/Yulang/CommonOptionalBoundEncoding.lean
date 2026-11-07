import Yulang.CommonGeneratedBoundSupport
import Yulang.CommonCanonicalShapes

/-!
# Encoding fixed bound references into the extended shared pool

The optional-bound inspector uses symbolic references before any values are
supplied. This module replaces those references with actual finite pool IDs.
Support proofs concern only the finite query inventory and disappear from
the computation. Every original ID keeps its numerical value.

For arbitrary independent rows and every constructor realizer of the
extended pool, the encoded checks have exactly the original meaning. This
is a representation theorem; it does not assert that every encoded branch
has an unrestricted parameter solution.
-/

namespace Yulang.CommonOptionalBoundEncoding

open Core.PresenceGeneration (TyTerm RowTerm)
open PresenceOpenTailGenerationLowering (Pool)
open CommonOptionalPool (Query extend embed restrictValues)
open CommonSymbolicBoundInspection (BoundRef payloadValue)
open CommonSymbolicBoundSupport (Supported CheckSupported BranchSupported OutputSupported)
open CommonSymbolicConstraints (Check Branch Alternatives)
open CommonPresenceConstraintGraph (Realizes evaluate restrict rowEval)

variable {m : Nat}

def term (pool : Pool m) : BoundRef (Fin pool.size) → TyTerm (Fin m)
  | .original index => pool.termAt index
  | .top => .top
  | .width => .emptyRecord
  | .exactEmpty => .exactEmpty
  | .required label payload => CommonOptionalPool.requiredTerm pool (label, payload)
  | .optional label payload => CommonOptionalPool.optionalTerm pool (label, payload)

theorem term_member (pool : Pool m) (queries : List (Query pool))
    (reference : BoundRef (Fin pool.size)) (supported : Supported queries reference) :
    term pool reference ∈ (extend pool queries).terms := by
  cases reference with
  | original index => exact CommonOptionalPool.original_member pool queries _ (pool.at_mem index)
  | top | width | exactEmpty =>
      exact CommonOptionalPool.candidate_member pool queries _ (by simp [term, CommonOptionalPool.candidates])
  | required label payload =>
      exact CommonOptionalPool.candidate_member pool queries _
        (CommonOptionalPool.required_candidate pool queries (label, payload) supported)
  | optional label payload =>
      exact CommonOptionalPool.candidate_member pool queries _
        (CommonOptionalPool.optional_candidate pool queries (label, payload) supported)

def encode (pool : Pool m) (queries : List (Query pool))
    (reference : BoundRef (Fin pool.size)) (supported : Supported queries reference) :
    Fin (extend pool queries).size :=
  (extend pool queries).reference (term pool reference) (term_member pool queries reference supported)

@[simp] theorem termAt_encode (pool : Pool m) (queries : List (Query pool))
    (reference : BoundRef (Fin pool.size)) (supported : Supported queries reference) :
    (extend pool queries).termAt (encode pool queries reference supported) = term pool reference :=
  Pool.termAt_reference _ _ _

@[simp] theorem encode_original (pool : Pool m) (queries : List (Query pool))
    (index : Fin pool.size) (supported : Supported queries (.original index)) :
    encode pool queries (.original index) supported = embed pool queries index := rfl

@[simp] theorem encode_original_val (pool : Pool m) (queries : List (Query pool))
    (index : Fin pool.size) (supported : Supported queries (.original index)) :
    (encode pool queries (.original index) supported).val = index.val :=
  CommonOptionalPool.embed_val pool queries index

theorem payload_evaluate_exact (pool : Pool m) (rows : Fin m → Common.Row)
    (values : Fin pool.size → Common.Ty) (realizes : Realizes pool rows values)
    (label : Nat) (payload : Option (Fin pool.size)) :
    Common.Equivalent
      (evaluate rows (restrict pool values) (CommonOptionalPool.payloadTerm pool (label, payload)))
      (payloadValue values payload) := by
  cases payload with
  | none => exact Common.equivalent_refl _
  | some index =>
      have same := CommonPresenceConstraintGraph.realizes_evaluate pool rows values realizes
        (pool.termAt index) (pool.at_mem index)
      rw [Pool.reference_termAt] at same
      exact Common.equivalent_symm same

theorem term_evaluate_exact (pool : Pool m) (rows : Fin m → Common.Row)
    (values : Fin pool.size → Common.Ty) (realizes : Realizes pool rows values)
    (reference : BoundRef (Fin pool.size)) :
    Common.Equivalent (evaluate rows (restrict pool values) (term pool reference))
      (reference.eval values) := by
  cases reference with
  | original index =>
      have same := CommonPresenceConstraintGraph.realizes_evaluate pool rows values realizes
        (pool.termAt index) (pool.at_mem index)
      rw [Pool.reference_termAt] at same
      exact Common.equivalent_symm same
  | top | width | exactEmpty => exact Common.equivalent_refl _
  | required label payload =>
      exact (CommonCanonicalShapes.required_equivalent_iff label _ _).mpr
        (payload_evaluate_exact pool rows values realizes label payload)
  | optional label payload =>
      exact CommonCanonicalShapes.union_congr (Common.equivalent_refl _)
        ((CommonCanonicalShapes.required_equivalent_iff label _ _).mpr
          (payload_evaluate_exact pool rows values realizes label payload))

/-- The graph equations alone identify every encoded reference, including
arbitrary original var/mask/regular values. -/
theorem encode_exact (pool : Pool m) (queries : List (Query pool))
    (rows : Fin m → Common.Row) (values : Fin (extend pool queries).size → Common.Ty)
    (realizes : Realizes (extend pool queries) rows values)
    (reference : BoundRef (Fin pool.size)) (supported : Supported queries reference) :
    Common.Equivalent (values (encode pool queries reference supported))
      (reference.eval (restrictValues pool queries values)) := by
  have same := CommonPresenceConstraintGraph.realizes_evaluate (extend pool queries)
    rows values realizes (term pool reference) (term_member pool queries reference supported)
  rw [CommonOptionalPool.restrict_inputs] at same
  exact Common.equivalent_trans same (term_evaluate_exact pool rows _
    (CommonOptionalPool.restrict_realizes pool queries rows values realizes) reference)

abbrev InputCheck (pool : Pool m) :=
  Check (RowTerm (Fin m)) (Fin pool.size) (BoundRef (Fin pool.size))

abbrev EncodedCheck (pool : Pool m) (queries : List (Query pool)) :=
  Check (RowTerm (Fin m)) (Fin (extend pool queries).size) (Fin (extend pool queries).size)

def encodeCheck (pool : Pool m) (queries : List (Query pool)) :
    (check : InputCheck pool) → CheckSupported queries check → EncodedCheck pool queries
  | .childBelow (.ref source) (.ref target), supported =>
      .childBelow (.ref (encode pool queries source supported.1))
        (.ref (encode pool queries target supported.2))
  | .rowBelow source target, _ => .rowBelow source target
  | .flag (.literal value), _ => .flag (.literal value)
  | .childBelow .bottom _, impossible => False.elim impossible
  | .childBelow .top _, impossible => False.elim impossible
  | .childBelow (.union _ _) _, impossible => False.elim impossible
  | .childBelow (.inter _ _) _, impossible => False.elim impossible
  | .childBelow (.ref _) .bottom, impossible => False.elim impossible
  | .childBelow (.ref _) .top, impossible => False.elim impossible
  | .childBelow (.ref _) (.union _ _), impossible => False.elim impossible
  | .childBelow (.ref _) (.inter _ _), impossible => False.elim impossible
  | .flag (.atom _), impossible => False.elim impossible
  | .flag (.and _ _), impossible => False.elim impossible
  | .flag (.or _ _), impossible => False.elim impossible
  | .flag (.not _), impossible => False.elim impossible
  | .profileBelow _ _, impossible => False.elim impossible

theorem encodeCheck_exact (pool : Pool m) (queries : List (Query pool))
    (rows : Fin m → Common.Row) (values : Fin (extend pool queries).size → Common.Ty)
    (realizes : Realizes (extend pool queries) rows values)
    (check : InputCheck pool) (supported : CheckSupported queries check) :
    (encodeCheck pool queries check supported).Holds (rowEval rows) values values ↔
      check.Holds (rowEval rows) (restrictValues pool queries values)
        (BoundRef.eval (restrictValues pool queries values)) := by
  cases check with
  | childBelow source target =>
      cases source <;> cases target
      all_goals first
      | exact False.elim supported
      | exact CommonSymbolicBoundInspection.subtype_congr
          (encode_exact pool queries rows values realizes _ supported.1)
          (encode_exact pool queries rows values realizes _ supported.2)
  | rowBelow => rfl
  | flag expression =>
      cases expression
      case literal => rfl
      all_goals exact False.elim supported
  | profileBelow => cases supported

def encodeBranch (pool : Pool m) (queries : List (Query pool))
    (branch : List (InputCheck pool)) (supported : BranchSupported queries branch) :
    List (EncodedCheck pool queries) :=
  branch.attach.map (fun check => encodeCheck pool queries check.val (supported check.val check.property))

theorem encodeBranch_exact (pool : Pool m) (queries : List (Query pool))
    (rows : Fin m → Common.Row) (values : Fin (extend pool queries).size → Common.Ty)
    (realizes : Realizes (extend pool queries) rows values)
    (branch : List (InputCheck pool)) (supported : BranchSupported queries branch) :
    Branch.Holds (rowEval rows) values values (encodeBranch pool queries branch supported) ↔
      Branch.Holds (rowEval rows) (restrictValues pool queries values)
        (BoundRef.eval (restrictValues pool queries values)) branch := by
  constructor
  · intro accepted check included
    exact (encodeCheck_exact pool queries rows values realizes check (supported check included)).mp
      (accepted _ (List.mem_map.mpr ⟨⟨check, included⟩, List.mem_attach _ _, rfl⟩))
  · intro accepted check included
    obtain ⟨⟨original, member⟩, _, rfl⟩ := List.mem_map.mp included
    exact (encodeCheck_exact pool queries rows values realizes original (supported original member)).mpr
      (accepted original member)

def encodeOutput (pool : Pool m) (queries : List (Query pool))
    (output : List (List (InputCheck pool))) (supported : OutputSupported queries output) :
    List (List (EncodedCheck pool queries)) :=
  output.attach.map (fun branch => encodeBranch pool queries branch.val (supported branch.val branch.property))

theorem encodeOutput_exact (pool : Pool m) (queries : List (Query pool))
    (rows : Fin m → Common.Row) (values : Fin (extend pool queries).size → Common.Ty)
    (realizes : Realizes (extend pool queries) rows values)
    (output : List (List (InputCheck pool))) (supported : OutputSupported queries output) :
    Alternatives.Holds (rowEval rows) values values (encodeOutput pool queries output supported) ↔
      CommonSymbolicBoundInspection.Holds (rowEval rows) (restrictValues pool queries values) output := by
  constructor
  · rintro ⟨branch, included, accepted⟩
    obtain ⟨⟨original, member⟩, _, rfl⟩ := List.mem_map.mp included
    exact ⟨original, member,
      (encodeBranch_exact pool queries rows values realizes original (supported original member)).mp accepted⟩
  · rintro ⟨original, member, accepted⟩
    exact ⟨_, List.mem_map.mpr ⟨⟨original, member⟩, List.mem_attach _ _, rfl⟩,
      (encodeBranch_exact pool queries rows values realizes original (supported original member)).mpr accepted⟩

end Yulang.CommonOptionalBoundEncoding
