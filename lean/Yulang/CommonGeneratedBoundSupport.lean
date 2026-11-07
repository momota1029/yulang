import Yulang.CommonSymbolicBoundSupport
import Yulang.CommonGeneratedBoundInspection
import Yulang.CommonOptionalPoolQueries

/-!
# The initial bound inspector stays in the original pool query inventory

Every required target in the original shared pool contributes its own
payload query and a top-payload query. The fixed bound inspector uses only
those queries and the existing source child IDs. The support theorems here
are unconditional syntax facts; they do not inspect rows, values, model
certificates, or successful branches.

This establishes support for ordinary target inspection and selected
optional targets in the original pool. It is not a theorem that arbitrary
new graphs or repeated saturation steps remain within this inventory.
-/

namespace Yulang.CommonGeneratedBoundSupport

open Core.PresenceGeneration (TyTerm)
open PresenceOpenTailGenerationLowering (Pool subterms)
open CommonSymbolicBoundInspection
open CommonSymbolicBoundSupport
open CommonGeneratedBoundInspection
open CommonOptionalPoolQueries (queries)

variable {m : Nat}

theorem queries_top_closed (pool : Pool m) : TopClosed (queries pool) := by
  intro label payload member
  exact CommonOptionalPoolQueries.top_query_closed pool (label, payload) member

/-- Parsing an original node introduces only original child references and
constants, so it is supported by every query inventory, including empty. -/
theorem ofNode_supported (pool : Pool m) (inventory : List (Query (Fin pool.size)))
    (term : TyTerm (Fin m)) (member : term ∈ pool.terms) (source : PoolSource pool)
    (found : ofNode pool term member = some source) : SourceSupported inventory source := by
  cases term <;> simp only [ofNode] at found <;> cases found <;> simp

theorem withNode_supported (pool : Pool m) (inventory : List (Query (Fin pool.size)))
    (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (inspector : PoolSource pool → PoolOutput pool)
    (supported : ∀ source, ofNode pool term member = some source → OutputSupported inventory (inspector source)) :
    OutputSupported inventory (withNode pool term member inspector) := by
  cases found : ofNode pool term member with
  | none => simp [withNode, found, OutputSupported]
  | some source => simpa only [withNode, found] using supported source found

theorem required_supported (pool : Pool m) (inventory : List (Query (Fin pool.size)))
    (closed : TopClosed inventory) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (label : Nat) (payload : Option (Fin pool.size)) (selected : (label, payload) ∈ inventory) :
    OutputSupported inventory (required pool term member label payload) :=
  withNode_supported pool inventory term member _ (fun source found =>
    inspect_required_supported inventory closed source label payload
      (ofNode_supported pool inventory term member source found) selected)

theorem optional_supported (pool : Pool m) (inventory : List (Query (Fin pool.size)))
    (closed : TopClosed inventory) (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (label : Nat) (payload : Option (Fin pool.size)) (selected : (label, payload) ∈ inventory) :
    OutputSupported inventory (optional pool term member label payload) :=
  withNode_supported pool inventory term member _ (fun source found =>
    inspect_optional_supported inventory closed source label payload
      (ofNode_supported pool inventory term member source found) selected)

theorem width_supported (pool : Pool m) (inventory : List (Query (Fin pool.size)))
    (term : TyTerm (Fin m)) (member : term ∈ pool.terms) :
    OutputSupported inventory (width pool term member) :=
  withNode_supported pool inventory term member _ (fun source found =>
    inspect_width_supported inventory source (ofNode_supported pool inventory term member source found))

theorem rigid_supported (pool : Pool m) (inventory : List (Query (Fin pool.size)))
    (term : TyTerm (Fin m)) (member : term ∈ pool.terms)
    (target : PoolRigid pool) (targetRef : BoundRef (Fin pool.size))
    (targetSupported : RigidSupported inventory target) (referenceSupported : Supported inventory targetRef) :
    OutputSupported inventory (rigid pool term member target targetRef) :=
  withNode_supported pool inventory term member _ (fun source found =>
    inspect_rigid_supported inventory source target targetRef
      (ofNode_supported pool inventory term member source found) targetSupported referenceSupported)

/-- In particular, any original required target supplies every optional and
presence-test reference emitted while inspecting its source. -/
theorem required_target_supported (pool : Pool m) (source : TyTerm (Fin m))
    (sourceMember : source ∈ pool.terms) (label : Nat) (payload : TyTerm (Fin m))
    (targetMember : TyTerm.required label payload ∈ pool.terms) :
    OutputSupported (queries pool) (required pool source sourceMember label
      (some (pool.child _ targetMember payload (by simp [subterms])))) :=
  required_supported pool (queries pool) (queries_top_closed pool) source sourceMember label _
    (CommonOptionalPoolQueries.required_query pool label payload targetMember)

theorem optional_target_supported (pool : Pool m) (source : TyTerm (Fin m))
    (sourceMember : source ∈ pool.terms) (label : Nat) (payload : TyTerm (Fin m))
    (targetMember : TyTerm.required label payload ∈ pool.terms) :
    OutputSupported (queries pool) (optional pool source sourceMember label
      (some (pool.child _ targetMember payload (by simp [subterms])))) :=
  optional_supported pool (queries pool) (queries_top_closed pool) source sourceMember label _
    (CommonOptionalPoolQueries.required_query pool label payload targetMember)

theorem optional_query_supported (pool : Pool m) (source : TyTerm (Fin m))
    (sourceMember : source ∈ pool.terms) (query : Query (Fin pool.size))
    (selected : query ∈ queries pool) :
    OutputSupported (queries pool) (optional pool source sourceMember query.1 query.2) :=
  optional_supported pool (queries pool) (queries_top_closed pool) source sourceMember _ _ selected

theorem required_query_supported (pool : Pool m) (source : TyTerm (Fin m))
    (sourceMember : source ∈ pool.terms) (query : Query (Fin pool.size))
    (selected : query ∈ queries pool) :
    OutputSupported (queries pool) (required pool source sourceMember query.1 query.2) :=
  required_supported pool (queries pool) (queries_top_closed pool) source sourceMember _ _ selected

/-- All original-pool ordinary target outputs fit the fixed inventory. No
endpoint-shape, assignment, realization, or branch-success premise is used. -/
theorem inspect_supported (pool : Pool m) (source target : TyTerm (Fin m))
    (sourceMember : source ∈ pool.terms) (targetMember : target ∈ pool.terms) :
    OutputSupported (queries pool) (inspect pool source target sourceMember targetMember) := by
  cases target with
  | var => simp [inspect, OutputSupported, BranchSupported, edge]
  | emptyRecord => exact width_supported _ _ _ _
  | required label payload => exact required_target_supported pool source sourceMember label payload targetMember
  | base | pair | arrow | bottom | variant =>
      apply rigid_supported <;> simp
  | top | exactEmpty | union | inter | record | recordDefault => simp [inspect, OutputSupported, BranchSupported]

end Yulang.CommonGeneratedBoundSupport
