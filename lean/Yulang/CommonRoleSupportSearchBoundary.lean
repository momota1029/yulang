import Yulang.CommonRoleSupportSearch
import Yulang.CommonRoleFirstHitSupportBoundary

/-! A real fixed-receiver associated equation can disable its own first-hit
source support. This is an implementation boundary, NOT a language counterexample
or a decision to reject the source program. The finite search exposes the absence
of a self-supported candidate rather than silently retaining a stale equation. -/
namespace Yulang.CommonRoleSupportSearchBoundary
open CommonRoleFirstHitSupportBoundary
open CommonRoleSourceWorklist CommonRoleMaterializedDomain
open CommonRoleAssociatedStateFlow
open Roles.AssocExamples Roles.Examples

def request : Request 1 := ⟨index (box int) int, 0, 0⟩
def table (_ : Fin 1) : Request 1 := request

def decode : List (Fin 1) → CommonRoleSettledConstraints.State 1 :=
  CommonRoleAssociatedFeedback.decode (singletonEnv boxImpl) requiredRoles box_paterson before table

def emit (q : Node registry root) : List (Fin 1) :=
  if q.val.role = 1 then [0] else []

/-- The narrowing is computed by a checked associated declaration, not supplied
as an arbitrary ordinary equation or arbitrary decoder. -/
theorem actual_associated_value :
    value (singletonEnv boxImpl) requiredRoles box_paterson request = some .int := by
  have resolved : Roles.resolve (singletonEnv boxImpl).cores box_paterson
      (index (box int) int) = .resolved := by
    rw [Roles.resolve_one _ _ _ boxImpl.impl (by decide)]
    rfl
  unfold value
  have known : Roles.argsBound request.receiver.args = 0 := by decide
  rw [ite_eq_left known]
  change (Roles.assocOf (singletonEnv boxImpl) requiredRoles box_paterson
    (index (box int) int) 0).bind scalar = some .int
  rw [Roles.assoc_independent_of_constraints _ _ _ _ _ resolved boxImpl
    (by simp [singletonEnv]) (by decide)]
  rfl

theorem decode_empty : decode [] = before := rfl

theorem decode_singleton : decode [0] = after := by
  change CommonRoleAssociatedBatch.advance (singletonEnv boxImpl) requiredRoles box_paterson request before = after
  simp only [CommonRoleAssociatedBatch.advance, actual_associated_value]
  rfl

/-- No child-bearing source remains reachable after the computed equation. -/
theorem no_emission_after (q : Node registry root)
    (reached : Reach registry root after q) : emit q = [] := by
  have onlyRoot : q = rootNode registry root := by
    induction reached with
    | root => rfl
    | @step parent child _ edge ih =>
      rw [ih] at edge
      have empty : actualNext registry after (rootNode registry root).val = [] := rfl
      rw [empty] at edge
      cases edge
  rw [onlyRoot]
  rfl

/-- Both possible token subsets fail the support equation. -/
theorem no_supported_candidate :
    CommonRoleSupportSearch.search registry root decode emit = [] := by
  rw [CommonRoleSupportSearch.empty_exact]
  rintro ⟨seen, member, supported⟩
  have possibilities : seen = [] ∨ seen = [0] := by
    simpa [CommonRoleSupportSearch.subsets, List.finRange] using member
  rcases possibilities with rfl | rfl
  · have bad := (supported 0).mpr
      ⟨childNode, by rw [decode_empty]; exact reachable_disappears.1, by decide⟩
    cases bad
  · obtain ⟨q, reached, emitted⟩ := (supported 0).mp (by simp)
    rw [decode_singleton] at reached
    rw [no_emission_after q reached] at emitted
    cases emitted

/-- Actual associated-only decoding does not rescue universal emission
monotonicity: a legitimate checked declaration computes the disabling equality.
This is a two-state finite-token counterexample, not a language rejection. -/
theorem associated_not_monotone :
    ¬ CommonRoleFeedbackConfluence.EmissionMonotone registry root decode emit := by
  intro mono
  have formerly : ∃ q, Reach registry root (decode []) q ∧ (0 : Fin 1) ∈ emit q :=
    ⟨childNode, by rw [decode_empty]; exact reachable_disappears.1, by decide⟩
  obtain ⟨q, reached, emitted⟩ := mono [] [0] (by simp) 0 formerly
  rw [decode_singleton] at reached
  rw [no_emission_after q reached] at emitted
  cases emitted

end Yulang.CommonRoleSupportSearchBoundary
