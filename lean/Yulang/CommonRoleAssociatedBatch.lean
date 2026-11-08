import Yulang.CommonRoleAssociatedStateFlow

/-! Fixed associated requests accumulate real declaration-computed equations.
Unknown results remain pending, not errors. The semantic fixed-point result
is only for fixed first-order receivers; it is not general source saturation. -/
namespace Yulang.CommonRoleAssociatedBatch
open CommonRoleAssociatedStateFlow (Request Computed value)
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

variable (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
  (wf : Roles.WellFormed env.cores)

def advance (q : Request n) (s : State n) : State n :=
  match value env roles wf q with
  | none => s
  | some head => CommonRoleCandidateStateFrontier.extend s q.output head

def Obligations (qs : List (Request n)) (assignment : Fin n → Comp Common.model) : Prop :=
  ∀ q ∈ qs, ∀ head, Computed env roles wf q head →
    Common.Equivalent (assignment q.output).1 (.base head)

def run : List (Request n) → State n → State n
  | [], s => s
  | q :: rest, s => run rest (advance env roles wf q s)

def pending (qs : List (Request n)) : List (Request n) :=
  qs.filter fun q => (value env roles wf q).isNone

theorem advance_models (q : Request n) (s : State n)
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (advance env roles wf q s).atoms ↔
      All Common.model assignment s.atoms ∧
      ∀ head, Computed env roles wf q head →
        Common.Equivalent (assignment q.output).1 (.base head) := by
  cases result : value env roles wf q with
  | none =>
    have absent : ∀ head, ¬ Computed env roles wf q head := by
      intro head computed
      have h := (CommonRoleAssociatedStateFlow.value_exact ..).mpr computed
      rw [result] at h
      cases h
    simp [advance, result, absent]
  | some head =>
    rw [advance, result, CommonRoleCandidateStateFrontier.extend_exact]
    constructor
    · rintro ⟨old, equation⟩
      refine ⟨old, ?_⟩
      intro other computed
      have h := (CommonRoleAssociatedStateFlow.value_exact ..).mpr computed
      rw [result] at h
      cases h
      exact equation
    · rintro ⟨old, all⟩
      exact ⟨old, all head ((CommonRoleAssociatedStateFlow.value_exact ..).mp result)⟩

theorem run_models (qs : List (Request n)) (s : State n)
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (run env roles wf qs s).atoms ↔
      All Common.model assignment s.atoms ∧ Obligations env roles wf qs assignment := by
  induction qs generalizing s with
  | nil => simp [run, Obligations]
  | cons q rest ih =>
    rw [run, ih, advance_models]
    simp only [Obligations, List.forall_mem_cons]
    exact and_assoc

theorem run_preserves (qs : List (Request n)) (s : State n)
    (assignment : Fin n → Comp Common.model)
    (model : All Common.model assignment (run env roles wf qs s).atoms) :
    All Common.model assignment s.atoms := ((run_models ..).mp model).1

/-- Repeating the same fixed requests adds no new semantic constraint. -/
theorem run_idempotent_models (qs : List (Request n)) (s : State n)
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (run env roles wf qs (run env roles wf qs s)).atoms ↔
      All Common.model assignment (run env roles wf qs s).atoms := by
  rw [run_models, run_models]
  exact and_self_right

/-- Only this fixed, already supplied associated-request batch is permutable. -/
theorem run_permutation_models (left right : List (Request n)) (s : State n)
    (perm : left.Perm right) (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (run env roles wf left s).atoms ↔
      All Common.model assignment (run env roles wf right s).atoms := by
  rw [run_models, run_models]
  apply and_congr Iff.rfl
  constructor <;> intro held q member head computed
  · exact held q (perm.mem_iff.mpr member) head computed
  · exact held q (perm.mem_iff.mp member) head computed

theorem pending_exact (qs : List (Request n)) (q : Request n) :
    q ∈ pending env roles wf qs ↔ q ∈ qs ∧ ∀ head, ¬ Computed env roles wf q head := by
  simp only [pending, List.mem_filter, Option.isNone_iff_eq_none]
  apply and_congr Iff.rfl
  cases result : value env roles wf q with
  | none =>
    simp only [true_iff]
    intro head computed
    have h := (CommonRoleAssociatedStateFlow.value_exact ..).mpr computed
    rw [result] at h
    cases h
  | some head =>
    constructor
    · intro impossible; cases impossible
    · intro absent
      exact False.elim (absent head ((CommonRoleAssociatedStateFlow.value_exact ..).mp result))

/-- All candidates have identical feasibility after a repeated fixed pass. -/
theorem candidate_stable (qs : List (Request n)) (s : State n)
    (slot : Fin n) (c : CommonRoleCandidateStateFrontier.Candidate) :
    CommonRoleCandidateStateFrontier.Fits (run env roles wf qs (run env roles wf qs s)) slot c ↔
      CommonRoleCandidateStateFrontier.Fits (run env roles wf qs s) slot c := by
  unfold CommonRoleCandidateStateFrontier.Fits
  exact exists_congr fun assignment => and_congr (run_idempotent_models ..) Iff.rfl

end Yulang.CommonRoleAssociatedBatch
