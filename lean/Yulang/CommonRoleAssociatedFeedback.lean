import Yulang.CommonRoleFiniteFeedback
import Yulang.CommonRoleAssociatedBatch

/-! Finite feedback with real declaration-computed associated equations.
The finite request table and source-node-to-request association are still supplied.
Receivers of table requests are fixed; this is not arbitrary interval inference.
Collected obligations are persistent; no least-solution/order theorem is claimed. -/
namespace Yulang.CommonRoleAssociatedFeedback
open CommonRoleMaterializedDomain CommonRoleSourceWorklist
open CommonRoleOpenProducer (Registry)
open CommonRoleSettledConstraints (State)
open CommonRoleAssociatedStateFlow (Request Computed)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

variable (env : Roles.AssocEnv) (roles : Roles.RoleDecls)
  (wf : Roles.WellFormed env.cores)

def decode (seed : State n) (table : Fin k → Request n) (seen : List (Fin k)) : State n :=
  CommonRoleAssociatedBatch.run env roles wf (seen.map table) seed

def collected (registry : Registry) (root : SourceRequest n) (seed : State n)
    (table : Fin k → Request n) (emit : Node registry root → List (Fin k)) : List (Fin k) :=
  CommonRoleFiniteFeedback.collect registry root (decode env roles wf seed table) emit

def finalState (registry : Registry) (root : SourceRequest n) (seed : State n)
    (table : Fin k → Request n) (emit : Node registry root → List (Fin k)) : State n :=
  decode env roles wf seed table (collected env roles wf registry root seed table emit)

/-- Ordinary equations come from actual associated declarations, at one assignment. -/
theorem decode_models (seed : State n) (table : Fin k → Request n) (seen : List (Fin k))
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (decode env roles wf seed table seen).atoms ↔
      All Common.model assignment seed.atoms ∧
      ∀ i ∈ seen, ∀ head, Computed env roles wf (table i) head →
        Common.Equivalent (assignment (table i).output).1 (.base head) := by
  rw [decode, CommonRoleAssociatedBatch.run_models]
  simp only [CommonRoleAssociatedBatch.Obligations, List.mem_map]
  constructor
  · rintro ⟨initial, obligations⟩
    exact ⟨initial, fun i member head computed => obligations (table i) ⟨i, member, rfl⟩ head computed⟩
  · rintro ⟨initial, obligations⟩
    refine ⟨initial, ?_⟩
    rintro q ⟨i, member, rfl⟩ head computed
    exact obligations i member head computed

/-- At most k distinct request identifiers are processed; no external trace. -/
theorem collected_bounded (registry : Registry) (root : SourceRequest n) (seed : State n)
    (table : Fin k → Request n) (emit : Node registry root → List (Fin k)) :
    (collected env roles wf registry root seed table emit).Nodup ∧
    (collected env roles wf registry root seed table emit).length ≤ k :=
  ⟨CommonRoleFiniteFeedback.collect_nodup .., CommonRoleFiniteFeedback.collect_capacity ..⟩

theorem final_models (registry : Registry) (root : SourceRequest n) (seed : State n)
    (table : Fin k → Request n) (emit : Node registry root → List (Fin k))
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (finalState env roles wf registry root seed table emit).atoms ↔
      All Common.model assignment seed.atoms ∧
      ∀ i ∈ collected env roles wf registry root seed table emit, ∀ head,
        Computed env roles wf (table i) head →
        Common.Equivalent (assignment (table i).output).1 (.base head) := decode_models ..

/-- Every finally reachable source obligation has its computed equation in the
final ordinary state. The model premise is explicit; inconsistency is not hidden. -/
theorem reachable_equation (registry : Registry) (root : SourceRequest n) (seed : State n)
    (table : Fin k → Request n) (emit : Node registry root → List (Fin k))
    (assignment : Fin n → Comp Common.model)
    (models : All Common.model assignment (finalState env roles wf registry root seed table emit).atoms)
    (q : Node registry root)
    (reachable : Reach registry root (finalState env roles wf registry root seed table emit) q)
    (i : Fin k) (emitted : i ∈ emit q) (head : Inference.Base)
    (computed : Computed env roles wf (table i) head) :
    Common.Equivalent (assignment (table i).output).1 (.base head) := by
  have member := CommonRoleFiniteFeedback.collect_closed registry root
    (decode env roles wf seed table) emit q reachable i emitted
  exact ((final_models ..).mp models).2 i member head computed

/-- Final closure is recomputed, so no stale source node is retained merely
because it was reachable before an associated equation narrowed its parent. -/
theorem final_visits_exact (registry : Registry) (root : SourceRequest n) (seed : State n)
    (table : Fin k → Request n) (emit : Node registry root → List (Fin k))
    (q : Node registry root) :
    q ∈ CommonRoleFiniteFeedback.visits registry root (decode env roles wf seed table) emit ↔
      Reach registry root (finalState env roles wf registry root seed table emit) q :=
  CommonRoleFiniteFeedback.visits_exact ..

end Yulang.CommonRoleAssociatedFeedback
