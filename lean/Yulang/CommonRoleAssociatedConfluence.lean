import Yulang.CommonRoleFeedbackConfluence
import Yulang.CommonRoleAssociatedFeedback

/-! Model-set order independence for actual associated equation batches.
The first theorem is unconditional on reachability. The second still requires
emission monotonicity, an unproved adapter obligation. Neither establishes
unconditional B4 exactness, variable receivers, or principal typing. -/
namespace Yulang.CommonRoleAssociatedConfluence
open CommonRoleMaterializedDomain CommonRoleSourceWorklist
open CommonRoleOpenProducer (Registry)
open CommonRoleSettledConstraints (State)
open CommonRoleAssociatedStateFlow (Request)
open CommonRoleAssociatedFeedback CommonRoleFeedbackConfluence CommonRoleFeedbackTrace
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)

variable (env : Roles.AssocEnv) (roles : Roles.RoleDecls) (wf : Roles.WellFormed env.cores)

/-- Equal token membership gives precisely equal ordinary model sets, regardless
of token order or duplicates, for every assignment. Requests have fixed receivers. -/
theorem same_facts_same_models (seed : State n) (table : Fin k → Request n)
    (a b : List (Fin k)) (same : ∀ i, i ∈ a ↔ i ∈ b)
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (decode env roles wf seed table a).atoms ↔
      All Common.model assignment (decode env roles wf seed table b).atoms := by
  rw [decode_models, decode_models]
  constructor
  · rintro ⟨initial, obligations⟩
    exact ⟨initial, fun i member => obligations i ((same i).mpr member)⟩
  · rintro ⟨initial, obligations⟩
    exact ⟨initial, fun i member => obligations i ((same i).mp member)⟩

/-- Any two closed legal source feedback histories have exactly the same real
ordinary models PROVIDED the named emission-monotonicity obligation holds.
This is conditional; no such proof is supplied for the general source adapter. -/
theorem closed_histories_same_models (registry : Registry) (root : SourceRequest n)
    (seed : State n) (table : Fin k → Request n) (emit : Node registry root → List (Fin k))
    (mono : EmissionMonotone registry root (decode env roles wf seed table) emit)
    (a b : List (Fin k))
    (ha : Trace registry root (decode env roles wf seed table) emit [] a)
    (hb : Trace registry root (decode env roles wf seed table) emit [] b)
    (ca : Closed registry root (decode env roles wf seed table) emit a)
    (cb : Closed registry root (decode env roles wf seed table) emit b)
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (decode env roles wf seed table a).atoms ↔
      All Common.model assignment (decode env roles wf seed table b).atoms :=
  same_facts_same_models env roles wf seed table a b
    (closed_traces_same_facts registry root (decode env roles wf seed table) emit mono ha hb ca cb)
    assignment

/-- Exact model-set agreement of the executable collector with any closed legal
history under emission monotonicity. No satisfiability assumption is hidden. -/
theorem final_models_exact_closed_history (registry : Registry) (root : SourceRequest n)
    (seed : State n) (table : Fin k → Request n) (emit : Node registry root → List (Fin k))
    (mono : EmissionMonotone registry root (decode env roles wf seed table) emit)
    (finish : List (Fin k))
    (history : Trace registry root (decode env roles wf seed table) emit [] finish)
    (closed : Closed registry root (decode env roles wf seed table) emit finish)
    (assignment : Fin n → Comp Common.model) :
    All Common.model assignment (finalState env roles wf registry root seed table emit).atoms ↔
      All Common.model assignment (decode env roles wf seed table finish).atoms :=
  same_facts_same_models env roles wf seed table _ finish
    (collect_exact_closed_trace registry root (decode env roles wf seed table) emit mono finish history closed)
    assignment

end Yulang.CommonRoleAssociatedConfluence
