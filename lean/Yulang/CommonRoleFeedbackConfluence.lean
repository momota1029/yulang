import Yulang.CommonRoleFeedbackTrace

/-! Conditional confluence of finite source feedback. This isolates an unproved
adapter obligation; it does NOT establish general B4 or actual-adapter order
independence. Emission monotonicity is an implementation hypothesis, not a
language rejection rule. -/
namespace Yulang.CommonRoleFeedbackConfluence
open CommonRoleMaterializedDomain CommonRoleSourceWorklist
open CommonRoleOpenProducer (Registry)
open CommonRoleSettledConstraints (State)
open CommonRoleFiniteFeedback CommonRoleFeedbackTrace

variable (registry : Registry) (root : SourceRequest n)
  (decode : List (Fin k) → State n) (emit : Node registry root → List (Fin k))

/-- Stability of emitted facts under additional collected facts. The witnessing
source may change; preserving every individual Reach node is not required. -/
def EmissionMonotone : Prop :=
  ∀ a b : List (Fin k), a ⊆ b → ∀ fact,
    (∃ q, Reach registry root (decode a) q ∧ fact ∈ emit q) →
    ∃ q, Reach registry root (decode b) q ∧ fact ∈ emit q

/-- Independent closure, stated without the implementation's traversal. -/
def Closed (seen : List (Fin k)) : Prop :=
  ∀ q, Reach registry root (decode seen) q → ∀ fact, fact ∈ emit q → fact ∈ seen

/-- A legal history cannot leave any closed upper bound, PROVIDED emitted facts
are monotone. This hypothesis is not yet established for the source adapter. -/
theorem trace_subset_closed
    (mono : EmissionMonotone registry root decode emit)
    {start finish bound : List (Fin k)}
    (history : Trace registry root decode emit start finish)
    (initial : start ⊆ bound) (closed : Closed registry root decode emit bound) :
    finish ⊆ bound := by
  induction history with
  | refl => exact initial
  | @step seen fact prior fresh origin ih =>
    intro x member
    rcases List.mem_cons.mp member with eq | old
    · subst x
      obtain ⟨q, reachable, emitted⟩ := mono seen bound ih fact origin
      exact closed q reachable fact emitted
    · exact ih old

/-- Every two closed legal histories from empty have equal fact membership,
under the explicit adapter monotonicity obligation, regardless of step order. -/
theorem closed_traces_same_facts
    (mono : EmissionMonotone registry root decode emit)
    {a b : List (Fin k)}
    (ha : Trace registry root decode emit [] a)
    (hb : Trace registry root decode emit [] b)
    (ca : Closed registry root decode emit a)
    (cb : Closed registry root decode emit b) :
    ∀ fact, fact ∈ a ↔ fact ∈ b := by
  have ab := trace_subset_closed registry root decode emit mono ha (by simp) cb
  have ba := trace_subset_closed registry root decode emit mono hb (by simp) ca
  exact fun fact => ⟨fun h => ab h, fun h => ba h⟩

/-- Closure of the concrete collector is unconditional. -/
theorem collect_is_closed : Closed registry root decode emit
    (collect registry root decode emit) :=
  collect_closed registry root decode emit

/-- The concrete collector is least among independently closed token sets,
conditional on emission monotonicity. -/
theorem collect_least
    (mono : EmissionMonotone registry root decode emit)
    (bound : List (Fin k)) (closed : Closed registry root decode emit bound) :
    collect registry root decode emit ⊆ bound :=
  trace_subset_closed registry root decode emit mono
    (loop_trace registry root decode emit k []) (by simp) closed

/-- Executable result agrees with every closed legal history, under the named
monotonicity obligation. No list-order equality is asserted. -/
theorem collect_exact_closed_trace
    (mono : EmissionMonotone registry root decode emit)
    (finish : List (Fin k)) (history : Trace registry root decode emit [] finish)
    (closed : Closed registry root decode emit finish) :
    ∀ fact, fact ∈ collect registry root decode emit ↔ fact ∈ finish :=
  closed_traces_same_facts registry root decode emit mono
    (loop_trace registry root decode emit k []) history
    (collect_is_closed registry root decode emit) closed

end Yulang.CommonRoleFeedbackConfluence
