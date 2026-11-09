import Yulang.CommonRoleFiniteFeedback

/-! Provenance for nonmonotone finite feedback. Updates persist even when their
source is no longer finally reachable; this proves historical origin, NOT a
least solution or order independence. -/
namespace Yulang.CommonRoleFeedbackTrace
open CommonRoleMaterializedDomain CommonRoleSourceWorklist
open CommonRoleOpenProducer (Registry)
open CommonRoleSettledConstraints (State)
open CommonRoleFiniteFeedback

variable (registry : Registry) (root : SourceRequest n)
  (decode : List (Fin k) → State n) (emit : Node registry root → List (Fin k))

/-- Declarative trace: add only a fresh token emitted by an actually reachable
source in the state before the update. No implementation traversal is mentioned. -/
inductive Trace (registry : Registry) (root : SourceRequest n)
    (decode : List (Fin k) → State n) (emit : Node registry root → List (Fin k)) :
    List (Fin k) → List (Fin k) → Prop where
  | refl (seen) : Trace registry root decode emit seen seen
  | step {start seen fact} : Trace registry root decode emit start seen →
      fact ∉ seen → (∃ q, Reach registry root (decode seen) q ∧ fact ∈ emit q) →
      Trace registry root decode emit start (fact :: seen)

theorem trace_trans {a b c : List (Fin k)}
    (ab : Trace registry root decode emit a b) (bc : Trace registry root decode emit b c) :
    Trace registry root decode emit a c := by
  induction bc with
  | refl => exact ab
  | step _ fresh origin ih => exact .step ih fresh origin

/-- Every execution, at arbitrary fuel and starting state, is a valid trace. -/
theorem loop_trace (fuel : Nat) (seen : List (Fin k)) :
    Trace registry root decode emit seen
      (loop (feedbackRules registry root decode emit) fuel seen) := by
  induction fuel generalizing seen with
  | zero => exact .refl _
  | succ fuel ih =>
    simp only [loop]
    cases found : FiniteHorn.firstFresh (feedbackRules registry root decode emit seen)
        seen (List.finRange k) with
    | none => exact .refl _
    | some fact =>
      have fresh := FiniteHorn.firstFresh_some _ _ _ found
      apply trace_trans registry root decode emit (b := fact :: seen)
      · exact .step (.refl _) fresh.2.1 ((feedback_enabled ..).mp fresh.2.2)
      · exact ih _

/-- Every added token has an earlier reachable source, without requiring rules
to stay enabled later. The witness state is itself on a legal trace. -/
theorem trace_origin {start finish : List (Fin k)}
    (history : Trace registry root decode emit start finish) (fact : Fin k)
    (member : fact ∈ finish) (new : fact ∉ start) :
    ∃ seen q, Trace registry root decode emit start seen ∧
      Reach registry root (decode seen) q ∧ fact ∈ emit q := by
  induction history with
  | refl => exact False.elim (new member)
  | @step seen token prior fresh origin ih =>
    rcases List.mem_cons.mp member with eq | old
    · subst fact
      obtain ⟨q, reach, emitted⟩ := origin
      exact ⟨seen, q, prior, reach, emitted⟩
    · exact ih old

/-- Unconditional historical provenance for every collected update ID. -/
theorem collected_origin (fact : Fin k)
    (member : fact ∈ collect registry root decode emit) :
    ∃ seen q, Trace registry root decode emit [] seen ∧
      Reach registry root (decode seen) q ∧ fact ∈ emit q :=
  trace_origin registry root decode emit (loop_trace registry root decode emit k [])
    fact member (by simp)

end Yulang.CommonRoleFeedbackTrace
