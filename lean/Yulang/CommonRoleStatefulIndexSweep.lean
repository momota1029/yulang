import Yulang.CommonRoleOrdinaryKnownness

/-! Actual Index receivers are materialized again from the current state at each
visit. Finite sweep exactness, not general saturation or language classification. -/
namespace Yulang.CommonRoleStatefulIndexSweep
open CommonRoleSettledConstraints (State)
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (All)
open CommonRoleOrdinaryKnownness

structure Edge (n : Nat) where
  receiver : Fin n
  output : Fin n

def visit (s : State n) (edge : Edge n) : Bool × State n :=
  match produceIndex s edge.receiver edge.output with
  | none => (false, s)
  | some out => (true, out)

/-- Positive source step: materialized receiver and actual associated declaration.
No call to the execution function appears in this judgment. -/
def Produced (s : State n) (edge : Edge n) (out : State n) : Prop :=
  ∃ payload head,
    materialize s.atoms edge.receiver = some payload ∧
    CommonRoleAssociatedStateFlow.Computed
      (Roles.AssocExamples.singletonEnv Roles.AssocExamples.boxImpl)
      Roles.AssocExamples.requiredRoles Roles.AssocExamples.box_paterson
      ⟨Roles.AssocExamples.index (Roles.AssocExamples.box payload) Roles.Examples.int,
       0, edge.output⟩ head ∧
    out = CommonRoleCandidateStateFrontier.extend s edge.output head

def Step (s : State n) (edge : Edge n) (done : Bool) (out : State n) : Prop :=
  (done = false ∧ out = s ∧ ¬ ∃ next, Produced s edge next) ∨
  (done = true ∧ Produced s edge out)

theorem produced_exact (s : State n) (edge : Edge n) (out : State n) :
    produceIndex s edge.receiver edge.output = some out ↔ Produced s edge out := by
  unfold produceIndex Produced
  change ((materialize s.atoms edge.receiver).bind _) = some out ↔ _
  simp only [Option.bind_eq_some_iff, CommonRoleAssociatedStateFlow.produce_exact]
  constructor
  · rintro ⟨payload, known, head, computed, equal⟩
    exact ⟨payload, head, known, computed, equal.symm⟩
  · rintro ⟨payload, head, known, computed, equal⟩
    exact ⟨payload, known, head, computed, equal.symm⟩

theorem visit_exact (s : State n) (edge : Edge n) (done : Bool) (out : State n) :
    visit s edge = (done, out) ↔ Step s edge done out := by
  cases h : produceIndex s edge.receiver edge.output with
  | none =>
    have absent : ∀ next, ¬ Produced s edge next := by
      intro next proof
      have p := (produced_exact ..).mpr proof
      rw [h] at p
      cases p
    simp [visit, h, Step, absent, eq_comm]
  | some next =>
    have exactness : ∀ out, Produced s edge out ↔ next = out := by
      intro out
      rw [← produced_exact, h, Option.some.injEq]
    simp [visit, h, Step, exactness, eq_comm]

def sweep : List (Edge n) → State n → List Bool × State n
  | [], s => ([], s)
  | edge :: rest, s =>
      let first := visit s edge
      let tail := sweep rest first.2
      (first.1 :: tail.1, tail.2)

inductive Runs : List (Edge n) → State n → List Bool → State n → Prop
  | nil (s) : Runs [] s [] s
  | cons {edge rest s mid out done trace} :
      Step s edge done mid → Runs rest mid trace out →
      Runs (edge :: rest) s (done :: trace) out

theorem sweep_exact (edges : List (Edge n)) (s : State n) (trace : List Bool) (out : State n) :
    sweep edges s = (trace, out) ↔ Runs edges s trace out := by
  induction edges generalizing s trace out with
  | nil =>
    constructor
    · intro h; cases h; exact Runs.nil _
    · intro h; cases h; rfl
  | cons edge rest ih =>
    cases hv : visit s edge with
    | mk done mid =>
      cases ht : sweep rest mid with
      | mk tail result =>
        constructor
        · intro h
          simp only [sweep, hv, ht] at h
          cases h
          exact Runs.cons ((visit_exact ..).mp hv) ((ih ..).mp ht)
        · intro h
          cases h with
          | cons first remaining =>
            have v := (visit_exact ..).mpr first
            rw [hv] at v
            cases v
            have t := (ih ..).mpr remaining
            simp [sweep, hv, t]

theorem visit_preserves (s : State n) (edge : Edge n)
    (assignment : Fin n → Comp Common.model)
    (model : All Common.model assignment (visit s edge).2.atoms) :
    All Common.model assignment s.atoms := by
  cases h : produceIndex s edge.receiver edge.output with
  | none => simpa [visit, h] using model
  | some out =>
    exact index_preserves s out edge.receiver edge.output h assignment
      (by simpa [visit, h] using model)

theorem sweep_preserves (edges : List (Edge n)) (s : State n)
    (assignment : Fin n → Comp Common.model)
    (model : All Common.model assignment (sweep edges s).2.atoms) :
    All Common.model assignment s.atoms := by
  induction edges generalizing s with
  | nil => exact model
  | cons edge rest ih =>
    exact visit_preserves s edge assignment (ih _ model)

end Yulang.CommonRoleStatefulIndexSweep
