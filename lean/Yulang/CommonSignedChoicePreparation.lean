import Yulang.CommonSignedSafetyDecision

/-! Finite disjunctive row-flow clauses. A transported occurrence must belong
to at least one listed target; an empty target list is a pure obligation.
The first safety phase turns unrestricted candidates into finite lists. -/
namespace Yulang.CommonSignedChoicePreparation
open Common (Occurrence Row)
open CommonSignedFlowFamily (Action)
open CommonSignedSafetyPreimage (Fiber preimage preimage_exact run_preserves)
open CommonSignedSafetyPreparation (State allowed set unknown set_unknown_lt)

structure Clause (n : Nat) where
  source : Fin n
  action : Action
  targets : List (Fin n)

abbrev Graph (n : Nat) := List (Clause n)

def Models (graph : Graph n) (rows : Fin n → Row) : Prop :=
  ∀ clause ∈ graph, ∀ source target, rows clause.source source → clause.action.run source = some target →
    ∃ slot ∈ clause.targets, rows slot target

def Supported (graph : Graph n) (slot : Fin n) (occurrence : Occurrence) : Prop :=
  ∃ rows, Models graph rows ∧ rows slot occurrence

theorem supported_models (graph : Graph n) : Models graph (Supported graph) := by
  intro clause member source target present runs
  obtain ⟨rows, model, seed⟩ := present
  obtain ⟨slot, listed, next⟩ := model clause member source target seed runs
  exact ⟨slot, listed, rows, model, next⟩

def destinationCandidates (state : State n) (clause : Clause n) : List Occurrence :=
  clause.targets.flatMap (fun slot => (state slot).getD [])

theorem mem_destinationCandidates (state : State n) (clause : Clause n) (occurrence : Occurrence) :
    occurrence ∈ destinationCandidates state clause ↔
      ∃ slot ∈ clause.targets, occurrence ∈ (state slot).getD [] := by
  simp only [destinationCandidates, List.mem_flatMap]

def discover (graph : Graph n) (state : State n) : Option (Clause n) :=
  graph.find? (fun clause => (state clause.source).isNone &&
    clause.targets.all (fun target => (state target).isSome))

theorem discover_some (graph : Graph n) (state : State n) (clause : Clause n)
    (found : discover graph state = some clause) :
    clause ∈ graph ∧ state clause.source = none ∧ ∀ target ∈ clause.targets, (state target).isSome = true := by
  have selected := List.find?_some (p := fun clause : Clause n => (state clause.source).isNone &&
    clause.targets.all (fun target => (state target).isSome)) found
  have flags := Bool.and_eq_true_iff.mp selected
  exact ⟨List.mem_of_find?_eq_some found, Option.isNone_iff_eq_none.mp flags.1,
    List.all_eq_true.mp flags.2⟩

def advance (fiber : Fiber) (state : State n) (clause : Clause n) : State n :=
  set state clause.source (some (preimage fiber clause.action (destinationCandidates state clause)))

theorem advance_decreases (graph : Graph n) (fiber : Fiber) (state : State n) (clause : Clause n)
    (found : discover graph state = some clause) : unknown (advance fiber state clause) < unknown state :=
  set_unknown_lt state clause.source _ (discover_some graph state clause found).2.1

def prepare (graph : Graph n) (fiber : Fiber) (state : State n) : State n :=
  match _found : discover graph state with
  | none => state
  | some clause => prepare graph fiber (advance fiber state clause)
termination_by unknown state
decreasing_by exact advance_decreases graph fiber state clause _found

theorem prepare_finished (graph : Graph n) (fiber : Fiber) (state : State n) :
    discover graph (prepare graph fiber state) = none := by
  rw [prepare]
  split
  · assumption
  · exact prepare_finished graph fiber _
termination_by unknown state
decreasing_by exact advance_decreases graph fiber state _ ‹_›

theorem prepare_invariant (graph : Graph n) (fiber : Fiber) (invariant : State n → Prop)
    (preserved : ∀ state clause, discover graph state = some clause → invariant state → invariant (advance fiber state clause))
    (state : State n) (initial : invariant state) : invariant (prepare graph fiber state) := by
  rw [prepare]
  split
  · exact initial
  · exact prepare_invariant graph fiber invariant preserved _ (preserved _ _ ‹_› initial)
termination_by unknown state
decreasing_by exact advance_decreases graph fiber state _ ‹_›

def Covers (graph : Graph n) (fiber : Fiber) (state : State n) : Prop :=
  ∀ slot occurrence, fiber.Contains occurrence → Supported graph slot occurrence → allowed (state slot) occurrence = true

theorem advance_covers (graph : Graph n) (fiber : Fiber) (state : State n) (clause : Clause n)
    (found : discover graph state = some clause) (covers : Covers graph fiber state) :
    Covers graph fiber (advance fiber state clause) := by
  obtain ⟨member, _, finite⟩ := discover_some graph state clause found
  intro slot occurrence within supported
  by_cases same : slot = clause.source
  · subst slot
    simp only [advance, CommonSignedSafetyPreparation.set_same, allowed, List.contains_iff_mem]
    apply (preimage_exact fiber clause.action _ occurrence within).mpr
    intro target runs
    obtain ⟨slot, listed, next⟩ := supported_models graph clause member occurrence target supported runs
    apply (mem_destinationCandidates state clause target).mpr
    refine ⟨slot, listed, ?_⟩
    have accepted := covers slot target (run_preserves fiber clause.action occurrence target within runs) next
    have isFinite := finite slot listed
    cases atSlot : state slot with
    | none => simp [atSlot] at isFinite
    | some values => simpa [atSlot, allowed] using accepted
  · simpa only [advance, CommonSignedSafetyPreparation.set_other state clause.source slot _ same] using
      covers slot occurrence within supported
end Yulang.CommonSignedChoicePreparation
