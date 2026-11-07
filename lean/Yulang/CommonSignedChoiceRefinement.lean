import Yulang.CommonSignedChoicePreparation

/-! The second disjunctive safety phase deletes failing finite candidates.
Every outgoing clause is universal, and its destination list is existential.
Unrestricted statuses never change during this phase. -/
namespace Yulang.CommonSignedChoiceRefinement
open Common (Occurrence)
open CommonSignedChoicePreparation (Clause Graph Supported Covers supported_models discover)
open CommonSignedSafetyPreimage (Fiber run_preserves)
open CommonSignedSafetyPreparation (State allowed set)
open CommonSignedSafetyRefinement (candidates mem_candidates prune size prune_status)

def clauseGood (state : State n) (slot : Fin n) (source : Occurrence) (clause : Clause n) : Bool :=
  if clause.source = slot then
    match clause.action.run source with
    | none => true
    | some target => clause.targets.any (fun slot => allowed (state slot) target)
  else true

theorem clauseGood_exact (state : State n) (slot : Fin n) (source : Occurrence) (clause : Clause n) :
    clauseGood state slot source clause = true ↔
      clause.source = slot → ∀ target, clause.action.run source = some target →
        ∃ destination ∈ clause.targets, allowed (state destination) target = true := by
  by_cases same : clause.source = slot
  · cases runs : clause.action.run source <;> simp [clauseGood, same, runs]
  · simp [clauseGood, same]

def good (graph : Graph n) (state : State n) (slot : Fin n) (source : Occurrence) : Bool :=
  graph.all (clauseGood state slot source)

theorem good_exact (graph : Graph n) (state : State n) (slot : Fin n) (source : Occurrence) :
    good graph state slot source = true ↔
      ∀ clause ∈ graph, clause.source = slot → ∀ target, clause.action.run source = some target →
        ∃ destination ∈ clause.targets, allowed (state destination) target = true := by
  simp only [good, List.all_eq_true, clauseGood_exact]

def removable (graph : Graph n) (state : State n) : Option (Fin n × Occurrence) :=
  (candidates state).find? (fun item => !good graph state item.1 item.2)

theorem removable_some (graph : Graph n) (state : State n) (item : Fin n × Occurrence)
    (found : removable graph state = some item) :
    (∃ values, state item.1 = some values ∧ item.2 ∈ values) ∧ good graph state item.1 item.2 = false := by
  exact ⟨(mem_candidates state item.1 item.2).mp (List.mem_of_find?_eq_some found),
    by simpa only [Bool.not_eq_true'] using List.find?_some found⟩

private theorem sum_weak (nodes : List α) (first last : α → Nat)
    (weak : ∀ node ∈ nodes, first node ≤ last node) : (nodes.map first).sum ≤ (nodes.map last).sum := by
  induction nodes with
  | nil => simp
  | cons head tail ih =>
    have atHead := weak head (by simp)
    have atTail := ih (fun node member => weak node (by simp [member]))
    simp only [List.map_cons, List.sum_cons]
    omega

private theorem sum_strict (nodes : List α) (first last : α → Nat)
    (weak : ∀ node ∈ nodes, first node ≤ last node)
    (extra : ∃ node ∈ nodes, first node < last node) : (nodes.map first).sum < (nodes.map last).sum := by
  induction nodes with
  | nil => simp at extra
  | cons head tail ih =>
    have tailWeak : ∀ node ∈ tail, first node ≤ last node :=
      fun node member => weak node (List.mem_cons_of_mem _ member)
    have weakSum := sum_weak tail first last tailWeak
    obtain ⟨node, member, strict⟩ := extra
    rcases List.mem_cons.mp member with same | member
    · subst node
      simp only [List.map_cons, List.sum_cons]
      omega
    · have tailStrict := ih tailWeak ⟨node, member, strict⟩
      have headWeak := weak head (by simp)
      simp only [List.map_cons, List.sum_cons]
      omega

theorem prune_decreases (graph : Graph n) (state : State n) (item : Fin n × Occurrence)
    (found : removable graph state = some item) : size (prune state item) < size state := by
  obtain ⟨⟨values, atSlot, member⟩, _⟩ := removable_some graph state item found
  have strict : (values.filter (fun occurrence => decide (occurrence ≠ item.2))).length < values.length := by
    apply List.length_filter_lt_length_iff_exists.mpr
    exact ⟨item.2, member, by simp⟩
  apply sum_strict
  · intro slot _
    by_cases same : slot = item.1
    · simpa [prune, CommonSignedSafetyPreparation.set, same, atSlot] using Nat.le_of_lt strict
    · simp [prune, CommonSignedSafetyPreparation.set, same]
  · refine ⟨item.1, by simp, ?_⟩
    simpa [prune, CommonSignedSafetyPreparation.set, atSlot] using strict

def refine (graph : Graph n) (state : State n) : State n :=
  match _found : removable graph state with
  | none => state
  | some item => refine graph (prune state item)
termination_by size state
decreasing_by exact prune_decreases graph state item _found

theorem refine_finished (graph : Graph n) (state : State n) : removable graph (refine graph state) = none := by
  rw [refine]
  split
  · assumption
  · exact refine_finished graph _
termination_by size state
decreasing_by exact prune_decreases graph state _ ‹_›

theorem refine_invariant (graph : Graph n) (invariant : State n → Prop)
    (preserved : ∀ state item, removable graph state = some item → invariant state → invariant (prune state item))
    (state : State n) (initial : invariant state) : invariant (refine graph state) := by
  rw [refine]
  split
  · exact initial
  · exact refine_invariant graph invariant preserved _ (preserved _ _ ‹_› initial)
termination_by size state
decreasing_by exact prune_decreases graph state _ ‹_›

theorem supported_good (graph : Graph n) (fiber : Fiber) (state : State n) (covers : Covers graph fiber state)
    (slot : Fin n) (occurrence : Occurrence) (within : fiber.Contains occurrence) (supported : Supported graph slot occurrence) :
    good graph state slot occurrence = true := by
  apply (good_exact graph state slot occurrence).mpr
  intro clause member same target runs
  subst slot
  obtain ⟨destination, listed, next⟩ := supported_models graph clause member occurrence target supported runs
  exact ⟨destination, listed, covers destination target (run_preserves fiber clause.action occurrence target within runs) next⟩

theorem prune_covers (graph : Graph n) (fiber : Fiber) (state : State n) (item : Fin n × Occurrence)
    (found : removable graph state = some item) (covers : Covers graph fiber state) : Covers graph fiber (prune state item) := by
  intro slot occurrence within supported
  obtain ⟨⟨values, atSlot, _⟩, failed⟩ := removable_some graph state item found
  by_cases same : slot = item.1
  · subst slot
    have accepted := covers item.1 occurrence within supported
    have different : occurrence ≠ item.2 := by
      intro same
      subst occurrence
      have valid := supported_good graph fiber state covers item.1 item.2 within supported
      simp [failed] at valid
    simpa [prune, CommonSignedSafetyPreparation.set, atSlot, allowed, different] using accepted
  · simpa [prune, CommonSignedSafetyPreparation.set, same] using covers slot occurrence within supported

theorem prune_no_discovery (graph : Graph n) (state : State n) (item : Fin n × Occurrence)
    (found : removable graph state = some item) (finished : discover graph state = none) :
    discover graph (prune state item) = none := by
  have candidate := (removable_some graph state item found).1
  apply List.find?_eq_none.mpr
  intro clause member
  have previous := List.find?_eq_none.mp finished clause member
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, List.all_eq_true, Option.isSome_iff_ne_none] at previous ⊢
  rintro ⟨sourceNone, targetsSome⟩
  apply previous
  refine ⟨(prune_status state item clause.source candidate).mp sourceNone, ?_⟩
  intro target listed targetNone
  exact targetsSome target listed ((prune_status state item target candidate).mpr targetNone)
end Yulang.CommonSignedChoiceRefinement
