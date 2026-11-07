import Yulang.CommonSignedSafetyPreparation

/-! Second terminating safety phase: delete a finite candidate with a failing
outgoing edge. Only finite lists shrink; unrestricted rows remain unrestricted. -/
namespace Yulang.CommonSignedSafetyRefinement
open Common (Occurrence)
open CommonSignedFlowFamily (Graph Edge Safe)
open CommonSignedSafetyPreimage (Fiber safe_successor run_preserves)
open CommonSignedSafetyPreparation (State allowed set PureEmpty CoversSafe discover)

/-- Per-occurrence edge obligations are all finite Boolean tests. -/
def edgeGood (state : State n) (slot : Fin n) (source : Occurrence) (edge : Edge n) : Bool :=
  if edge.source = slot then
    match edge.action.run source with
    | none => true
    | some target => allowed (state edge.target) target
  else true

theorem edgeGood_exact (state : State n) (slot : Fin n) (source : Occurrence) (edge : Edge n) :
    edgeGood state slot source edge = true ↔
      edge.source = slot → ∀ target, edge.action.run source = some target → allowed (state edge.target) target = true := by
  by_cases same : edge.source = slot
  · cases runs : edge.action.run source <;> simp [edgeGood, same, runs]
  · simp [edgeGood, same]

def good (graph : Graph n) (state : State n) (slot : Fin n) (source : Occurrence) : Bool :=
  graph.edges.all (edgeGood state slot source)

theorem good_exact (graph : Graph n) (state : State n) (slot : Fin n) (source : Occurrence) :
    good graph state slot source = true ↔
      ∀ edge ∈ graph.edges, edge.source = slot → ∀ target,
        edge.action.run source = some target → allowed (state edge.target) target = true := by
  simp only [good, List.all_eq_true, edgeGood_exact]

def candidates (state : State n) : List (Fin n × Occurrence) :=
  (List.finRange n).flatMap (fun slot => ((state slot).getD []).map (fun occurrence => (slot, occurrence)))

theorem mem_candidates (state : State n) (slot : Fin n) (occurrence : Occurrence) :
    (slot, occurrence) ∈ candidates state ↔
      ∃ values, state slot = some values ∧ occurrence ∈ values := by
  simp only [candidates, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨actual, _, value, member, same⟩
    have slots : actual = slot := congrArg Prod.fst same
    have occurrences : value = occurrence := congrArg Prod.snd same
    subst actual
    subst value
    cases found : state slot with
    | none => simp [found] at member
    | some values => exact ⟨values, rfl, by simpa [found] using member⟩
  · rintro ⟨values, found, member⟩
    exact ⟨slot, by simp, occurrence, by simpa [found] using member, rfl⟩

def removable (graph : Graph n) (state : State n) : Option (Fin n × Occurrence) :=
  (candidates state).find? (fun item => !good graph state item.1 item.2)

theorem removable_some (graph : Graph n) (state : State n) (item : Fin n × Occurrence)
    (found : removable graph state = some item) :
    (∃ values, state item.1 = some values ∧ item.2 ∈ values) ∧ good graph state item.1 item.2 = false := by
  exact ⟨(mem_candidates state item.1 item.2).mp (List.mem_of_find?_eq_some found),
    by simpa only [Bool.not_eq_true'] using List.find?_some found⟩

def prune (state : State n) (item : Fin n × Occurrence) : State n :=
  set state item.1 (some (((state item.1).getD []).filter (fun occurrence => decide (occurrence ≠ item.2))))

def size (state : State n) : Nat :=
  ((List.finRange n).map (fun slot => ((state slot).getD []).length)).sum

private theorem sum_weak (nodes : List α) (first last : α → Nat)
    (weak : ∀ node ∈ nodes, first node ≤ last node) :
    (nodes.map first).sum ≤ (nodes.map last).sum := by
  induction nodes with
  | nil => simp
  | cons head tail ih =>
    have atHead := weak head (by simp)
    have atTail := ih (fun node member => weak node (by simp [member]))
    simp only [List.map_cons, List.sum_cons]
    omega

private theorem sum_strict (nodes : List α) (first last : α → Nat)
    (weak : ∀ node ∈ nodes, first node ≤ last node)
    (extra : ∃ node ∈ nodes, first node < last node) :
    (nodes.map first).sum < (nodes.map last).sum := by
  induction nodes with
  | nil => simp at extra
  | cons head tail ih =>
    have tailWeak : ∀ node ∈ tail, first node ≤ last node :=
      fun node member => weak node (List.mem_cons_of_mem _ member)
    have weakSum : (tail.map first).sum ≤ (tail.map last).sum := by
      exact sum_weak tail first last tailWeak
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

/-- No caller-selected iteration cutoff. -/
def refine (graph : Graph n) (state : State n) : State n :=
  match _found : removable graph state with
  | none => state
  | some item => refine graph (prune state item)
termination_by size state
decreasing_by exact prune_decreases graph state item _found

theorem refine_finished (graph : Graph n) (state : State n) :
    removable graph (refine graph state) = none := by
  rw [refine]
  split
  · assumption
  · exact refine_finished graph _
termination_by size state
decreasing_by exact prune_decreases graph state _ ‹_›

theorem refine_invariant (graph : Graph n) (invariant : State n → Prop)
    (preserved : ∀ state item, removable graph state = some item →
      invariant state → invariant (prune state item))
    (state : State n) (initial : invariant state) : invariant (refine graph state) := by
  rw [refine]
  split
  · exact initial
  · exact refine_invariant graph invariant preserved _ (preserved _ _ ‹_› initial)
termination_by size state
decreasing_by exact prune_decreases graph state _ ‹_›

theorem safe_good (graph : Graph n) (fiber : Fiber) (state : State n) (covers : CoversSafe graph fiber state)
    (slot : Fin n) (occurrence : Occurrence) (within : fiber.Contains occurrence) (safe : Safe graph slot occurrence) :
    good graph state slot occurrence = true := by
  apply (good_exact graph state slot occurrence).mpr
  intro edge member same target runs
  subst slot
  exact covers edge.target target (run_preserves fiber edge.action occurrence target within runs)
    (safe_successor edge member occurrence target safe runs)

theorem prune_covers_safe (graph : Graph n) (fiber : Fiber) (state : State n) (item : Fin n × Occurrence)
    (found : removable graph state = some item) (covers : CoversSafe graph fiber state) :
    CoversSafe graph fiber (prune state item) := by
  intro slot occurrence within safe
  obtain ⟨⟨values, atSlot, _⟩, failed⟩ := removable_some graph state item found
  by_cases same : slot = item.1
  · subst slot
    have permitted := covers item.1 occurrence within safe
    have different : occurrence ≠ item.2 := by
      intro same
      subst occurrence
      have accepted := safe_good graph fiber state covers item.1 item.2 within safe
      simp [failed] at accepted
    simpa [prune, CommonSignedSafetyPreparation.set, atSlot, allowed, different] using permitted
  · simpa [prune, CommonSignedSafetyPreparation.set, same] using covers slot occurrence within safe

theorem prune_status (state : State n) (item : Fin n × Occurrence) (slot : Fin n) :
    (∃ values, state item.1 = some values ∧ item.2 ∈ values) →
      ((prune state item) slot = none ↔ state slot = none) := by
  rintro ⟨values, atSlot, _⟩
  by_cases same : slot = item.1 <;> simp [prune, CommonSignedSafetyPreparation.set, same, atSlot]

theorem prune_pure_empty (graph : Graph n) (state : State n) (item : Fin n × Occurrence)
    (empty : PureEmpty graph state) : PureEmpty graph (prune state item) := by
  intro slot pure
  by_cases same : slot = item.1
  · subst slot
    simp [prune, CommonSignedSafetyPreparation.set, empty item.1 pure]
  · simpa [prune, CommonSignedSafetyPreparation.set, same] using empty slot pure

theorem prune_no_discovery (graph : Graph n) (state : State n) (item : Fin n × Occurrence)
    (found : removable graph state = some item) (finished : discover graph state = none) :
    discover graph (prune state item) = none := by
  have member := (removable_some graph state item found).1
  apply List.find?_eq_none.mpr
  intro edge included
  have previous := List.find?_eq_none.mp finished edge included
  have sourceStatus := prune_status state item edge.source member
  have targetStatus := prune_status state item edge.target member
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Option.isSome_iff_ne_none] at previous ⊢
  rintro ⟨sourceNone, targetSome⟩
  exact previous ⟨sourceStatus.mp sourceNone, fun h => targetSome (targetStatus.mpr h)⟩
end Yulang.CommonSignedSafetyRefinement
