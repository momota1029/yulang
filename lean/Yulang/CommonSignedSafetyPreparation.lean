import Yulang.CommonSignedSafetyPreimage

/-! First terminating phase of signed head/pure checking. Each step turns one
unrestricted candidate row into a finite safety preimage. -/
namespace Yulang.CommonSignedSafetyPreparation
open Common (Occurrence)
open CommonSignedFlowFamily (Graph Edge Safe)
open CommonSignedSafetyPreimage (Fiber preimage preimage_exact safe_successor run_preserves)

abbrev State (n : Nat) := Fin n → Option (List Occurrence)

def allowed : Option (List Occurrence) → Occurrence → Bool
  | none, _ => true
  | some candidates, occurrence => candidates.contains occurrence

def set (state : State n) (slot : Fin n) (candidate : Option (List Occurrence)) : State n :=
  fun index => if index = slot then candidate else state index

@[simp] theorem set_same (state : State n) (slot : Fin n) (candidate) :
    set state slot candidate slot = candidate := by simp [set]

@[simp] theorem set_other (state : State n) (slot index : Fin n) (candidate)
    (different : index ≠ slot) : set state slot candidate index = state index := by simp [set, different]

def unknown (state : State n) : Nat :=
  (List.finRange n).countP (fun slot => (state slot).isNone)

private theorem countP_strict (nodes : List α) (first last : α → Bool)
    (included : ∀ node ∈ nodes, first node = true → last node = true)
    (extra : ∃ node ∈ nodes, first node = false ∧ last node = true) :
    nodes.countP first < nodes.countP last := by
  induction nodes with
  | nil => simp at extra
  | cons head tail ih =>
    have tailIncluded : ∀ node ∈ tail, first node = true → last node = true :=
      fun node member => included node (List.mem_cons_of_mem _ member)
    have weak := List.countP_mono_left tailIncluded
    by_cases headExtra : first head = false ∧ last head = true
    · simp [headExtra.1, headExtra.2]
      omega
    · have tailExtra : ∃ node ∈ tail, first node = false ∧ last node = true := by
        obtain ⟨node, member, difference⟩ := extra
        rcases List.mem_cons.mp member with same | member
        · subst node; exact False.elim (headExtra difference)
        · exact ⟨node, member, difference⟩
      have strict := ih tailIncluded tailExtra
      have atHead := included head (by simp)
      simp only [List.countP_cons]
      cases firstEq : first head with
      | false =>
        cases lastEq : last head <;> simp <;> omega
      | true =>
        have lastEq : last head = true := atHead firstEq
        simp [lastEq]
        omega

theorem set_unknown_lt (state : State n) (slot : Fin n) (candidates : List Occurrence)
    (unassigned : state slot = none) : unknown (set state slot (some candidates)) < unknown state := by
  apply countP_strict
  · intro node _ present
    by_cases same : node = slot
    · simp [same, set] at present
    · simpa [set, same] using present
  · refine ⟨slot, by simp, ?_, ?_⟩
    · simp [set]
    · simp [unassigned]

def discover (graph : Graph n) (state : State n) : Option (Edge n) :=
  graph.edges.find? (fun edge => (state edge.source).isNone && (state edge.target).isSome)

theorem discover_some (graph : Graph n) (state : State n) (edge : Edge n)
    (found : discover graph state = some edge) :
    edge ∈ graph.edges ∧ state edge.source = none ∧ (state edge.target).isSome = true := by
  have chosen := List.find?_some found
  have flags : (state edge.source).isNone = true ∧ (state edge.target).isSome = true := by
    simpa only [Bool.and_eq_true] using chosen
  exact ⟨List.mem_of_find?_eq_some found, Option.isNone_iff_eq_none.mp flags.1, flags.2⟩

def advance (fiber : Fiber) (state : State n) (edge : Edge n) : State n :=
  set state edge.source (some (preimage fiber edge.action ((state edge.target).getD [])))

theorem advance_decreases (graph : Graph n) (fiber : Fiber) (state : State n) (edge : Edge n)
    (found : discover graph state = some edge) : unknown (advance fiber state edge) < unknown state :=
  set_unknown_lt state edge.source _ (discover_some graph state edge found).2.1

/-- No caller fuel, reachability oracle or semantic premise is an input. -/
def prepare (graph : Graph n) (fiber : Fiber) (state : State n) : State n :=
  match _found : discover graph state with
  | none => state
  | some edge => prepare graph fiber (advance fiber state edge)
termination_by unknown state
decreasing_by exact advance_decreases graph fiber state edge _found

theorem prepare_finished (graph : Graph n) (fiber : Fiber) (state : State n) :
    discover graph (prepare graph fiber state) = none := by
  rw [prepare]
  split
  · assumption
  · exact prepare_finished graph fiber _
termination_by unknown state
decreasing_by exact advance_decreases graph fiber state _ ‹_›

theorem prepare_invariant (graph : Graph n) (fiber : Fiber) (invariant : State n → Prop)
    (preserved : ∀ state edge, discover graph state = some edge →
      invariant state → invariant (advance fiber state edge))
    (state : State n) (initial : invariant state) : invariant (prepare graph fiber state) := by
  rw [prepare]
  split
  · exact initial
  · exact prepare_invariant graph fiber invariant preserved _ (preserved _ _ ‹_› initial)
termination_by unknown state
decreasing_by exact advance_decreases graph fiber state _ ‹_›

/-- This is a proof invariant of the algorithm, not a solver input. -/
def CoversSafe (graph : Graph n) (fiber : Fiber) (state : State n) : Prop :=
  ∀ slot occurrence, fiber.Contains occurrence → Safe graph slot occurrence → allowed (state slot) occurrence = true

theorem advance_covers_safe (graph : Graph n) (fiber : Fiber) (state : State n) (edge : Edge n)
    (found : discover graph state = some edge) (covers : CoversSafe graph fiber state) :
    CoversSafe graph fiber (advance fiber state edge) := by
  obtain ⟨member, _, targetSome⟩ := discover_some graph state edge found
  intro slot occurrence within safe
  by_cases same : slot = edge.source
  · subst slot
    simp only [advance, set_same, allowed, List.contains_iff_mem]
    apply (preimage_exact fiber edge.action _ occurrence within).mpr
    intro target runs
    have targetWithin := run_preserves fiber edge.action occurrence target within runs
    have targetSafe := safe_successor edge member occurrence target safe runs
    have permitted := covers edge.target target targetWithin targetSafe
    cases targetEq : state edge.target with
    | none => simp [targetEq] at targetSome
    | some candidates => simpa [targetEq, allowed] using permitted
  · simpa only [advance, set_other state edge.source slot _ same] using covers slot occurrence within safe

def PureEmpty (graph : Graph n) (state : State n) : Prop :=
  ∀ slot ∈ graph.pure, state slot = some []

theorem advance_pure_empty (graph : Graph n) (fiber : Fiber) (state : State n) (edge : Edge n)
    (found : discover graph state = some edge) (empty : PureEmpty graph state) :
    PureEmpty graph (advance fiber state edge) := by
  intro slot member
  have different : slot ≠ edge.source := by
    intro same
    have before := (discover_some graph state edge found).2.1
    have atPure := empty slot member
    rw [same, before] at atPure
    contradiction
  simpa only [advance, set_other state edge.source slot _ different] using empty slot member

def initial (graph : Graph n) : State n :=
  fun slot => if slot ∈ graph.pure then some [] else none

theorem initial_pure_empty (graph : Graph n) : PureEmpty graph (initial graph) := by
  intro slot member
  simp [initial, member]

theorem initial_covers_safe (graph : Graph n) (fiber : Fiber) : CoversSafe graph fiber (initial graph) := by
  intro slot occurrence _ safe
  by_cases pure : slot ∈ graph.pure
  · exact False.elim (safe slot occurrence (.nil _ _) pure)
  · simp [initial, pure, allowed]
end Yulang.CommonSignedSafetyPreparation
