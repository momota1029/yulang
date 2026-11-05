import Yulang.FiniteBooleanReachability
import Yulang.Horn

/-!
# Exact inclusion of finite nondeterministic automata

The independent `Runs` judgment consumes arbitrary finite words. Executable
subset construction computes its exact set of endpoints; a finite graph of
pairs of such subsets detects every counterexample to language inclusion.
Graph reachability uses the materialized Boolean closure, with no bound on
word length and no supplied termination fuel.

The alphabet is supplied as a finite list. The unrestricted inclusion theorem
requires that this list covers the letter type. Its restricted version covers
exactly words whose letters occur in the list. Repetitions and letter order do
not change the meaning. States are finite but words have unbounded length.

This reference algorithm explicitly enumerates the two powersets and computes
their product reachability matrix. It is not a claim of production performance.
-/

namespace Yulang.FiniteAutomata

structure NFA (Letter : Type) (n : Nat) where
  initial : Fin n → Bool
  transition : Fin n → Letter → Fin n → Bool
  accepting : Fin n → Bool

inductive Runs (automaton : NFA Letter n) : Fin n → List Letter → Fin n → Prop where
  | nil (state : Fin n) : Runs automaton state [] state
  | cons : automaton.transition source symbol middle = true →
      Runs automaton middle rest target → Runs automaton source (symbol :: rest) target

def Accepts (automaton : NFA Letter n) (word : List Letter) : Prop :=
  ∃ source target, automaton.initial source = true ∧ Runs automaton source word target ∧
    automaton.accepting target = true

abbrev Subset (n : Nat) := Fin n → Bool

def advance (automaton : NFA Letter n) (subset : Subset n) (symbol : Letter) : Subset n :=
  fun target => (List.finRange n).any fun source =>
    subset source && automaton.transition source symbol target

theorem advance_exact (automaton : NFA Letter n) (subset : Subset n)
    (symbol : Letter) (target : Fin n) :
    advance automaton subset symbol target = true ↔
      ∃ source, subset source = true ∧ automaton.transition source symbol target = true := by
  simp [advance]

def run (automaton : NFA Letter n) : Subset n → List Letter → Subset n
  | subset, [] => subset
  | subset, symbol :: rest => run automaton (advance automaton subset symbol) rest

theorem run_exact (automaton : NFA Letter n) (subset : Subset n)
    (word : List Letter) (target : Fin n) :
    run automaton subset word target = true ↔
      ∃ source, subset source = true ∧ Runs automaton source word target := by
  induction word generalizing subset with
  | nil =>
      constructor
      · intro member
        exact ⟨target, member, .nil _⟩
      · rintro ⟨source, member, reached⟩
        cases reached
        exact member
  | cons symbol rest ih =>
      rw [run, ih]
      constructor
      · rintro ⟨middle, member, reached⟩
        obtain ⟨source, present, step⟩ := (advance_exact automaton subset symbol middle).mp member
        exact ⟨source, present, .cons step reached⟩
      · rintro ⟨source, present, reached⟩
        cases reached with
        | @cons _ _ middle _ _ step rest =>
            exact ⟨middle, (advance_exact automaton subset symbol middle).mpr ⟨source, present, step⟩, rest⟩

def acceptsSubset (automaton : NFA Letter n) (subset : Subset n) : Bool :=
  (List.finRange n).any fun state => subset state && automaton.accepting state

theorem acceptsSubset_exact (automaton : NFA Letter n) (subset : Subset n) :
    acceptsSubset automaton subset = true ↔
      ∃ state, subset state = true ∧ automaton.accepting state = true := by
  simp [acceptsSubset]

def checkWord (automaton : NFA Letter n) (word : List Letter) : Bool :=
  acceptsSubset automaton (run automaton automaton.initial word)

theorem checkWord_exact (automaton : NFA Letter n) (word : List Letter) :
    checkWord automaton word = true ↔ Accepts automaton word := by
  rw [checkWord, acceptsSubset_exact]
  constructor
  · rintro ⟨target, reached, accepted⟩
    obtain ⟨source, initial, path⟩ := (run_exact automaton automaton.initial word target).mp reached
    exact ⟨source, target, initial, path, accepted⟩
  · rintro ⟨source, target, initial, path, accepted⟩
    exact ⟨target, (run_exact automaton automaton.initial word target).mpr ⟨source, initial, path⟩,
      accepted⟩

instance (automaton : NFA Letter n) (word : List Letter) : Decidable (Accepts automaton word) :=
  decidable_of_iff (checkWord automaton word = true) (checkWord_exact automaton word)

def subsetEq (left right : Subset n) : Bool :=
  (List.finRange n).all fun state => decide (left state = right state)

theorem subsetEq_exact (left right : Subset n) : subsetEq left right = true ↔ left = right := by
  simp only [subsetEq, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq]
  exact ⟨funext, fun same state => congrFun same state⟩

abbrev Pair (n m : Nat) := Subset n × Subset m

def pairEq (left right : Pair n m) : Bool :=
  subsetEq left.1 right.1 && subsetEq left.2 right.2

theorem pairEq_exact (left right : Pair n m) : pairEq left right = true ↔ left = right := by
  simp only [pairEq, Bool.and_eq_true, subsetEq_exact]
  exact ⟨fun parts => Prod.ext parts.1 parts.2, fun equal => ⟨congrArg Prod.fst equal, congrArg Prod.snd equal⟩⟩

def stepPair (left : NFA Letter n) (right : NFA Letter m) (pair : Pair n m) (symbol : Letter) : Pair n m :=
  (advance left pair.1 symbol, advance right pair.2 symbol)

def runPair (left : NFA Letter n) (right : NFA Letter m) : Pair n m → List Letter → Pair n m
  | pair, [] => pair
  | pair, symbol :: rest => runPair left right (stepPair left right pair symbol) rest

theorem runPair_eq (left : NFA Letter n) (right : NFA Letter m)
    (pair : Pair n m) (word : List Letter) :
    runPair left right pair word = (run left pair.1 word, run right pair.2 word) := by
  induction word generalizing pair with
  | nil => rfl
  | cons symbol rest ih => simp only [runPair, ih, stepPair, run]

def badPair (left : NFA Letter n) (right : NFA Letter m) (pair : Pair n m) : Bool :=
  acceptsSubset left pair.1 && !(acceptsSubset right pair.2)

theorem badPair_run_exact (left : NFA Letter n) (right : NFA Letter m) (word : List Letter) :
    badPair left right (runPair left right (left.initial, right.initial) word) = true ↔
      Accepts left word ∧ ¬ Accepts right word := by
  rw [runPair_eq]
  change (checkWord left word && !(checkWord right word)) = true ↔ _
  simp [Bool.eq_false_iff, checkWord_exact]

def pairs (n m : Nat) : List (Pair n m) :=
  (Horn.valuations n).flatMap fun left => (Horn.valuations m).map fun right => (left, right)

theorem mem_pairs (pair : Pair n m) : pair ∈ pairs n m := by
  exact List.mem_flatMap.mpr ⟨pair.1, Horn.mem_valuations _,
    List.mem_map.mpr ⟨pair.2, Horn.mem_valuations _, rfl⟩⟩

abbrev Vertex (n m : Nat) := Fin (pairs n m).length

def stateAt (vertex : Vertex n m) : Pair n m := (pairs n m).get vertex

theorem stateAt_covers (pair : Pair n m) : ∃ vertex, stateAt vertex = pair :=
  List.mem_iff_get.mp (mem_pairs pair)

def graph (alphabet : List Letter) (left : NFA Letter n) (right : NFA Letter m)
    (source target : Vertex n m) : Bool :=
  alphabet.any fun symbol => pairEq (stepPair left right (stateAt source) symbol) (stateAt target)

theorem graph_exact (alphabet : List Letter) (left : NFA Letter n) (right : NFA Letter m)
    (source target : Vertex n m) :
    graph alphabet left right source target = true ↔
      ∃ symbol ∈ alphabet, stepPair left right (stateAt source) symbol = stateAt target := by
  simp [graph, pairEq_exact]

def Over (alphabet : List Letter) (word : List Letter) : Prop :=
  ∀ symbol ∈ word, symbol ∈ alphabet

theorem path_word (alphabet : List Letter) (left : NFA Letter n) (right : NFA Letter m)
    {source target : Vertex n m}
    (path : FiniteBooleanReachability.Path (graph alphabet left right) source target) :
    ∃ word, Over alphabet word ∧ runPair left right (stateAt source) word = stateAt target := by
  induction path with
  | nil vertex => exact ⟨[], by simp [Over], rfl⟩
  | @cons source middle target edge rest ih =>
      obtain ⟨symbol, member, step⟩ := (graph_exact alphabet left right source middle).mp edge
      obtain ⟨word, over, finished⟩ := ih
      refine ⟨symbol :: word, ?_, ?_⟩
      · intro letter present
        rcases List.mem_cons.mp present with rfl | inRest
        · exact member
        · exact over letter inRest
      · simpa only [runPair, step] using finished

theorem word_path (alphabet : List Letter) (left : NFA Letter n) (right : NFA Letter m)
    (source : Vertex n m) (word : List Letter) (over : Over alphabet word) :
    ∃ target, FiniteBooleanReachability.Path (graph alphabet left right) source target ∧
      stateAt target = runPair left right (stateAt source) word := by
  induction word generalizing source with
  | nil => exact ⟨source, .nil _, rfl⟩
  | cons symbol rest ih =>
      obtain ⟨middle, step⟩ := stateAt_covers (stepPair left right (stateAt source) symbol)
      obtain ⟨target, reached, final⟩ := ih middle (fun letter member => over letter (List.mem_cons_of_mem _ member))
      refine ⟨target, .cons ?_ reached, ?_⟩
      · exact (graph_exact alphabet left right source middle).mpr
          ⟨symbol, over symbol (by simp), step.symm⟩
      · simpa only [runPair, step] using final

def hasCounterexample (alphabet : List Letter) (left : NFA Letter n) (right : NFA Letter m) : Bool :=
  let reachability := FiniteBooleanReachability.closure (graph alphabet left right)
  (List.finRange (pairs n m).length).any fun source =>
    pairEq (stateAt source) (left.initial, right.initial) &&
      (List.finRange (pairs n m).length).any fun target =>
        FiniteBooleanReachability.entry reachability source target && badPair left right (stateAt target)

theorem hasCounterexample_exact (alphabet : List Letter)
    (left : NFA Letter n) (right : NFA Letter m) :
    hasCounterexample alphabet left right = true ↔
      ∃ word, Over alphabet word ∧ Accepts left word ∧ ¬ Accepts right word := by
  simp only [hasCounterexample, List.any_eq_true, List.mem_finRange, true_and,
    Bool.and_eq_true, pairEq_exact, FiniteBooleanReachability.closure_exact]
  constructor
  · rintro ⟨source, initial, target, path, bad⟩
    obtain ⟨word, over, final⟩ := path_word alphabet left right path
    refine ⟨word, over, ?_⟩
    rw [initial] at final
    rw [← final] at bad
    exact (badPair_run_exact left right word).mp bad
  · rintro ⟨word, over, accepted, rejected⟩
    obtain ⟨source, initial⟩ := stateAt_covers (left.initial, right.initial)
    obtain ⟨target, path, final⟩ := word_path alphabet left right source word over
    refine ⟨source, initial, target, path, ?_⟩
    rw [final, initial]
    exact (badPair_run_exact left right word).mpr ⟨accepted, rejected⟩

def checkSubset (alphabet : List Letter) (left : NFA Letter n) (right : NFA Letter m) : Bool :=
  !(hasCounterexample alphabet left right)

theorem checkSubset_over_exact (alphabet : List Letter)
    (left : NFA Letter n) (right : NFA Letter m) :
    checkSubset alphabet left right = true ↔
      ∀ word, Over alphabet word → Accepts left word → Accepts right word := by
  constructor
  · intro checked word over accepted
    by_cases rightAccepts : Accepts right word
    · exact rightAccepts
    · have counterexample := (hasCounterexample_exact alphabet left right).mpr
        ⟨word, over, accepted, rightAccepts⟩
      simp [checkSubset, counterexample] at checked
  · intro included
    cases counterexample : hasCounterexample alphabet left right with
    | false => simp [checkSubset, counterexample]
    | true =>
        obtain ⟨word, over, accepted, rejected⟩ :=
          (hasCounterexample_exact alphabet left right).mp counterexample
        exact (rejected (included word over accepted)).elim

/-- Complete finite alphabets give a decision procedure for inclusion over
all finite words; no length bound appears in the quantified statement. -/
theorem checkSubset_exact (alphabet : List Letter) (complete : ∀ symbol, symbol ∈ alphabet)
    (left : NFA Letter n) (right : NFA Letter m) :
    checkSubset alphabet left right = true ↔ ∀ word, Accepts left word → Accepts right word := by
  rw [checkSubset_over_exact]
  exact ⟨fun included word => included word (fun symbol _ => complete symbol),
    fun included word _ => included word⟩

theorem checkSubset_rejects (alphabet : List Letter) (complete : ∀ symbol, symbol ∈ alphabet)
    (left : NFA Letter n) (right : NFA Letter m) :
    checkSubset alphabet left right = false ↔
      ∃ word, Accepts left word ∧ ¬ Accepts right word := by
  simp only [checkSubset, Bool.not_eq_false', hasCounterexample_exact]
  exact ⟨fun ⟨word, _, accepted, rejected⟩ => ⟨word, accepted, rejected⟩,
    fun ⟨word, accepted, rejected⟩ => ⟨word, fun symbol _ => complete symbol, accepted, rejected⟩⟩

def checkEqual (alphabet : List Letter) (left : NFA Letter n) (right : NFA Letter m) : Bool :=
  checkSubset alphabet left right && checkSubset alphabet right left

theorem checkEqual_exact (alphabet : List Letter) (complete : ∀ symbol, symbol ∈ alphabet)
    (left : NFA Letter n) (right : NFA Letter m) :
    checkEqual alphabet left right = true ↔ ∀ word, Accepts left word ↔ Accepts right word := by
  simp only [checkEqual, Bool.and_eq_true, checkSubset_exact alphabet complete]
  exact ⟨fun ⟨forward, backward⟩ word => ⟨forward word, backward word⟩,
    fun same => ⟨fun word => (same word).mp, fun word => (same word).mpr⟩⟩

namespace Examples

def universal : NFA Bool 1 := ⟨fun _ => true, fun _ _ _ => true, fun _ => true⟩

def onlyTrue : NFA Bool 1 := ⟨fun _ => true, fun _ symbol _ => symbol, fun _ => true⟩

def zeroStates : NFA Bool 0 :=
  ⟨Fin.elim0, fun source => Fin.elim0 source, Fin.elim0⟩

def noInitialState : NFA Bool 1 :=
  ⟨fun _ => false, fun _ _ _ => true, fun _ => true⟩

theorem true_words_in_universal : checkSubset [false, true] onlyTrue universal = true := by decide

theorem universal_not_in_true_words : checkSubset [false, true] universal onlyTrue = false := by decide

theorem omitted_letter_is_outside_restricted_test : checkSubset [true] universal onlyTrue = true := by decide

theorem reflexive_language_equality : checkEqual [false, true] onlyTrue onlyTrue = true := by decide

theorem empty_word_counterexample_without_letters : checkSubset [] universal zeroStates = false := by decide

theorem zero_states_and_no_initial_state_agree :
    checkEqual [false, true] zeroStates noInitialState = true := by decide

/-- Repetition is unbounded; the inclusion test does not examine a fixed
prefix of this family. -/
theorem every_true_repetition_is_accepted (length : Nat) :
    Accepts onlyTrue (List.replicate length true) := by
  refine ⟨0, 0, rfl, ?_, rfl⟩
  induction length with
  | zero => exact .nil _
  | succ length ih => exact .cons rfl ih

theorem concrete_separating_word : Accepts universal [false] ∧ ¬ Accepts onlyTrue [false] := by
  constructor <;> decide

end Examples

end Yulang.FiniteAutomata
