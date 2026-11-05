import Yulang.SemilinearDigits
import Yulang.FiniteAutomata

/-!
# Exact finite automata for arbitrary semilinear integer sets

A state records a linear component and a bounded carry. Each signed input
digit is matched with one binary digit of every natural period coefficient.
The transition equation is `carry + periodDigit = inputDigit + 2 * nextCarry`.
At the end of a word, the existing total span decision checks the remaining
high coefficient digits. Consequently every finite encoding of an integer
vector has the same acceptance result; zero-padding conventions introduce no
exception to language inclusion.

Together with signed-word surjectivity and finite NFA inclusion, this yields
total executable containment and equality decisions for all finite
semilinear subsets of `Fin n → Int`, including mixed signs and cancellation.
The construction is a reference decision procedure, not a performance claim
for a production row solver.
-/

namespace Yulang.SemilinearAutomata

open SemilinearWeights BinaryCarries
open SemilinearDigits (Letter digit value)
open SemilinearDecisions (subtract)

variable {n : Nat}

def lineBound (line : Linear n) : Nat := max (norm line.base) (budget line.periods + 1)

def Step (line : Linear n) (letter : Letter n) (current next : Weight n) : Prop :=
  ∃ selected ∈ digits line.periods,
    add current selected = add (digit letter) (scale 2 next)

def Residual (line : Linear n) (word : List (Letter n)) (carry : Weight n) : Prop :=
  Span line.periods (subtract (value word) carry)

theorem step_bounded (line : Linear n) (letter : Letter n) (current next : Weight n)
    (bounded : Within (lineBound line) current) (step : Step line letter current next) :
    Within (lineBound line) next := by
  obtain ⟨selected, member, equation⟩ := step
  have selectedBound := BinaryCarries.digit_bounded line.periods selected member
  have inputBound := SemilinearDigits.digit_bounded letter
  have large : budget line.periods + 1 ≤ lineBound line := Nat.le_max_right _ _
  intro coordinate
  have c := bounded coordinate
  have a := selectedBound coordinate
  have d := inputBound coordinate
  have eqn := congrFun equation coordinate
  simp only [add, scale] at eqn
  omega

theorem step_sound (line : Linear n) (letter : Letter n) (word : List (Letter n))
    (current next : Weight n) (step : Step line letter current next)
    (tail : Residual line word next) : Residual line (letter :: word) current := by
  obtain ⟨selected, member, equation⟩ := step
  have represented := (digit_span line.periods selected member).append
    (scale_span line.periods 2 _ tail)
  have same : subtract (value (letter :: word)) current =
      add selected (scale 2 (subtract (value word) next)) := by
    funext coordinate
    have eqn := congrFun equation coordinate
    simp only [value, add, scale, subtract] at eqn ⊢
    omega
  unfold Residual
  rw [same]
  exact represented

theorem step_complete (line : Linear n) (letter : Letter n) (word : List (Letter n))
    (current : Weight n) (bounded : Within (lineBound line) current)
    (member : Residual line (letter :: word) current) :
    ∃ next, Within (lineBound line) next ∧ Step line letter current next ∧ Residual line word next := by
  obtain ⟨counts, length, equality⟩ := span_coefficients line.periods _ member
  let selected := combine line.periods (counts.map (fun count => count % 2))
  let tail := combine line.periods (counts.map (fun count => count / 2))
  let next := subtract (value word) tail
  have chosen : selected ∈ digits line.periods := coefficient_digit line.periods counts length
  have split : subtract (value (letter :: word)) current = add selected (scale 2 tail) :=
    equality.symm.trans (coefficient_split line.periods counts)
  have equation : add current selected = add (digit letter) (scale 2 next) := by
    funext coordinate
    have point := congrFun split coordinate
    simp only [value, add, scale, subtract, next] at point ⊢
    omega
  have step : Step line letter current next := ⟨selected, chosen, equation⟩
  refine ⟨next, step_bounded line letter current next bounded step, step, ?_⟩
  have same : subtract (value word) next = tail := by
    funext coordinate
    simp only [next, subtract]
    omega
  unfold Residual
  rw [same]
  exact combine_span line.periods _

structure State (n components : Nat) where
  component : Fin components
  carry : Weight n

def states (semi : Semi n) : List (State n semi.length) :=
  (List.finRange semi.length).flatMap fun component =>
    (SemilinearDecisions.box (lineBound (semi.get component)) n).map (State.mk component)

theorem states_exact (semi : Semi n) (state : State n semi.length) :
    state ∈ states semi ↔ Within (lineBound (semi.get state.component)) state.carry := by
  constructor
  · intro member
    obtain ⟨component, _, mapped⟩ := List.mem_flatMap.mp member
    obtain ⟨carry, present, rfl⟩ := List.mem_map.mp mapped
    exact (SemilinearDecisions.box_exact _ _).mp present
  · intro bounded
    apply List.mem_flatMap.mpr
    exact ⟨state.component, by simp,
      List.mem_map.mpr ⟨state.carry, (SemilinearDecisions.box_exact _ _).mpr bounded, rfl⟩⟩

abbrev Vertex (semi : Semi n) := Fin (states semi).length

def stateAt (semi : Semi n) (vertex : Vertex semi) : State n semi.length := (states semi).get vertex

def lineAt (semi : Semi n) (vertex : Vertex semi) : Linear n := semi.get (stateAt semi vertex).component

theorem at_bounded (semi : Semi n) (vertex : Vertex semi) :
    Within (lineBound (lineAt semi vertex)) (stateAt semi vertex).carry :=
  (states_exact semi _).mp (List.get_mem _ vertex)

theorem at_complete (semi : Semi n) (component : Fin semi.length) (carry : Weight n)
    (bounded : Within (lineBound (semi.get component)) carry) :
    ∃ vertex, stateAt semi vertex = ⟨component, carry⟩ :=
  List.get_of_mem ((states_exact semi ⟨component, carry⟩).mpr bounded)

def weightEqual (left right : Weight n) : Bool := decide (∀ coordinate, left coordinate = right coordinate)

theorem weightEqual_exact (left right : Weight n) : weightEqual left right = true ↔ left = right := by
  simp only [weightEqual, decide_eq_true_eq]
  exact ⟨funext, congrFun⟩

def checkStep (line : Linear n) (letter : Letter n) (current next : Weight n) : Bool :=
  (digits line.periods).any fun selected =>
    weightEqual (add current selected) (add (digit letter) (scale 2 next))

theorem checkStep_exact (line : Linear n) (letter : Letter n) (current next : Weight n) :
    checkStep line letter current next = true ↔ Step line letter current next := by
  simp only [checkStep, List.any_eq_true, weightEqual_exact, Step]

def negate (weight : Weight n) : Weight n := fun coordinate => -(weight coordinate)

def automaton (semi : Semi n) : FiniteAutomata.NFA (Letter n) (states semi).length where
  initial vertex := weightEqual (stateAt semi vertex).carry (lineAt semi vertex).base
  transition source letter target :=
    decide ((stateAt semi source).component = (stateAt semi target).component) &&
      checkStep (lineAt semi source) letter (stateAt semi source).carry (stateAt semi target).carry
  accepting vertex := SemilinearDecisions.checkSpan (lineAt semi vertex).periods (negate (stateAt semi vertex).carry)

theorem initial_exact (semi : Semi n) (vertex : Vertex semi) :
    (automaton semi).initial vertex = true ↔ (stateAt semi vertex).carry = (lineAt semi vertex).base :=
  weightEqual_exact _ _

theorem transition_exact (semi : Semi n) (source target : Vertex semi) (letter : Letter n) :
    (automaton semi).transition source letter target = true ↔
      (stateAt semi source).component = (stateAt semi target).component ∧
        Step (lineAt semi source) letter (stateAt semi source).carry (stateAt semi target).carry := by
  simp only [automaton, Bool.and_eq_true, decide_eq_true_eq, checkStep_exact]

theorem accepting_exact (semi : Semi n) (vertex : Vertex semi) :
    (automaton semi).accepting vertex = true ↔ Residual (lineAt semi vertex) [] (stateAt semi vertex).carry := by
  rw [show (automaton semi).accepting vertex =
    SemilinearDecisions.checkSpan (lineAt semi vertex).periods (negate (stateAt semi vertex).carry) from rfl,
    SemilinearDecisions.checkSpan_exact]
  have same : negate (stateAt semi vertex).carry = subtract (value []) (stateAt semi vertex).carry := by
    funext coordinate
    simp [negate, subtract, value, zero]
  rw [same]
  rfl

theorem runs_sound (semi : Semi n) {source target : Vertex semi} {word : List (Letter n)}
    (run : FiniteAutomata.Runs (automaton semi) source word target)
    (accepted : (automaton semi).accepting target = true) :
    Residual (lineAt semi source) word (stateAt semi source).carry := by
  induction run with
  | nil state => exact (accepting_exact semi state).mp accepted
  | @cons source letter middle rest target step tail ih =>
      obtain ⟨component, relation⟩ := (transition_exact semi source middle letter).mp step
      have same : lineAt semi source = lineAt semi middle := congrArg semi.get component
      apply step_sound (lineAt semi source) letter rest (stateAt semi source).carry (stateAt semi middle).carry relation
      rw [same]
      exact ih accepted

theorem runs_complete (semi : Semi n) (word : List (Letter n)) (source : Vertex semi)
    (member : Residual (lineAt semi source) word (stateAt semi source).carry) :
    ∃ target, FiniteAutomata.Runs (automaton semi) source word target ∧
      (automaton semi).accepting target = true := by
  induction word generalizing source with
  | nil => exact ⟨source, .nil source, (accepting_exact semi source).mpr member⟩
  | cons letter rest ih =>
      obtain ⟨nextCarry, bounded, step, tail⟩ :=
        step_complete (lineAt semi source) letter rest _ (at_bounded semi source) member
      obtain ⟨middle, chosen⟩ := at_complete semi (stateAt semi source).component nextCarry bounded
      have component : (stateAt semi source).component = (stateAt semi middle).component := by rw [chosen]
      have same : lineAt semi middle = lineAt semi source := congrArg semi.get component.symm
      have tailAt : Residual (lineAt semi middle) rest (stateAt semi middle).carry := by
        rw [same, chosen]
        exact tail
      obtain ⟨target, reached, accepted⟩ := ih middle tailAt
      refine ⟨target, .cons ((transition_exact semi source middle letter).mpr ⟨component, ?_⟩) reached, accepted⟩
      rw [chosen]
      exact step

/-- Every word is interpreted by its integer value. The theorem includes
short encodings and arbitrarily many trailing zero letters. -/
theorem accepts_exact (semi : Semi n) (word : List (Letter n)) :
    FiniteAutomata.Accepts (automaton semi) word ↔ Meaning semi (value word) := by
  constructor
  · rintro ⟨source, target, initial, run, accepted⟩
    have remainder := runs_sound semi run accepted
    have start := (initial_exact semi source).mp initial
    refine ⟨lineAt semi source, List.get_mem semi (stateAt semi source).component, ?_⟩
    apply (SemilinearDecisions.linear_iff_span _ _).mpr
    rw [start] at remainder
    exact remainder
  · rintro ⟨line, present, member⟩
    obtain ⟨component, selected⟩ := List.get_of_mem present
    have bounded : Within (lineBound (semi.get component)) line.base := by
      rw [selected]
      exact (within_norm line.base).mono (Nat.le_max_left _ _)
    obtain ⟨source, chosen⟩ := at_complete semi component line.base bounded
    have sourceLine : lineAt semi source = line := by simp only [lineAt, chosen, selected]
    have sourceCarry : (stateAt semi source).carry = line.base := by rw [chosen]
    have remainder : Residual (lineAt semi source) word (stateAt semi source).carry := by
      rw [sourceLine, sourceCarry]
      exact (SemilinearDecisions.linear_iff_span _ _).mp member
    obtain ⟨target, reached, accepted⟩ := runs_complete semi word source remainder
    refine ⟨source, target, (initial_exact semi source).mpr ?_, reached, accepted⟩
    rw [sourceLine, sourceCarry]

def alphabet (n : Nat) : List (Letter n) := List.finRange _

theorem alphabet_complete (letter : Letter n) : letter ∈ alphabet n := by simp [alphabet]

theorem normalized_accepts_exact (semi : Semi n) (word : List (Letter n)) :
    FiniteAutomata.Accepts (automaton (SemilinearNormalization.normalize semi)) word ↔
      Meaning semi (value word) :=
  (accepts_exact _ word).trans (SemilinearNormalization.normalize_exact semi (value word))

def checkSubset (source target : Semi n) : Bool :=
  FiniteAutomata.checkSubset (alphabet n)
    (automaton (SemilinearNormalization.normalize source))
    (automaton (SemilinearNormalization.normalize target))

/-- Finite NFA inclusion decides semantic containment at every integer vector,
not merely at a supplied collection of sample weights. -/
theorem checkSubset_exact (source target : Semi n) :
    checkSubset source target = true ↔ ∀ weight, Meaning source weight → Meaning target weight := by
  rw [checkSubset, FiniteAutomata.checkSubset_exact _ alphabet_complete]
  constructor
  · intro included weight member
    obtain ⟨word, represented⟩ := SemilinearDigits.value_surjective weight
    rw [← represented] at member ⊢
    exact (normalized_accepts_exact target word).mp
      (included word ((normalized_accepts_exact source word).mpr member))
  · intro included word accepted
    exact (normalized_accepts_exact target word).mpr
      (included _ ((normalized_accepts_exact source word).mp accepted))

theorem checkSubset_rejects (source target : Semi n) :
    checkSubset source target = false ↔ ∃ weight, Meaning source weight ∧ ¬ Meaning target weight := by
  rw [checkSubset, FiniteAutomata.checkSubset_rejects _ alphabet_complete]
  constructor
  · rintro ⟨word, accepted, rejected⟩
    exact ⟨value word, (normalized_accepts_exact source word).mp accepted,
      fun member => rejected ((normalized_accepts_exact target word).mpr member)⟩
  · rintro ⟨weight, member, absent⟩
    obtain ⟨word, represented⟩ := SemilinearDigits.value_surjective weight
    rw [← represented] at member absent
    exact ⟨word, (normalized_accepts_exact source word).mpr member,
      fun accepted => absent ((normalized_accepts_exact target word).mp accepted)⟩

def checkEqual (left right : Semi n) : Bool := checkSubset left right && checkSubset right left

theorem checkEqual_exact (left right : Semi n) :
    checkEqual left right = true ↔ ∀ weight, Meaning left weight ↔ Meaning right weight := by
  simp only [checkEqual, Bool.and_eq_true, checkSubset_exact]
  exact ⟨fun ⟨forward, backward⟩ weight => ⟨forward weight, backward weight⟩,
    fun same => ⟨fun weight => (same weight).mp, fun weight => (same weight).mpr⟩⟩

theorem checkEqual_sets (left right : Semi n) :
    checkEqual left right = true ↔ Meaning left = Meaning right := by
  rw [checkEqual_exact]
  exact ⟨fun same => funext (fun weight => propext (same weight)),
    fun same weight => by rw [same]⟩

end Yulang.SemilinearAutomata
