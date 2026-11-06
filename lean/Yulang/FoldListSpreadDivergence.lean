import Yulang.FoldListSpread

/-!
# A nonterminating Fold cannot advance to later list elements

If every valid traversal state has another internal step, item or request,
the surrounding list machine keeps exactly the same remaining source syntax
at every finite prefix. Its accumulation may grow and requests may suspend,
but it cannot return a list or start the later source occurrences.

The example supplies a locally typed infinite repetition protocol and a
nonempty independently typed literal containing an ordinary prefix element,
that spread, and a later element. This is a resolved protocol example, not a
claim that its arbitrary source method has been elaborated.
-/

namespace Yulang.FoldListSpreadDivergence

open Directed SignatureRequests FoldListSpread

section General

variable {Key Value Source Conversion Dictionary SourceState FoldState : Type}
variable {n : Nat} {signature : Signature Key}
variable {engine : Engine n signature Source Conversion Dictionary Value SourceState FoldState}

def Traversing (dictionary : Dictionary) (rest : List (Part Source Conversion Dictionary))
    (valid : FoldState → Prop)
    (configuration : Configuration Source Conversion Dictionary Value SourceState FoldState) : Prop :=
  ∃ cursor, configuration.control = .traversing dictionary rest cursor ∧ valid cursor

theorem perpetual_observe (dictionary : Dictionary) (rest : List (Part Source Conversion Dictionary))
    (safe : FoldTraversal.Safe (engine.fold dictionary).observe valid itemType row)
    (noEnd : ∀ cursor, valid cursor → (engine.fold dictionary).observe cursor ≠ .done)
    (configuration : Configuration Source Conversion Dictionary Value SourceState FoldState)
    (inside : Traversing dictionary rest valid configuration) :
    match engine.observe configuration with
    | .value _ => False
    | .tick next => Traversing dictionary rest valid next
    | .request occurrence _ resume => row occurrence ∧ ∀ response, Traversing dictionary rest valid (resume response) := by
  rcases configuration with ⟨values, control⟩
  rcases inside with ⟨cursor, rfl, cursorValid⟩
  cases observed : (engine.fold dictionary).observe cursor with
  | done => exact False.elim (noEnd cursor cursorValid observed)
  | tick next =>
      simp only [Engine.observe, observed]
      exact ⟨next, rfl, safe.tick _ _ cursorValid observed⟩
  | yield item next =>
      simp only [Engine.observe, observed]
      exact ⟨next, rfl, (safe.yield _ _ _ cursorValid observed).2⟩
  | request occurrence payload resume =>
      simp only [Engine.observe, observed]
      obtain ⟨allowed, resumes⟩ := safe.request _ _ _ _ cursorValid observed
      exact ⟨allowed, fun response => ⟨resume response, rfl, resumes response⟩⟩

theorem perpetual_safe (dictionary : Dictionary) (rest : List (Part Source Conversion Dictionary))
    (safe : FoldTraversal.Safe (engine.fold dictionary).observe valid itemType row)
    (noEnd : ∀ cursor, valid cursor → (engine.fold dictionary).observe cursor ≠ .done) :
    Safe engine.observe (Traversing dictionary rest valid) (fun _ => False) row := by
  constructor
  · intro configuration value inside observed
    have held := perpetual_observe dictionary rest safe noEnd configuration inside
    simp only [observed] at held
  · intro configuration next inside observed
    have held := perpetual_observe dictionary rest safe noEnd configuration inside
    simpa only [observed] using held
  · intro configuration occurrence payload resume inside observed
    have held := perpetual_observe dictionary rest safe noEnd configuration inside
    simpa only [observed] using held

theorem no_later_source_or_return (dictionary : Dictionary) (rest : List (Part Source Conversion Dictionary))
    (safe : FoldTraversal.Safe (engine.fold dictionary).observe valid itemType row)
    (noEnd : ∀ cursor, valid cursor → (engine.fold dictionary).observe cursor ≠ .done)
    (cursorValid : valid cursor)
    (observedPrefix : Prefix engine.observe ⟨values, .traversing dictionary rest cursor⟩ requests last) :
    Traversing dictionary rest valid last ∧ (∀ request ∈ requests, row request) ∧
      ∀ result, engine.observe last ≠ .value result := by
  have machineSafe := perpetual_safe dictionary rest safe noEnd
  obtain ⟨inside, allowed⟩ := prefix_safe machineSafe ⟨cursor, rfl, cursorValid⟩ observedPrefix
  exact ⟨inside, allowed, fun result returned => machineSafe.value _ _ inside returned⟩

end General

namespace Examples

abbrev emptySignature := Signature.constant Empty Unit Unit

def engine : Engine 0 emptySignature Nat Unit Unit Nat Nat Nat where
  startSource := id
  source := .value
  convert _ := id
  fold _ := ⟨id, fun value => .yield value value⟩

def contracts : Contracts engine where
  SourceTyped code input _ := input code
  ConversionTyped _ input output := ∀ value, input value → output value
  FoldTyped _ container item _ := ∀ value, container value → item value
  SourceValid state input _ := input state
  FoldValid _ state item _ := item state
  source_start := by intro code input row typed; exact typed
  source_safe := by
    intro input row
    constructor
    · intro state value typed observed; cases observed; exact typed
    · intro state next typed observed; cases observed
    · intro state occurrence payload resume typed observed; cases observed
  conversion_safe := by intro conversion input output typed value held; exact typed value held
  fold_start := by intro dictionary input item row typed value held; exact typed value held
  fold_safe := by
    intro dictionary item row
    constructor
    · intro state next typed observed; cases observed
    · intro state value next typed observed; cases observed; exact ⟨typed, typed⟩
    · intro state occurrence payload resume typed observed; cases observed

def parts : List (Part Nat Unit Unit) := [.element 3 (), .spread 7 (), .element 11 ()]
def itemTypes : List (Nat → Prop) := [(· = 3), (· = 7), (· = 11)]
def rows : List (Occurrence 0 Empty → Prop) := [fun _ => False, fun _ => False ∨ False, fun _ => False]

theorem literal_typed : Typing contracts parts itemTypes rows := by
  exact .cons (.element (input := (· = 3)) rfl (fun _ held => held))
    (.cons (.spread (container := (· = 7)) rfl (fun _ held => held))
      (.cons (.element (input := (· = 11)) rfl (fun _ held => held)) .nil))

theorem reaches_repeat : Prefix engine.observe (start parts) []
    ⟨[3], .traversing () [.element 11 ()] 7⟩ := by
  have first : Step engine.observe (start parts) []
      ⟨[], .evaluating (.element 3 ()) [.spread 7 (), .element 11 ()] 3⟩ := .tick rfl
  have second : Step engine.observe
      ⟨[], .evaluating (.element 3 ()) [.spread 7 (), .element 11 ()] 3⟩ []
      ⟨[3], .ready [.spread 7 (), .element 11 ()]⟩ := .tick rfl
  have third : Step engine.observe ⟨[3], .ready [.spread 7 (), .element 11 ()]⟩ []
      ⟨[3], .evaluating (.spread 7 ()) [.element 11 ()] 7⟩ := .tick rfl
  have fourth : Step engine.observe ⟨[3], .evaluating (.spread 7 ()) [.element 11 ()] 7⟩ []
      ⟨[3], .traversing () [.element 11 ()] 7⟩ := .tick rfl
  exact .cons first (.cons second (.cons third (.cons fourth .refl)))

theorem repeat_stage_never_returns
    (observedPrefix : Prefix engine.observe ⟨[3], .traversing () [.element 11 ()] 7⟩ requests last) :
    Traversing () [.element 11 ()] (· = 7) last ∧
      ∀ result, engine.observe last ≠ .value result := by
  have noEnd : ∀ cursor, cursor = 7 → (engine.fold ()).observe cursor ≠ .done := by
    intro cursor typed impossible
    cases impossible
  have held := no_later_source_or_return () [.element 11 ()]
    (contracts.fold_safe () (· = 7) (fun _ => False)) noEnd rfl observedPrefix
  exact ⟨held.1, held.2.2⟩

/-- The nonterminating stage remains covered by the same type/effect safety
theorem as the finite kernel, with the union of all three contribution types. -/
theorem repeat_stage_safe
    (observedPrefix : Prefix engine.observe ⟨[3], .traversing () [.element 11 ()] 7⟩ requests last) :
    ConfigurationTyped contracts (union itemTypes) (union rows) last ∧
      ∀ request ∈ requests, union rows request := by
  exact typed_prefix contracts literal_typed (reaches_repeat.trans observedPrefix)

end Examples

end Yulang.FoldListSpreadDivergence
