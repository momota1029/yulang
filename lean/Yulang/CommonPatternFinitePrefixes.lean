import Yulang.CommonPatternComputationSafety
import Yulang.CommonCaseEffectPaths

/-! A concrete computation logic for finite prefixes, errors and returns.
`none` is an unfinished observation, distinct from a completed pattern miss.
Computations need not contain any terminating observation, and may contain
many observations. Source evaluation adequacy is deliberately not assumed
to follow from this construction. -/

namespace Yulang.CommonPatternFinitePrefixes

open CommonPatternComputations (Ops)
open CommonPatternComputationSafety (Logic)
open CommonCaseEffectPaths (traceRow traceRow_append)
open CaseEvaluation (Event)

structure Observation (E R A : Type) where
  trace : List (Event E)
  result : Option (Except R A)

abbrev Computation (E R A : Type) := Observation E R A → Prop

def ret (value : A) : Computation E R A := fun observed =>
  observed = ⟨[], none⟩ ∨ observed = ⟨[], some (.ok value)⟩

inductive Bind (first : Computation E R A) (next : A → Computation E R B) : Computation E R B where
  | pending (trace) : first ⟨trace, none⟩ → Bind first next ⟨trace, none⟩
  | error (trace) (error : R) : first ⟨trace, some (.error error)⟩ → Bind first next ⟨trace, some (.error error)⟩
  | returned (trace) (value : A) (later : Observation E R B) :
      first ⟨trace, some (.ok value)⟩ → next value later →
        Bind first next ⟨trace ++ later.trace, later.result⟩

def ops (E R : Type) : Ops (Computation E R) := ⟨ret, Bind⟩

def resultRow (failure : R → Common.Row) : Option (Except R A) → Common.Row
  | some (.error error) => failure error
  | _ => Common.rowEmpty

def observationRow (source : E → Common.Row) (failure : R → Common.Row) (observed : Observation E R A) : Common.Row :=
  Common.rowJoin (traceRow source observed.trace) (resultRow failure observed.result)

def Safe (source : E → Common.Row) (failure : R → Common.Row) (computation : Computation E R A)
    (post : A → Prop) (cap : Common.Row) : Prop :=
  ∀ observed, computation observed → Common.rowLe (observationRow source failure observed) cap ∧
    ∀ value, observed.result = some (.ok value) → post value

theorem ret_safe (source : E → Common.Row) (failure : R → Common.Row) (value : A) (post : A → Prop)
    (cap : Common.Row) (valid : post value) : Safe source failure (ret value) post cap := by
  intro observed present
  rcases present with rfl | rfl
  · constructor
    · intro occurrence within
      rcases within with impossible | impossible <;> exact False.elim impossible
    · intro returned impossible
      cases impossible
  · constructor
    · intro occurrence within
      rcases within with impossible | impossible <;> exact False.elim impossible
    · intro returned same
      cases same
      exact valid

theorem bind_safe (source : E → Common.Row) (failure : R → Common.Row)
    (first : Computation E R A) (next : A → Computation E R B) (pre : A → Prop) (post : B → Prop)
    (cap : Common.Row) (firstSafe : Safe source failure first pre cap)
    (nextSafe : ∀ value, pre value → Safe source failure (next value) post cap) :
    Safe source failure (Bind first next) post cap := by
  intro observed present
  cases present with
  | pending trace within =>
      have head := firstSafe ⟨trace, none⟩ within
      refine ⟨head.1, ?_⟩
      intro value impossible
      cases impossible
  | error trace error within =>
      have head := firstSafe ⟨trace, some (.error error)⟩ within
      refine ⟨head.1, ?_⟩
      intro value impossible
      cases impossible
  | returned trace value later head tail =>
      have earlier := firstSafe ⟨trace, some (.ok value)⟩ head
      have after := nextSafe value (earlier.2 value rfl) later tail
      constructor
      · intro occurrence within
        have split : traceRow source trace occurrence ∨ observationRow source failure later occurrence := by
          simpa only [observationRow, traceRow_append, Common.rowJoin, or_assoc] using within
        rcases split with firstPart | lastPart
        · exact earlier.1 occurrence (Or.inl firstPart)
        · exact after.1 occurrence lastPart
      · exact after.2

def logic (source : E → Common.Row) (failure : R → Common.Row) : Logic (ops E R) where
  Safe := Safe source failure
  ret_safe := ret_safe source failure
  bind_safe := fun {A B} {first next pre post cap} => bind_safe source failure first next pre post cap
  weaken := by
    intro A computation pre post cap safe implication observed present
    have result := safe observed present
    exact ⟨result.1, fun value returned => implication value (result.2 value returned)⟩

/-- A computation may diverge silently: it has an unfinished empty prefix
and no error or return. It satisfies every postcondition and every row cap. -/
def silent : Computation E R A := fun observed => observed = ⟨[], none⟩

theorem silent_safe (source : E → Common.Row) (failure : R → Common.Row)
    (post : A → Prop) (cap : Common.Row) : Safe source failure silent post cap := by
  intro observed same
  cases same
  constructor
  · intro occurrence impossible
    rcases impossible with left | right <;> exact False.elim ‹False›
  · intro value impossible
    cases impossible

theorem silent_has_no_completion (trace : List (Event E)) (result : Except R A) :
    ¬ silent (⟨trace, some result⟩ : Observation E R A) := by
  intro same
  cases same

/-- The structural theorem applies to every finite prefix of defaults
with arbitrary nondeterminism, failure or nontermination. Only the stated
partial source-default contract is required. -/
theorem typing_finite_prefixes (source : E → Common.Row) (failure : R → Common.Row) (cap : Common.Row)
    (floatCheck : Empty → Empty → Bool)
    (evaluate : CaseValues.Bindings Empty → D → Computation E R Core.CommonData.Value)
    (defaults : CommonPatternComputationSafety.DefaultSound (logic source failure) cap DefaultTyped evaluate)
    (typed : CommonAlignedPatternTyping.Typing DefaultTyped types pattern input bindings)
    (actual : CaseValues.Bindings Empty)
    (env : CaseValues.BindingsHold (CommonPatternTyping.bindingTypes types) actual)
    (subject : Core.CommonData.Value) (within : CommonPatternTyping.valueAt input subject) :
    Safe source failure (CommonPatternComputations.run (ops E R) floatCheck evaluate actual pattern subject)
      (CommonPatternComputationSafety.OptionHolds bindings) cap :=
  CommonPatternComputationSafety.typing_safe (logic source failure) cap floatCheck evaluate defaults
    typed.2 typed.1 actual env subject within

end Yulang.CommonPatternFinitePrefixes
