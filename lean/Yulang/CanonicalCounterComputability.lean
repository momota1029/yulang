import Std

/-!
# Finite two-counter programs

This is the ordinary counter-machine instruction set: increment, zero-test
or decrement, goto, and a Boolean halt. Program counters range over a finite
declared state set. Missing table entries halt with false. Counters are
unbounded natural numbers, and execution is a finite inductive derivation.
-/

namespace Yulang.CanonicalCounterComputability

inductive Counter where
  | first | last
  deriving DecidableEq, Repr

abbrev Counters := Nat × Nat

def Counters.read (values : Counters) : Counter → Nat
  | .first => values.1
  | .last => values.2

def Counters.write (values : Counters) (counter : Counter) (value : Nat) : Counters :=
  match counter with
  | .first => (value, values.2)
  | .last => (values.1, value)

inductive Instruction (states : Nat) where
  | halt : Bool → Instruction states
  | increment : Counter → Fin states → Instruction states
  | decrement : Counter → Fin states → Fin states → Instruction states
  | goto : Fin states → Instruction states
  deriving DecidableEq, Repr

structure Program where
  states : Nat
  entry : Fin states
  code : List (Instruction states)

structure State (states : Nat) where
  pc : Fin states
  counters : Counters
  deriving DecidableEq, Repr

def step (program : Program) (state : State program.states) : Bool ⊕ State program.states :=
  match program.code[state.pc.val]?.getD (.halt false) with
  | .halt answer => .inl answer
  | .increment counter next => .inr ⟨next,
      state.counters.write counter (state.counters.read counter + 1)⟩
  | .decrement counter zero positive =>
      if state.counters.read counter = 0 then .inr ⟨zero, state.counters⟩
      else .inr ⟨positive, state.counters.write counter (state.counters.read counter - 1)⟩
  | .goto next => .inr ⟨next, state.counters⟩

inductive Executes (program : Program) : State program.states → Bool → Prop where
  | done : step program state = .inl answer → Executes program state answer
  | next : step program state = .inr following →
      Executes program following answer → Executes program state answer

def Runs (program : Program) (input : Nat) (answer : Bool) : Prop :=
  Executes program ⟨program.entry, (input, 0)⟩ answer

def Halts (program : Program) (input : Nat) : Prop := ∃ answer, Runs program input answer

/-- Determinism holds without any assumption that execution terminates. -/
theorem executes_deterministic (program : Program) (state : State program.states) (first last : Bool)
    (before : Executes program state first) (after : Executes program state last) : first = last := by
  induction before with
  | done stopped =>
      cases after with
      | done other => exact Sum.inl.inj (stopped.symm.trans other)
      | next other _ => cases stopped.symm.trans other
  | next moved _ ih =>
      cases after with
      | done other => cases moved.symm.trans other
      | next other rest =>
          have same := Sum.inr.inj (moved.symm.trans other)
          subst same
          exact ih rest

end Yulang.CanonicalCounterComputability
