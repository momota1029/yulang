import Std

/-!
# A finite register-counter computation model

Programs have a finite list of counter instructions, a finite declared control
set, and finitely many unbounded natural counters. Counter zero is the input
and output register. The `registers` field counts the additional registers,
so every program has at least this input/output register. There are no oracle
instructions, semantic functions, or proof fields in program syntax.

This model supports concrete finite preprocessing routines without requiring
an additional simulation back to exactly two counters.
-/

namespace Yulang.CanonicalRegisterMachine

inductive Instruction (registers states : Nat) where
  | halt : Instruction registers states
  | increment : Fin (registers + 1) → Fin states → Instruction registers states
  | decrement : Fin (registers + 1) → Fin states → Fin states → Instruction registers states
  | goto : Fin states → Instruction registers states
  deriving DecidableEq, Repr

structure Program where
  registers : Nat
  states : Nat
  entry : Fin states
  code : List (Instruction registers states)

structure State (registers states : Nat) where
  pc : Fin states
  values : Fin (registers + 1) → Nat

def write (values : Fin (registers + 1) → Nat) (register : Fin (registers + 1))
    (value : Nat) : Fin (registers + 1) → Nat :=
  fun current => if current = register then value else values current

/-- Missing table entries are explicit returns of counter zero. -/
def step (program : Program) (state : State program.registers program.states) :
    Nat ⊕ State program.registers program.states :=
  match program.code[state.pc.val]?.getD .halt with
  | .halt => .inl (state.values 0)
  | .increment register next =>
      .inr ⟨next, write state.values register (state.values register + 1)⟩
  | .decrement register zero positive =>
      if state.values register = 0 then .inr ⟨zero, state.values⟩
      else .inr ⟨positive, write state.values register (state.values register - 1)⟩
  | .goto next => .inr ⟨next, state.values⟩

inductive Executes (program : Program) : State program.registers program.states → Nat → Prop where
  | done : step program state = .inl output → Executes program state output
  | next : step program state = .inr following →
      Executes program following output → Executes program state output

def initial (program : Program) (input : Nat) : State program.registers program.states :=
  ⟨program.entry, fun register => if register = 0 then input else 0⟩

def Runs (program : Program) (input output : Nat) : Prop :=
  Executes program (initial program input) output

def Halts (program : Program) (input : Nat) : Prop := ∃ output, Runs program input output

/-- The complement of self-halting cannot even be semidecided by a program
of this model, under any representation. No totality, determinism, universal
interpreter, or computability premise on the representation is used. -/
theorem no_nonhalting_semidecider (encoding : Program → Nat) :
    ¬ ∃ recognizer : Program, ∀ program : Program,
      Halts recognizer (encoding program) ↔ ¬ Halts program (encoding program) := by
  rintro ⟨recognizer, correct⟩
  have self := correct recognizer
  have cannot : ¬ Halts recognizer (encoding recognizer) := fun halted => (self.mp halted) halted
  exact cannot (self.mpr cannot)

def Invariant (program : Program) (input : Nat)
    (safe : State program.registers program.states → Prop) : Prop :=
  safe (initial program input) ∧
    ∀ state, safe state →
      match step program state with
      | .inl _ => False
      | .inr following => safe following

/-- An arbitrary set invariant containing the initial configuration and
closed under nonterminal steps exists exactly for nonhalting computations.
The set need not be finite or computable. This matches the unrestricted
semantic row parameters; the interface itself will remain finite syntax. -/
theorem invariant_iff_nonhalting (program : Program) (input : Nat) :
    (∃ safe, Invariant program input safe) ↔ ¬ Halts program input := by
  constructor
  · rintro ⟨safe, starts, closed⟩ ⟨output, execution⟩
    have excludes (state : State program.registers program.states) (output : Nat)
        (trace : Executes program state output) : safe state → False := by
      induction trace with
      | done stopped =>
          intro present
          have impossible := closed _ present
          simp only [stopped] at impossible
      | next moved rest ih =>
          intro present
          apply ih
          have retained := closed _ present
          simpa only [moved] using retained
    exact excludes _ _ execution starts
  · intro nonhalting
    refine ⟨fun state => ¬ ∃ output, Executes program state output, nonhalting, ?_⟩
    intro state safe
    cases transition : step program state with
    | inl output => exact safe ⟨output, .done transition⟩
    | inr following =>
        rintro ⟨output, execution⟩
        exact safe ⟨output, .next transition execution⟩

end Yulang.CanonicalRegisterMachine
