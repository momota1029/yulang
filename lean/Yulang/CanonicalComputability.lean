import Std

/-!
# An explicit finite machine language for canonicality obstructions

Programs are finite instruction lists over binary trees. They can construct
and inspect trees, store them in numbered registers, branch and loop. There
are no arbitrary semantic functions in program syntax. Execution is an
inductive finite derivation, not a total evaluator or a halting oracle.

This file supplies computational infrastructure only. Connecting these
programs to finite public interfaces is a separate required reduction.
-/

namespace Yulang.CanonicalComputability

inductive Data where
  | nil : Data
  | cons : Data → Data → Data
  deriving DecidableEq, Repr

def Data.left : Data → Data
  | .nil => .nil
  | .cons first _ => first

def Data.right : Data → Data
  | .nil => .nil
  | .cons _ last => last

inductive Expression where
  | constant : Data → Expression
  | read : Nat → Expression
  | cons : Expression → Expression → Expression
  | left : Expression → Expression
  | right : Expression → Expression
  deriving DecidableEq, Repr

def Expression.eval (store : Nat → Data) : Expression → Data
  | .constant value => value
  | .read index => store index
  | .cons first last => .cons (first.eval store) (last.eval store)
  | .left source => (source.eval store).left
  | .right source => (source.eval store).right

inductive Instruction where
  | halt : Bool → Instruction
  | assign : Nat → Expression → Nat → Instruction
  | branch : Expression → Nat → Nat → Instruction
  | goto : Nat → Instruction
  deriving DecidableEq, Repr

structure Program where
  code : List Instruction
  entry : Nat
  deriving DecidableEq, Repr

structure State where
  pc : Nat
  store : Nat → Data

/-- Missing instruction addresses halt with false. This explicit convention
is preserved by code relocation; it is not a well-formedness premise. -/
def step (program : Program) (state : State) : Bool ⊕ State :=
  match program.code[state.pc]?.getD (.halt false) with
  | .halt answer => .inl answer
  | .assign index expression next =>
      .inr ⟨next, fun register =>
        if register = index then expression.eval state.store else state.store register⟩
  | .branch expression yes no =>
      .inr ⟨if expression.eval state.store = .nil then no else yes, state.store⟩
  | .goto next => .inr ⟨next, state.store⟩

inductive Executes (program : Program) : State → Bool → Prop where
  | done : step program state = .inl answer → Executes program state answer
  | next : step program state = .inr following →
      Executes program following answer → Executes program state answer

def initialStore (input : Data) : Nat → Data :=
  fun register => if register = 0 then input else .nil

def Runs (program : Program) (input : Data) (answer : Bool) : Prop :=
  Executes program ⟨program.entry, initialStore input⟩ answer

def Halts (program : Program) (input : Data) : Prop := ∃ answer, Runs program input answer

/-- A finite deterministic execution cannot return two different answers.
No termination assumption, input restriction or state invariant is needed. -/
theorem executes_deterministic (program : Program) (state : State) (first last : Bool)
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

def divergeOnTrueInstruction : Instruction → Instruction
  | .halt true => .goto 0
  | .halt false => .halt false
  | .assign index expression next => .assign index expression (next + 1)
  | .branch expression yes no => .branch expression (yes + 1) (no + 1)
  | .goto next => .goto (next + 1)

def divergeOnTrue (program : Program) : Program :=
  ⟨.goto 0 :: program.code.map divergeOnTrueInstruction, program.entry + 1⟩

def relocate (state : State) : State := ⟨state.pc + 1, state.store⟩

/-- The new state zero is a trap; every old address, including an invalid
one, is shifted by one. No original transition is silently redirected. -/
theorem divergeOnTrue_step (program : Program) (state : State) :
    step (divergeOnTrue program) (relocate state) =
      match step program state with
      | .inl false => .inl false
      | .inl true => .inr ⟨0, state.store⟩
      | .inr following => .inr (relocate following) := by
  simp only [step, divergeOnTrue, relocate, List.getElem?_cons_succ, List.getElem?_map]
  cases found : program.code[state.pc]? with
  | none => rfl
  | some instruction =>
      cases instruction with
      | halt answer => cases answer <;> rfl
      | assign => rfl
      | goto => rfl
      | branch expression yes no =>
          by_cases empty : expression.eval state.store = .nil <;>
            simp [divergeOnTrueInstruction, empty]

end Yulang.CanonicalComputability
