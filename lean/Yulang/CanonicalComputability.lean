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

theorem divergeOnTrue_trap (program : Program) (state : State) (answer : Bool)
    (execution : Executes (divergeOnTrue program) state answer) (trap : state.pc = 0) : False := by
  revert trap
  induction execution with
  | @done state answer stopped =>
      intro trap
      have self : step (divergeOnTrue program) state = .inr state := by
        cases state
        simp_all [step, divergeOnTrue]
      cases stopped.symm.trans self
  | @next state following answer moved _ ih =>
      intro trap
      have self : step (divergeOnTrue program) state = .inr state := by
        cases state
        simp_all [step, divergeOnTrue]
      have same : following = state := Sum.inr.inj (moved.symm.trans self)
      exact ih (same ▸ trap)

theorem executes_divergeOnTrue_iff (program : Program) (state : State) (answer : Bool) :
    Executes (divergeOnTrue program) (relocate state) answer ↔
      answer = false ∧ Executes program state false := by
  constructor
  · intro execution
    have reflect (destination : State) (answer : Bool)
        (trace : Executes (divergeOnTrue program) destination answer) :
        ∀ source, destination = relocate source →
          answer = false ∧ Executes program source false := by
      induction trace with
      | @done destination answer stopped =>
          intro source same
          subst destination
          rw [divergeOnTrue_step] at stopped
          cases original : step program source with
          | inl value =>
              cases value with
              | false =>
                  simp only [original] at stopped
                  exact ⟨(Sum.inl.inj stopped).symm, .done original⟩
              | true => simp [original] at stopped
          | inr following => simp [original] at stopped
      | @next destination following answer moved rest ih =>
          intro source same
          subst destination
          rw [divergeOnTrue_step] at moved
          cases original : step program source with
          | inl value =>
              cases value with
              | false => simp [original] at moved
              | true =>
                  simp only [original] at moved
                  have atTrap := congrArg State.pc (Sum.inr.inj moved)
                  exact False.elim (divergeOnTrue_trap program following answer rest atTrap.symm)
          | inr next =>
              simp only [original] at moved
              obtain ⟨answerFalse, before⟩ := ih next (Sum.inr.inj moved).symm
              exact ⟨answerFalse, .next original before⟩
    exact reflect _ _ execution state rfl
  · rintro ⟨rfl, execution⟩
    have lift (source : State) (answer : Bool) (trace : Executes program source answer) :
        answer = false → Executes (divergeOnTrue program) (relocate source) answer := by
      induction trace with
      | done stopped =>
          intro answerFalse
          simp only [answerFalse] at stopped ⊢
          exact .done (by rw [divergeOnTrue_step, stopped])
      | next moved _ ih =>
          intro answerFalse
          exact .next (by rw [divergeOnTrue_step, moved]) (ih answerFalse)
    exact lift _ _ execution rfl

/-- No finite program decides self-halting. The theorem holds for every
representation of programs as finite input data, without assuming a universal
interpreter, a computable encoding, or a successful decision procedure. -/
theorem no_self_halting_decider (encoding : Program → Data) :
    ¬ ∃ decider : Program,
      (∀ program : Program, ∃ answer : Bool, Runs decider (encoding program) answer) ∧
      (∀ program : Program,
        Runs decider (encoding program) true ↔ Halts program (encoding program)) := by
  rintro ⟨decider, total, correct⟩
  let diagonal := divergeOnTrue decider
  let input := encoding diagonal
  have diagonal_exact : Halts diagonal input ↔ Runs decider input false := by
    change (∃ answer, Executes (divergeOnTrue decider)
      (relocate ⟨decider.entry, initialStore input⟩) answer) ↔ _
    simp only [executes_divergeOnTrue_iff, exists_eq_left]
    rfl
  obtain ⟨answer, execution⟩ := total diagonal
  cases answer with
  | false =>
      have accepts := (correct diagonal).mpr (diagonal_exact.mpr execution)
      have impossible := executes_deterministic decider _ false true execution accepts
      cases impossible
  | true =>
      have rejects := diagonal_exact.mp ((correct diagonal).mp execution)
      have impossible := executes_deterministic decider _ true false execution rejects
      cases impossible

end Yulang.CanonicalComputability
