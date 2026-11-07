import Yulang.CanonicalRegisterComposition

/-!
# Finite counter flowcharts with a return port

The return port is a control-flow label, not an oracle or an additional
machine instruction. A routine is a finite table of increment, decrement,
and jump instructions. This representation makes finite linking explicit.
-/

namespace Yulang.CanonicalRegisterMachine

namespace Routine

abbrev Store (registers : Nat) := Fin (registers + 1) → Nat

inductive Op (registers : Nat) (Label : Type) where
  | jump : Label → Op registers Label
  | increment : Fin (registers + 1) → Label → Op registers Label
  | decrement : Fin (registers + 1) → Label → Label → Op registers Label

def Op.map {registers : Nat} {First Last : Type} (f : First → Last) :
    Op registers First → Op registers Last
  | .jump next => .jump (f next)
  | .increment register next => .increment register (f next)
  | .decrement register zero positive => .decrement register (f zero) (f positive)

def Op.eval {registers : Nat} {Label : Type} (values : Store registers) :
    Op registers Label → Label × Store registers
  | .jump next => (next, values)
  | .increment register next => (next, write values register (values register + 1))
  | .decrement register zero positive =>
      if values register = 0 then (zero, values)
      else (positive, write values register (values register - 1))

theorem op_map_eval {registers : Nat} {First Last : Type}
    (f : First → Last) (op : Op registers First) (values : Store registers) :
    (op.map f).eval values = ((op.eval values).1 |> f, (op.eval values).2) := by
  cases op with
  | jump next => rfl
  | increment register next => rfl
  | decrement register zero positive =>
      simp only [Op.map, Op.eval]
      split <;> rfl

end Routine

structure Routine (registers : Nat) where
  states : Nat
  entry : Option (Fin states)
  code : Fin states → Routine.Op registers (Option (Fin states))

namespace Routine

inductive Trace {registers : Nat} (routine : Routine registers) :
    Option (Fin routine.states) → Store registers →
      Option (Fin routine.states) → Store registers → Prop where
  | refl : Trace routine location values location values
  | next : (routine.code location).eval values = (following, nextValues) →
      Trace routine following nextValues final finalValues →
        Trace routine (some location) values final finalValues

def Runs {registers : Nat} (routine : Routine registers)
    (values finalValues : Store registers) : Prop :=
  Trace routine routine.entry values none finalValues

/-- Concatenation of two finite execution traces. -/
theorem trace_trans {registers : Nat} {routine : Routine registers}
    {first middle last : Option (Fin routine.states)}
    {firstValues middleValues lastValues : Store registers}
    (firstTrace : Trace routine first firstValues middle middleValues)
    (lastTrace : Trace routine middle middleValues last lastValues) :
    Trace routine first firstValues last lastValues := by
  induction firstTrace with
  | refl => exact lastTrace
  | next moved _ ih => exact .next moved (ih lastTrace)

/-- Relabel a trace into another finite instruction table. The source's
return port may map to any continuation of the target. -/
theorem trace_map {registers : Nat} {source target : Routine registers}
    (labels : Option (Fin source.states) → Option (Fin target.states))
    (table : ∀ location, ∃ mapped,
      labels (some location) = some mapped ∧
      target.code mapped = (source.code location).map labels)
    {first last : Option (Fin source.states)} {values finalValues : Store registers}
    (trace : Trace source first values last finalValues) :
    Trace target (labels first) values (labels last) finalValues := by
  induction trace with
  | refl => exact .refl
  | @next location values following nextValues final finalValues moved _ ih =>
      obtain ⟨mapped, atMapped, instruction⟩ := table location
      rw [atMapped]
      apply Trace.next (following := labels following) (nextValues := nextValues) ?_ ih
      rw [instruction, op_map_eval, moved]

def rightLabel (firstStates : Nat) {lastStates : Nat} :
    Option (Fin lastStates) → Option (Fin (firstStates + lastStates)) :=
  Option.map (Fin.natAdd firstStates)

def leftLabel {firstStates lastStates : Nat} (lastEntry : Option (Fin lastStates)) :
    Option (Fin firstStates) → Option (Fin (firstStates + lastStates))
  | none => rightLabel firstStates lastEntry
  | some location => some (location.castAdd lastStates)

/-- Place two finite tables next to each other. Every return from the first
table goes to the second entry; every return from the second stays a return. -/
def append {registers : Nat} (first last : Routine registers) : Routine registers where
  states := first.states + last.states
  entry := leftLabel last.entry first.entry
  code := Fin.addCases
    (fun location => (first.code location).map (leftLabel last.entry))
    (fun location => (last.code location).map (rightLabel first.states))

theorem append_runs {registers : Nat} {first last : Routine registers}
    {values middleValues finalValues : Store registers}
    (firstRun : Runs first values middleValues)
    (lastRun : Runs last middleValues finalValues) :
    Runs (append first last) values finalValues := by
  have firstTrace := trace_map (target := append first last) (leftLabel last.entry)
    (fun location => ⟨location.castAdd last.states, rfl,
      Fin.addCases_left (motive := fun _ => Op registers (Option (Fin (first.states + last.states))))
        (left := fun index => (first.code index).map (leftLabel last.entry))
        (right := fun index => (last.code index).map (rightLabel first.states)) location⟩) firstRun
  have lastTrace := trace_map (target := append first last) (rightLabel first.states)
    (fun location => ⟨Fin.natAdd first.states location, rfl,
      Fin.addCases_right (motive := fun _ => Op registers (Option (Fin (first.states + last.states))))
        (left := fun index => (first.code index).map (leftLabel last.entry))
        (right := fun index => (last.code index).map (rightLabel first.states)) location⟩) lastRun
  exact trace_trans firstTrace lastTrace

def loopLabel {states : Nat} : Option (Fin states) → Option (Fin (states + 1))
  | none => some 0
  | some location => some location.succ

/-- While the selected counter is positive, decrement it and execute the
body. The body may restore that counter when an ordinary while is desired. -/
def loop {registers : Nat} (register : Fin (registers + 1))
    (body : Routine registers) : Routine registers where
  states := body.states + 1
  entry := some 0
  code := Fin.cases (.decrement register none (loopLabel body.entry))
    (fun location => (body.code location).map loopLabel)

inductive LoopRuns {registers : Nat} (register : Fin (registers + 1))
    (body : Routine registers) : Store registers → Store registers → Prop where
  | done : values register = 0 → LoopRuns register body values values
  | next : values register ≠ 0 →
      Runs body (write values register (values register - 1)) middleValues →
      LoopRuns register body middleValues finalValues →
        LoopRuns register body values finalValues

theorem loop_runs {registers : Nat} {register : Fin (registers + 1)}
    {body : Routine registers} {values finalValues : Store registers}
    (execution : LoopRuns register body values finalValues) :
    Runs (loop register body) values finalValues := by
  induction execution with
  | done empty =>
      apply Trace.next (following := none) (nextValues := _) ?_ .refl
      simp only [loop, Fin.cases_zero, Op.eval, empty, ↓reduceIte]
  | @next values middleValues finalValues positive bodyRun _ ih =>
      have bodyTrace := trace_map (target := loop register body) loopLabel
        (fun location => ⟨location.succ, rfl, by simp only [loop, Fin.cases_succ]⟩) bodyRun
      apply Trace.next (following := loopLabel body.entry)
        (nextValues := write values register (values register - 1)) ?_
        (trace_trans bodyTrace ih)
      simp only [loop, Fin.cases_zero, Op.eval, positive, ↓reduceIte]

def machineLabel {states : Nat} : Option (Fin states) → Fin (states + 1)
  | none => Fin.last states
  | some location => location.castSucc

def Op.instruction {registers states : Nat} :
    Op registers (Option (Fin states)) → Instruction registers (states + 1)
  | .jump next => .goto (machineLabel next)
  | .increment register next => .increment register (machineLabel next)
  | .decrement register zero positive =>
      .decrement register (machineLabel zero) (machineLabel positive)

/-- The return port becomes an ordinary halt instruction at the final
control location. Every other instruction is already a counter instruction. -/
def compile {registers : Nat} (routine : Routine registers) : Program where
  registers := registers
  states := routine.states + 1
  entry := machineLabel routine.entry
  code := List.ofFn (Fin.lastCases .halt (fun location => (routine.code location).instruction))

/-- Every finite flowchart trace is a finite nonterminal prefix of the
concretely generated register program, with exactly the same counter store. -/
theorem trace_compiled {registers : Nat} {routine : Routine registers}
    {first last : Option (Fin routine.states)} {values finalValues : Store registers}
    (trace : Trace routine first values last finalValues) :
    Reaches routine.compile ⟨machineLabel first, values⟩ ⟨machineLabel last, finalValues⟩ := by
  induction trace with
  | refl => exact .refl
  | @next location values following nextValues final finalValues moved _ ih =>
      apply Reaches.next ?_ ih
      have lookup : routine.compile.code[location.castSucc.val]?.getD .halt =
          (routine.code location).instruction := by
        change (List.ofFn (Fin.lastCases .halt
          (fun index => (routine.code index).instruction)))[location.val]?.getD .halt = _
        rw [List.getElem?_ofFn, dite_eq_left (Nat.lt_trans location.isLt (Nat.lt_succ_self _))]
        exact Fin.lastCases_castSucc (motive := fun _ => Instruction registers (routine.states + 1))
          (last := .halt) (cast := fun index => (routine.code index).instruction) location
      change step routine.compile ⟨location.castSucc, values⟩ = _
      unfold step
      rw [lookup]
      cases instruction : routine.code location with
      | jump next =>
          simp only [instruction, Op.eval, Prod.mk.injEq] at moved
          rcases moved with ⟨rfl, rfl⟩
          rfl
      | increment register next =>
          simp only [instruction, Op.eval, Prod.mk.injEq] at moved
          rcases moved with ⟨rfl, rfl⟩
          rfl
      | decrement register zero positive =>
          simp only [instruction, Op.eval] at moved
          simp only [Op.instruction]
          split at moved <;> rename_i condition
          · rw [ite_eq_left condition]
            cases moved
            rfl
          · rw [ite_eq_right condition]
            cases moved
            rfl

def atomic {registers : Nat} (op : Op registers Unit) : Routine registers where
  states := 1
  entry := some 0
  code := fun _ => op.map (fun _ => none)

theorem atomic_runs {registers : Nat} (op : Op registers Unit) (values : Store registers) :
    Runs (atomic op) values (op.eval values).2 := by
  apply Trace.next (following := none) (nextValues := _) ?_ .refl
  exact op_map_eval (fun _ => none) op values

end Routine

end Yulang.CanonicalRegisterMachine
