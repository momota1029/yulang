import Yulang.CanonicalRegisterCalls
import Yulang.CanonicalRegisterMacros
import Yulang.CanonicalRegisterComparison
namespace Yulang.CanonicalRegisterGuard
open Yulang.CanonicalRegisterMachine
open Yulang.CanonicalRegisterMachine.Routine

theorem compiled_lookup (routine : Routine registers) (location : Fin routine.states) :
    routine.compile.code[location.val]?.getD .halt = (routine.code location).instruction := by
  change (List.ofFn (Fin.lastCases .halt
    (fun index => (routine.code index).instruction)))[location.val]?.getD .halt = _
  rw [List.getElem?_ofFn, dite_eq_left (Nat.lt_trans location.isLt (Nat.lt_succ_self _))]
  exact Fin.lastCases_castSucc (motive := fun _ => Instruction registers (routine.states + 1))
    (last := .halt) (cast := fun index => (routine.code index).instruction) location

theorem compiled_step (routine : Routine registers) (location : Fin routine.states)
    (values : Store registers) :
    step routine.compile ⟨machineLabel (some location), values⟩ =
      .inr ⟨machineLabel ((routine.code location).eval values).1,
        ((routine.code location).eval values).2⟩ := by
  simp only [step, machineLabel, Fin.val_castSucc, compiled_lookup]
  cases instruction : routine.code location with
  | jump next => rfl
  | increment register next => rfl
  | decrement register zero positive =>
    simp only [Op.instruction, Op.eval]
    split <;> rfl

theorem compiled_return (routine : Routine registers) (values : Store registers) :
    step routine.compile ⟨machineLabel (none : Option (Fin routine.states)), values⟩ =
      .inl (values 0) := by
  have lookup : routine.compile.code[(Fin.last routine.states).val]?.getD .halt = .halt := by
    change (List.ofFn (Fin.lastCases .halt
      (fun location => (routine.code location).instruction)))[routine.states]?.getD .halt = _
    rw [List.getElem?_ofFn, dite_eq_left (Nat.lt_succ_self _)]
    exact Fin.lastCases_last (motive := fun _ => Instruction registers (routine.states + 1))
      (last := .halt) (cast := fun location => (routine.code location).instruction)
  simp only [step, machineLabel, lookup]
  rfl

theorem executes_not_self_loop {program : Program}
    {state : State program.registers program.states} {output : Nat}
    (execution : Executes program state output) : step program state ≠ .inr state := by
  induction execution with
  | done stopped =>
    intro loop
    cases stopped.symm.trans loop
  | next moved rest ih =>
    intro loop
    have same := Sum.inr.inj (moved.symm.trans loop)
    subst same
    exact ih loop

def acceptZero (flag : Fin (registers + 1)) : Routine registers where
  states := 2
  entry := some 0
  code := fun location =>
    if location = 0 then .decrement flag none (some 1) else .jump (some 1)

theorem append_prefix_trace {first last : Routine registers}
    {values finalValues : Store registers} (execution : Runs first values finalValues) :
    Trace (append first last) (append first last).entry values
      (rightLabel first.states last.entry) finalValues := by
  exact trace_map (target := append first last) (leftLabel last.entry)
    (fun location => ⟨location.castAdd last.states, rfl,
      Fin.addCases_left (motive := fun _ => Op registers (Option (Fin (first.states + last.states))))
        (left := fun index => (first.code index).map (leftLabel last.entry))
        (right := fun index => (last.code index).map (rightLabel first.states)) location⟩) execution

def checkLabel (before : Routine registers) : Fin (before.states + 2) :=
  Fin.natAdd before.states 0

def trapLabel (before : Routine registers) : Fin (before.states + 2) :=
  Fin.natAdd before.states 1

theorem guard_check (before : Routine registers) (flag : Fin (registers + 1)) (values : Store registers) :
    step (append before (acceptZero flag)).compile ⟨machineLabel (some (checkLabel before)), values⟩ =
      if values flag = 0 then
        .inr ⟨machineLabel none, values⟩
      else .inr ⟨machineLabel (some (trapLabel before)), write values flag (values flag - 1)⟩ := by
  erw [compiled_step]
  simp only [checkLabel, append, Fin.addCases_right, acceptZero, ↓reduceIte, Op.map, Op.eval,
    rightLabel, Option.map_none, Option.map_some]
  split <;> rfl

theorem guard_trap (before : Routine registers) (flag : Fin (registers + 1)) (values : Store registers) :
    step (append before (acceptZero flag)).compile ⟨machineLabel (some (trapLabel before)), values⟩ =
      .inr ⟨machineLabel (some (trapLabel before)), values⟩ := by
  erw [compiled_step]
  simp [trapLabel, append, acceptZero, Op.map, Op.eval, rightLabel]

theorem guarded_prefix_halts_iff {before : Routine registers}
    (flag : Fin (registers + 1)) {values finalValues : Store registers}
    (execution : Runs before values finalValues) :
    (∃ output, Executes (append before (acceptZero flag)).compile
      ⟨machineLabel (append before (acceptZero flag)).entry, values⟩ output) ↔
      finalValues flag = 0 := by
  have reaches := trace_compiled (append_prefix_trace (last := acceptZero flag) execution)
  have atCheck : machineLabel (rightLabel before.states (acceptZero flag).entry) =
      machineLabel (some (checkLabel before)) := rfl
  erw [atCheck] at reaches
  constructor
  · rintro ⟨output, full⟩
    have atCheckExecution := (reaches_execution_iff reaches output).mp full
    by_cases zero : finalValues flag = 0
    · exact zero
    · have moved := guard_check before flag finalValues
      rw [ite_eq_right zero] at moved
      have atTrapExecution := (reaches_execution_iff (.next moved .refl) output).mp atCheckExecution
      exact False.elim (executes_not_self_loop atTrapExecution (guard_trap before flag _))
  · intro zero
    have moved := guard_check before flag finalValues
    rw [ite_eq_left zero] at moved
    refine ⟨finalValues 0, (reaches_execution_iff reaches _).mpr ?_⟩
    exact .next moved (.done (compiled_return _ _))

theorem routine_runs_compiled {routine : Routine registers}
    {values finalValues : Store registers} (execution : Routine.Runs routine values finalValues) :
    Executes routine.compile ⟨machineLabel routine.entry, values⟩ (finalValues 0) := by
  exact (reaches_execution_iff (trace_compiled execution) (finalValues 0)).mpr
    (.done (compiled_return routine finalValues))

theorem routine_program_runs {routine : Routine registers} (input : Nat)
    {finalValues : Store registers}
    (execution : Routine.Runs routine (initial routine.compile input).values finalValues) :
    Yulang.CanonicalRegisterMachine.Runs routine.compile input (finalValues 0) := by
  exact (reaches_execution_iff (trace_compiled execution) (finalValues 0)).mpr
    (.done (compiled_return routine finalValues))

end Yulang.CanonicalRegisterGuard
