import Yulang.CanonicalRegisterMachine

/-!
# Finite execution prefixes for counter-program composition

Preprocessing and a terminating subroutine can be verified by their finite
prefixes. Determinism of `step` then lets us cancel those prefixes from an
arbitrary complete execution, including one allegedly ending after a trap.
-/

namespace Yulang.CanonicalRegisterMachine

inductive Reaches (program : Program) :
    State program.registers program.states → State program.registers program.states → Prop where
  | refl : Reaches program state state
  | next : step program state = .inr following →
      Reaches program following final → Reaches program state final

/-- A verified nonterminal prefix preserves exactly the possible outputs,
including when the suffix never returns. -/
theorem reaches_execution_iff {program : Program}
    {first last : State program.registers program.states}
    (trace : Reaches program first last) (output : Nat) :
    Executes program first output ↔ Executes program last output := by
  induction trace with
  | refl => exact Iff.rfl
  | next moved _ ih =>
      constructor
      · intro execution
        cases execution with
        | done stopped => simp [moved] at stopped
        | next followed execution =>
            have same := Sum.inr.inj (moved.symm.trans followed)
            subst same
            exact ih.mp execution
      · intro execution
        exact .next moved (ih.mpr execution)

/-- Relocate every instruction of a finite program and turn its return into
a jump to the caller's continuation. -/
def Instruction.relocate {registers states targetRegisters targetStates : Nat}
    (registerMap : Fin (registers + 1) → Fin (targetRegisters + 1))
    (labelMap : Fin states → Fin targetStates) (resume : Fin targetStates) :
    Instruction registers states → Instruction targetRegisters targetStates
  | .halt => .goto resume
  | .increment register next => .increment (registerMap register) (labelMap next)
  | .decrement register zero positive =>
      .decrement (registerMap register) (labelMap zero) (labelMap positive)
  | .goto next => .goto (labelMap next)

/-- An actual finite execution of a callee becomes a nonterminal execution
prefix in a caller containing its relocated instruction table. The caller's
other registers are preserved. No assumption about the continuation is made. -/
theorem subroutine_reaches {source target : Program}
    (registerMap : Fin (source.registers + 1) → Fin (target.registers + 1))
    (registerMap_injective : Function.Injective registerMap)
    (labelMap : Fin source.states → Fin target.states) (resume : Fin target.states)
    (table : ∀ pc,
      target.code[(labelMap pc).val]?.getD .halt =
        (source.code[pc.val]?.getD .halt).relocate registerMap labelMap resume)
    {state : State source.registers source.states} {output : Nat}
    (execution : Executes source state output)
    (values : Fin (target.registers + 1) → Nat)
    (agrees : ∀ register, values (registerMap register) = state.values register) :
    ∃ finalValues,
      Reaches target ⟨labelMap state.pc, values⟩ ⟨resume, finalValues⟩ ∧
      finalValues (registerMap 0) = output ∧
      ∀ register, (∀ original, register ≠ registerMap original) →
        finalValues register = values register := by
  have update_agrees (old : Fin (source.registers + 1) → Nat)
      (current : Fin (target.registers + 1) → Nat)
      (equal : ∀ register, current (registerMap register) = old register)
      (changed : Fin (source.registers + 1)) (value : Nat) :
      ∀ register, write current (registerMap changed) value (registerMap register) =
        write old changed value register := by
    intro register
    simp only [write, registerMap_injective.eq_iff, equal]
  have update_frame (current : Fin (target.registers + 1) → Nat)
      (changed : Fin (source.registers + 1)) (value : Nat)
      (register : Fin (target.registers + 1))
      (outside : ∀ original, register ≠ registerMap original) :
      write current (registerMap changed) value register = current register := by
    simp only [write, outside changed, ↓reduceIte]
  induction execution generalizing values with
  | @done state output stopped =>
      cases instruction : source.code[state.pc.val]?.getD .halt with
      | halt =>
          have result : state.values 0 = output := by
            simpa only [step, instruction, Sum.inl.injEq] using stopped
          refine ⟨values, .next ?_ .refl, (agrees 0).trans result, ?_⟩
          · simp only [step, table, instruction, Instruction.relocate]
          · intro register _
            rfl
      | increment register next => simp [step, instruction] at stopped
      | decrement register zero positive =>
          simp only [step, instruction] at stopped
          split at stopped <;> cases stopped
      | goto next => simp [step, instruction] at stopped
  | @next state following output moved rest ih =>
      cases instruction : source.code[state.pc.val]?.getD .halt with
      | halt => simp [step, instruction] at moved
      | increment register next =>
          have same : following =
              ⟨next, write state.values register (state.values register + 1)⟩ := by
            simpa only [step, instruction, Sum.inr.injEq] using moved.symm
          subst following
          obtain ⟨finalValues, trace, result, frame⟩ :=
            ih (write values (registerMap register) (state.values register + 1))
              (update_agrees _ _ agrees _ _)
          refine ⟨finalValues, .next ?_ trace, result, ?_⟩
          · simp only [step, table, instruction, Instruction.relocate, agrees]
          · intro outside absent
            exact (frame outside absent).trans (update_frame _ _ _ outside absent)
      | decrement register zero positive =>
          by_cases empty : state.values register = 0
          · have same : following = ⟨zero, state.values⟩ := by
              simpa only [step, instruction, empty, ↓reduceIte, Sum.inr.injEq] using moved.symm
            subst following
            obtain ⟨finalValues, trace, result, frame⟩ := ih values agrees
            refine ⟨finalValues, .next ?_ trace, result, frame⟩
            simp only [step, table, instruction, Instruction.relocate, agrees, empty, ↓reduceIte]
          · have same : following =
                ⟨positive, write state.values register (state.values register - 1)⟩ := by
              simpa only [step, instruction, empty, ↓reduceIte, Sum.inr.injEq] using moved.symm
            subst following
            obtain ⟨finalValues, trace, result, frame⟩ :=
              ih (write values (registerMap register) (state.values register - 1))
                (update_agrees _ _ agrees _ _)
            refine ⟨finalValues, .next ?_ trace, result, ?_⟩
            · simp only [step, table, instruction, Instruction.relocate, agrees, empty, ↓reduceIte]
            · intro outside absent
              exact (frame outside absent).trans (update_frame _ _ _ outside absent)
      | goto next =>
          have same : following = ⟨next, state.values⟩ := by
            simpa only [step, instruction, Sum.inr.injEq] using moved.symm
          subst following
          obtain ⟨finalValues, trace, result, frame⟩ := ih values agrees
          refine ⟨finalValues, .next ?_ trace, result, frame⟩
          simp only [step, table, instruction, Instruction.relocate]

end Yulang.CanonicalRegisterMachine
