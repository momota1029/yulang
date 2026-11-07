import Yulang.CanonicalRegisterRoutines

/-! Calls to arbitrary finite counter programs, with explicit register banks. -/

namespace Yulang.CanonicalRegisterMachine.Routine

def call {registers : Nat} (source : Program)
    (registerMap : Fin (source.registers + 1) → Fin (registers + 1)) : Routine registers where
  states := source.states
  entry := some source.entry
  code := fun pc => match source.code[pc.val]?.getD .halt with
    | .halt => .jump none
    | .increment register next => .increment (registerMap register) (some next)
    | .decrement register zero positive => .decrement (registerMap register) (some zero) (some positive)
    | .goto next => .jump (some next)

/-- Every terminating execution of an arbitrary callee is realized by its
finite call routine. Missing instructions return as in the original model.
All caller registers outside the injected bank are preserved. -/
theorem call_trace {source : Program} {registers : Nat}
    (registerMap : Fin (source.registers + 1) → Fin (registers + 1))
    (registerMap_injective : Function.Injective registerMap)
    {state : State source.registers source.states} {output : Nat}
    (execution : Executes source state output) (values : Store registers)
    (agrees : ∀ register, values (registerMap register) = state.values register) :
    ∃ finalValues,
      Trace (call source registerMap) (some state.pc) values none finalValues ∧
      finalValues (registerMap 0) = output ∧
      ∀ register, (∀ original, register ≠ registerMap original) → finalValues register = values register := by
  have update_agrees (old : Store source.registers) (current : Store registers)
      (equal : ∀ register, current (registerMap register) = old register)
      (changed : Fin (source.registers + 1)) (value : Nat) :
      ∀ register, write current (registerMap changed) value (registerMap register) =
        write old changed value register := by
    intro register
    simp only [write, registerMap_injective.eq_iff, equal]
  have update_frame (current : Store registers) (changed : Fin (source.registers + 1)) (value : Nat)
      (register : Fin (registers + 1)) (outside : ∀ original, register ≠ registerMap original) :
      write current (registerMap changed) value register = current register := by
    simp only [write, outside changed, ↓reduceIte]
  induction execution generalizing values with
  | @done state output stopped =>
      cases instruction : source.code[state.pc.val]?.getD .halt with
      | halt =>
          have result : state.values 0 = output := by
            simpa only [step, instruction, Sum.inl.injEq] using stopped
          refine ⟨values, .next ?_ .refl, (agrees 0).trans result, ?_⟩
          · simp only [call, instruction, Op.eval]
          · intro register _
            rfl
      | increment register next => simp [step, instruction] at stopped
      | decrement register zero positive =>
          simp only [step, instruction] at stopped
          split at stopped <;> cases stopped
      | goto next => simp [step, instruction] at stopped
  | @next state following output moved _ ih =>
      cases instruction : source.code[state.pc.val]?.getD .halt with
      | halt => simp [step, instruction] at moved
      | increment register next =>
          have same : following = ⟨next, write state.values register (state.values register + 1)⟩ := by
            simpa only [step, instruction, Sum.inr.injEq] using moved.symm
          subst following
          obtain ⟨finalValues, trace, result, frame⟩ :=
            ih (write values (registerMap register) (state.values register + 1))
              (update_agrees _ _ agrees _ _)
          refine ⟨finalValues, .next ?_ trace, result, ?_⟩
          · simp only [call, instruction, Op.eval, agrees]
          · intro outside absent
            exact (frame outside absent).trans (update_frame _ _ _ outside absent)
      | decrement register zero positive =>
          by_cases empty : state.values register = 0
          · have same : following = ⟨zero, state.values⟩ := by
              simpa only [step, instruction, empty, ↓reduceIte, Sum.inr.injEq] using moved.symm
            subst following
            obtain ⟨finalValues, trace, result, frame⟩ := ih values agrees
            refine ⟨finalValues, .next ?_ trace, result, frame⟩
            simp only [call, instruction, Op.eval, agrees, empty, ↓reduceIte]
          · have same : following = ⟨positive, write state.values register (state.values register - 1)⟩ := by
              simpa only [step, instruction, empty, ↓reduceIte, Sum.inr.injEq] using moved.symm
            subst following
            obtain ⟨finalValues, trace, result, frame⟩ :=
              ih (write values (registerMap register) (state.values register - 1))
                (update_agrees _ _ agrees _ _)
            refine ⟨finalValues, .next ?_ trace, result, ?_⟩
            · simp only [call, instruction, Op.eval, agrees, empty, ↓reduceIte]
            · intro outside absent
              exact (frame outside absent).trans (update_frame _ _ _ outside absent)
      | goto next =>
          have same : following = ⟨next, state.values⟩ := by
            simpa only [step, instruction, Sum.inr.injEq] using moved.symm
          subst following
          obtain ⟨finalValues, trace, result, frame⟩ := ih values agrees
          refine ⟨finalValues, .next ?_ trace, result, frame⟩
          simp only [call, instruction, Op.eval]

end Yulang.CanonicalRegisterMachine.Routine
