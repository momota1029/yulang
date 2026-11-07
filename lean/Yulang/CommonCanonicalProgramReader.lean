import Yulang.CommonCanonicalWordPrograms

/-! Concrete finite-counter readers for the program compiler's input fields. -/

namespace Yulang.CommonCanonicalProgramReader

open CanonicalRegisterMachine
open CanonicalRegisterMachine.Routine
open CommonCanonicalSerialization
open CommonCanonicalWordPrograms

def readPair {registers : Nat} (bank : WordBank registers)
    (firstOutput lastOutput : Fin (registers + 1)) : Routine registers :=
  append (readNatural bank firstOutput) (readNatural bank lastOutput)

theorem readPair_runs {registers : Nat} (bank : WordBank registers)
    (distinct : Function.Injective bank) (firstOutput lastOutput : Fin (registers + 1))
    (firstOutside : ∀ index, firstOutput ≠ bank index) (lastOutside : ∀ index, lastOutput ≠ bank index)
    (first last : Nat) (rest : Word) (values : Store registers)
    (input : values (bank 0) = wordCode (natural first ++ natural last ++ rest)) :
    Runs (readPair bank firstOutput lastOutput) values
      (wordStore bank (write (write values firstOutput first) lastOutput last) (wordCode rest) 0 0 62) := by
  let firstFrame := write values firstOutput first
  let middle := wordStore bank firstFrame (wordCode (natural last ++ rest)) 0 0 62
  have firstRun := readNatural_runs bank distinct firstOutput firstOutside first (natural last ++ rest) values
    (by simpa only [List.append_assoc] using input)
  have middleInput : middle (bank 0) = wordCode (natural last ++ rest) := by
    simp [middle, wordStore, write, distinct.eq_iff]
  have lastRun := readNatural_runs bank distinct lastOutput lastOutside last rest middle middleInput
  change Runs (readNatural bank lastOutput) middle
    (wordStore bank (write (wordStore bank firstFrame (wordCode (natural last ++ rest)) 0 0 62)
      lastOutput last) (wordCode rest) 0 0 62) at lastRun
  rw [wordStore_write_frame] at lastRun
  exact append_runs firstRun lastRun

def readTriple {registers : Nat} (bank : WordBank registers)
    (outputs : Fin 3 → Fin (registers + 1)) : Routine registers :=
  append (readNatural bank (outputs 0))
    (append (readNatural bank (outputs 1)) (readNatural bank (outputs 2)))

theorem readTriple_runs {registers : Nat} (bank : WordBank registers)
    (distinct : Function.Injective bank) (outputs : Fin 3 → Fin (registers + 1))
    (outside : ∀ field index, outputs field ≠ bank index)
    (first second third : Nat) (rest : Word) (values : Store registers)
    (input : values (bank 0) = wordCode (natural first ++ natural second ++ natural third ++ rest)) :
    Runs (readTriple bank outputs) values
      (wordStore bank (write (write (write values (outputs 0) first) (outputs 1) second) (outputs 2) third)
        (wordCode rest) 0 0 62) := by
  let firstFrame := write values (outputs 0) first
  let firstStore := wordStore bank firstFrame (wordCode (natural second ++ natural third ++ rest)) 0 0 62
  have firstRun := readNatural_runs bank distinct (outputs 0) (outside 0) first
    (natural second ++ natural third ++ rest) values (by simpa only [List.append_assoc] using input)
  have secondInput : firstStore (bank 0) = wordCode (natural second ++ natural third ++ rest) := by
    simp [firstStore, wordStore, write, distinct.eq_iff]
  have secondRun := readNatural_runs bank distinct (outputs 1) (outside 1) second
    (natural third ++ rest) firstStore (by simpa only [List.append_assoc] using secondInput)
  change Runs (readNatural bank (outputs 1)) firstStore
    (wordStore bank (write (wordStore bank firstFrame
      (wordCode (natural second ++ natural third ++ rest)) 0 0 62) (outputs 1) second)
      (wordCode (natural third ++ rest)) 0 0 62) at secondRun
  rw [wordStore_write_frame] at secondRun
  let secondFrame := write firstFrame (outputs 1) second
  let secondStore := wordStore bank secondFrame (wordCode (natural third ++ rest)) 0 0 62
  have thirdInput : secondStore (bank 0) = wordCode (natural third ++ rest) := by
    simp [secondStore, wordStore, write, distinct.eq_iff]
  have thirdRun := readNatural_runs bank distinct (outputs 2) (outside 2) third rest secondStore thirdInput
  change Runs (readNatural bank (outputs 2)) secondStore
    (wordStore bank (write (wordStore bank secondFrame (wordCode (natural third ++ rest)) 0 0 62)
      (outputs 2) third) (wordCode rest) 0 0 62) at thirdRun
  rw [wordStore_write_frame] at thirdRun
  exact append_runs firstRun (append_runs secondRun thirdRun)

def readHeader {registers : Nat} (bank : WordBank registers)
    (outputs : Fin 3 → Fin (registers + 1)) : Routine registers :=
  append (wordPop bank) (readTriple bank outputs)

/-- Decode the actual finite-program serializer's register count, declared
state count, and entry index, leaving its instruction list as the exact suffix. -/
theorem readHeader_runs {registers : Nat} (bank : WordBank registers)
    (distinct : Function.Injective bank) (outputs : Fin 3 → Fin (registers + 1))
    (outside : ∀ field index, outputs field ≠ bank index)
    (source : CanonicalRegisterMachine.Program) (values : Store registers)
    (input : values (bank 0) = programCode source) :
    Runs (readHeader bank outputs) values
      (wordStore bank (updateAll values [(outputs 0, source.registers),
        (outputs 1, source.states), (outputs 2, source.entry.val)])
        (wordCode (list instruction source.code)) 0 0 62) := by
  let tail := natural source.registers ++ natural source.states ++ natural source.entry.val ++ list instruction source.code
  have encoded : values (bank 0) = wordCode (.program :: tail) := input
  have popRun := wordPop_token bank distinct values .program tail encoded
  simp only [Token.digit, Nat.reduceSub] at popRun
  let popped := wordStore bank values (wordCode tail) 0 20 43
  have fieldsInput : popped (bank 0) = wordCode tail := by simp [popped, wordStore, write, distinct.eq_iff]
  have fieldsRun := readTriple_runs bank distinct outputs outside source.registers source.states source.entry.val
    (list instruction source.code) popped fieldsInput
  change Runs (readTriple bank outputs) popped
    (wordStore bank (updateAll (wordStore bank values (wordCode tail) 0 20 43)
      [(outputs 0, source.registers), (outputs 1, source.states), (outputs 2, source.entry.val)])
      (wordCode (list instruction source.code)) 0 0 62) at fieldsRun
  rw [wordStore_update_frame] at fieldsRun
  exact append_runs popRun fieldsRun

theorem pop_dispatch_runs {registers : Nat} (bank : WordBank registers)
    (distinct : Function.Injective bank) (fallback : Routine registers)
    (choices : List (Routine registers)) (token : Token) (tail : Word) (chosen : Routine registers)
    (found : choices[token.digit]? = some chosen) (values finalValues : Store registers)
    (input : values (bank 0) = wordCode (token :: tail))
    (execution : Runs chosen (wordStore bank values (wordCode tail) 0 0 (63 - token.digit)) finalValues) :
    Runs (append (wordPop bank) (dispatch (bank 2) fallback choices)) values finalValues := by
  let popped := wordStore bank values (wordCode tail) 0 token.digit (63 - token.digit)
  have popRun := wordPop_token bank distinct values token tail input
  have poppedDigit : popped (bank 2) = token.digit := by simp [popped, wordStore, write, distinct.eq_iff]
  have reset : write popped (bank 2) 0 = wordStore bank values (wordCode tail) 0 0 (63 - token.digit) := by
    simp only [popped, wordStore]
    rw [write_commute _ (bank 3) (bank 2) (by simp [distinct.eq_iff]), write_shadow]
  have choiceRun := dispatch_runs (bank 2) fallback choices token.digit chosen found popped finalValues poppedDigit
    (by rw [reset]; exact execution)
  exact append_runs popRun choiceRun

structure InstructionHandlers (registers : Nat) where
  halt : Routine registers
  increment : Routine registers
  decrement : Routine registers
  jump : Routine registers

def InstructionHandlers.select (handlers : InstructionHandlers registers) :
    Instruction sourceRegisters sourceStates → Routine registers
  | .halt => handlers.halt
  | .increment _ _ => handlers.increment
  | .decrement _ _ _ => handlers.decrement
  | .goto _ => handlers.jump

def operandUpdates (outputs : Fin 3 → Fin (registers + 1)) :
    Instruction sourceRegisters sourceStates → List (Fin (registers + 1) × Nat)
  | .halt => []
  | .increment register next => [(outputs 0, register.val), (outputs 1, next.val)]
  | .decrement register zero positive =>
      [(outputs 0, register.val), (outputs 1, zero.val), (outputs 2, positive.val)]
  | .goto next => [(outputs 0, next.val)]

def instructionChoices {registers : Nat} (bank : WordBank registers)
    (outputs : Fin 3 → Fin (registers + 1)) (handlers : InstructionHandlers registers) : List (Routine registers) :=
  List.replicate 21 skip ++
    [append (setConstant (bank 3) 62) handlers.halt,
      append (readPair bank (outputs 0) (outputs 1)) handlers.increment,
      append (readTriple bank outputs) handlers.decrement,
      append (readNatural bank (outputs 0)) handlers.jump]

def readInstruction {registers : Nat} (bank : WordBank registers)
    (outputs : Fin 3 → Fin (registers + 1)) (handlers : InstructionHandlers registers) : Routine registers :=
  append (wordPop bank) (dispatch (bank 2) skip (instructionChoices bank outputs handlers))

/-- Decode every actual instruction constructor and enter its corresponding
finite handler with the exact numeric operands and unconsumed suffix.
The callback premise is an ordinary execution of the selected handler. -/
theorem readInstruction_runs {registers sourceRegisters sourceStates : Nat}
    (bank : WordBank registers) (distinct : Function.Injective bank)
    (outputs : Fin 3 → Fin (registers + 1)) (outside : ∀ field index, outputs field ≠ bank index)
    (handlers : InstructionHandlers registers) (source : Instruction sourceRegisters sourceStates)
    (rest : Word) (values finalValues : Store registers)
    (input : values (bank 0) = wordCode (instruction source ++ rest))
    (execution : Runs (handlers.select source)
      (wordStore bank (updateAll values (operandUpdates outputs source)) (wordCode rest) 0 0 62) finalValues) :
    Runs (readInstruction bank outputs handlers) values finalValues := by
  have afterToken (token : Token) (tail : Word) (chosen : Routine registers)
      (found : (instructionChoices bank outputs handlers)[token.digit]? = some chosen)
      (encoded : values (bank 0) = wordCode (token :: tail))
      (runChosen : Runs chosen (wordStore bank values (wordCode tail) 0 0 (63 - token.digit)) finalValues) :
      Runs (readInstruction bank outputs handlers) values finalValues := by
    let popped := wordStore bank values (wordCode tail) 0 token.digit (63 - token.digit)
    have popRun := wordPop_token bank distinct values token tail encoded
    have poppedDigit : popped (bank 2) = token.digit := by simp [popped, wordStore, write, distinct.eq_iff]
    have reset : write popped (bank 2) 0 = wordStore bank values (wordCode tail) 0 0 (63 - token.digit) := by
      simp only [popped, wordStore]
      rw [write_commute _ (bank 3) (bank 2) (by simp [distinct.eq_iff]), write_shadow]
    have choiceRun := dispatch_runs (bank 2) skip (instructionChoices bank outputs handlers)
      token.digit chosen found popped finalValues poppedDigit (by rw [reset]; exact runChosen)
    exact append_runs popRun choiceRun
  cases source with
  | halt =>
      apply afterToken .halt rest (append (setConstant (bank 3) 62) handlers.halt) rfl
        (by simpa only [instruction, List.singleton_append] using input)
      have resetRun := setConstant_runs (bank 3) 62 (wordStore bank values (wordCode rest) 0 0 (63 - Token.halt.digit))
      simp only [wordStore, write_shadow] at resetRun
      exact append_runs resetRun execution
  | increment register next =>
      let tail := natural register.val ++ natural next.val ++ rest
      apply afterToken .increment tail (append (readPair bank (outputs 0) (outputs 1)) handlers.increment) rfl
        (by simpa only [instruction, List.cons_append] using input)
      let prepared := wordStore bank values (wordCode tail) 0 0 (63 - Token.increment.digit)
      have fieldsInput : prepared (bank 0) = wordCode tail := by simp [prepared, wordStore, write, distinct.eq_iff]
      have fieldsRun := readPair_runs bank distinct (outputs 0) (outputs 1) (outside 0) (outside 1)
        register.val next.val rest prepared fieldsInput
      change Runs (readPair bank (outputs 0) (outputs 1)) prepared
        (wordStore bank (updateAll (wordStore bank values (wordCode tail) 0 0 (63 - Token.increment.digit))
          [(outputs 0, register.val), (outputs 1, next.val)]) (wordCode rest) 0 0 62) at fieldsRun
      rw [wordStore_update_frame] at fieldsRun
      exact append_runs fieldsRun execution
  | decrement register zero positive =>
      let tail := natural register.val ++ natural zero.val ++ natural positive.val ++ rest
      apply afterToken .decrement tail (append (readTriple bank outputs) handlers.decrement) rfl
        (by simpa only [instruction, List.cons_append] using input)
      let prepared := wordStore bank values (wordCode tail) 0 0 (63 - Token.decrement.digit)
      have fieldsInput : prepared (bank 0) = wordCode tail := by simp [prepared, wordStore, write, distinct.eq_iff]
      have fieldsRun := readTriple_runs bank distinct outputs outside register.val zero.val positive.val rest prepared fieldsInput
      change Runs (readTriple bank outputs) prepared
        (wordStore bank (updateAll (wordStore bank values (wordCode tail) 0 0 (63 - Token.decrement.digit))
          [(outputs 0, register.val), (outputs 1, zero.val), (outputs 2, positive.val)]) (wordCode rest) 0 0 62) at fieldsRun
      rw [wordStore_update_frame] at fieldsRun
      exact append_runs fieldsRun execution
  | goto next =>
      let tail := natural next.val ++ rest
      apply afterToken .jump tail (append (readNatural bank (outputs 0)) handlers.jump) rfl
        (by simpa only [instruction, List.cons_append] using input)
      let prepared := wordStore bank values (wordCode tail) 0 0 (63 - Token.jump.digit)
      have fieldsInput : prepared (bank 0) = wordCode tail := by simp [prepared, wordStore, write, distinct.eq_iff]
      have fieldsRun := readNatural_runs bank distinct (outputs 0) (outside 0) next.val rest prepared fieldsInput
      change Runs (readNatural bank (outputs 0)) prepared
        (wordStore bank (write (wordStore bank values (wordCode tail) 0 0 (63 - Token.jump.digit))
          (outputs 0) next.val) (wordCode rest) 0 0 62) at fieldsRun
      rw [wordStore_write_frame] at fieldsRun
      exact append_runs fieldsRun execution

def missingInstruction {registers : Nat} (bank : WordBank registers)
    (haltHandler : Routine registers) : Routine registers :=
  append (setConstant (bank 0) Token.nil.digit) (append (setConstant (bank 3) 62) haltHandler)

def nextChoices {registers : Nat} (bank : WordBank registers)
    (outputs : Fin 3 → Fin (registers + 1)) (handlers : InstructionHandlers registers) : List (Routine registers) :=
  List.replicate 3 skip ++ [missingInstruction bank handlers.halt, readInstruction bank outputs handlers]

def readNext {registers : Nat} (bank : WordBank registers)
    (outputs : Fin 3 → Fin (registers + 1)) (handlers : InstructionHandlers registers) : Routine registers :=
  append (wordPop bank) (dispatch (bank 2) skip (nextChoices bank outputs handlers))

/-- A missing entry selects the default halt and restores the serialized nil
cursor. Consequently repeated reads of a short table keep selecting halt;
nonempty tables consume exactly one instruction and retain their exact tail. -/
theorem readNext_runs {registers sourceRegisters sourceStates : Nat}
    (bank : WordBank registers) (distinct : Function.Injective bank)
    (outputs : Fin 3 → Fin (registers + 1)) (outside : ∀ field index, outputs field ≠ bank index)
    (handlers : InstructionHandlers registers) (code : List (Instruction sourceRegisters sourceStates))
    (values finalValues : Store registers) (input : values (bank 0) = wordCode (list instruction code))
    (execution : Runs (handlers.select (code.head?.getD .halt))
      (wordStore bank (updateAll values (operandUpdates outputs (code.head?.getD .halt)))
        (wordCode (list instruction code.tail)) 0 0 62) finalValues) :
    Runs (readNext bank outputs handlers) values finalValues := by
  cases code with
  | nil =>
      apply pop_dispatch_runs bank distinct skip (nextChoices bank outputs handlers) .nil []
        (missingInstruction bank handlers.halt) rfl values finalValues input
      let emptyStore := wordStore bank values (wordCode []) 0 0 (63 - Token.nil.digit)
      let restored := write emptyStore (bank 0) Token.nil.digit
      have restoreRun := setConstant_runs (bank 0) Token.nil.digit emptyStore
      have clockRun := setConstant_runs (bank 3) 62 restored
      have same : write restored (bank 3) 62 = wordStore bank values 3 0 0 62 := by
        funext current
        by_cases at0 : current = bank 0
        <;> by_cases at1 : current = bank 1
        <;> by_cases at2 : current = bank 2
        <;> by_cases at3 : current = bank 3
        <;> simp_all [restored, emptyStore, wordStore, write, wordCode, Token.digit, distinct.eq_iff]
      rw [same] at clockRun
      exact append_runs restoreRun (append_runs clockRun execution)
  | cons source tail =>
      apply pop_dispatch_runs bank distinct skip (nextChoices bank outputs handlers) .cons
        (instruction source ++ list instruction tail) (readInstruction bank outputs handlers) rfl values finalValues input
      let prepared := wordStore bank values (wordCode (instruction source ++ list instruction tail)) 0 0 (63 - Token.cons.digit)
      have preparedInput : prepared (bank 0) = wordCode (instruction source ++ list instruction tail) := by
        simp [prepared, wordStore, write, distinct.eq_iff]
      have callback : Runs (handlers.select source)
          (wordStore bank (updateAll prepared (operandUpdates outputs source))
            (wordCode (list instruction tail)) 0 0 62) finalValues := by
        change Runs (handlers.select source)
          (wordStore bank (updateAll (wordStore bank values
            (wordCode (instruction source ++ list instruction tail)) 0 0 (63 - Token.cons.digit))
            (operandUpdates outputs source)) (wordCode (list instruction tail)) 0 0 62) finalValues
        rw [wordStore_update_frame]
        exact execution
      exact readInstruction_runs bank distinct outputs outside handlers source (list instruction tail)
        prepared finalValues preparedInput callback

end Yulang.CommonCanonicalProgramReader
