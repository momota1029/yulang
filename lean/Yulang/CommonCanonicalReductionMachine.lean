import Yulang.CommonCanonicalConstraintPrograms
import Yulang.CommonCanonicalProgramReader
import Yulang.CommonCanonicalWordReverse

/-! A concrete seventeen-counter machine layout for serializing the reduction. -/

namespace Yulang.CommonCanonicalReductionMachine

open CanonicalRegisterMachine
open CanonicalRegisterMachine.Routine
open CommonCanonicalSerialization
open CommonCanonicalEmitters
open CommonCanonicalWordPrograms
open CommonCanonicalTemplatePrograms
open CommonCanonicalGridPrograms
open CommonCanonicalConstraintPrograms
open CommonCanonicalProgramReader

abbrev Register := Fin 17
abbrev Values := Store 16

def roster (field : Fin 10) : Register :=
  ⟨if field.val = 0 then 0 else field.val + 5, by split <;> omega⟩

def work (index : Fin 4) : Register := ⟨index.val + 2, by omega⟩

def context : GridContext 16 10 where
  base := {
    inputs := roster
    output := 1
    work := work
    distinct := by intro first last same; apply Fin.ext; have := congrArg Fin.val same; simp only [work] at this; omega
    outputOutside := by intro index; apply Fin.ne_of_val_ne; change 1 ≠ index.val + 2; omega
    inputsOutside := by
      intro field index
      apply Fin.ne_of_val_ne
      simp only [roster, work]
      split <;> omega
    inputsOutput := by
      intro field
      apply Fin.ne_of_val_ne
      simp only [roster]
      split <;> omega }
  coordinate := 15
  fuel := 16
  coordinateFuel := by decide
  coordinateOutput := by decide
  fuelOutput := by decide
  coordinateWork := by intro index; apply Fin.ne_of_val_ne; change 15 ≠ index.val + 2; omega
  fuelWork := by intro index; apply Fin.ne_of_val_ne; change 16 ≠ index.val + 2; omega
  inputsCoordinate := by intro field; apply Fin.ne_of_val_ne; change (if field.val = 0 then 0 else field.val + 5) ≠ 15; split <;> omega
  inputsFuel := by intro field; apply Fin.ne_of_val_ne; change (if field.val = 0 then 0 else field.val + 5) ≠ 16; split <;> omega

def readerBank : WordBank 16 := fourBank 0 2 3 4

def operandRegisters (index : Fin 3) : Register := ⟨index.val + 10, by omega⟩

def environment (values : Values) : Environment 10 := fun field => values (roster field)

def StableField (field : Fin 10) : Prop := field.val ≠ 0 ∧ (field.val < 5 ∨ 7 < field.val)

def prepared {registers states : Nat} (values : Values) (source : Instruction registers states) (rest : Word) : Values :=
  wordStore readerBank (updateAll values (operandUpdates operandRegisters source)) (wordCode rest) 0 0 62

/-- Parsing touches only the cursor, reader scratch, and the used operands.
All source header fields, the saved original input, PC and scan fuel survive. -/
theorem prepared_exact {registers states : Nat} (values : Values)
    (source : Instruction registers states) (rest : Word) :
    prepared values source rest 1 = values 1 ∧
    prepared values source rest 0 = wordCode rest ∧
    operandValues (environment (prepared values source rest)) source ∧
    ∀ field, StableField field → environment (prepared values source rest) field = environment values field := by
  have outputEq : prepared values source rest 1 = values 1 := by
    cases source <;> rfl
  have cursorEq : prepared values source rest 0 = wordCode rest := by
    cases source <;> rfl
  refine ⟨outputEq, cursorEq, ?_, ?_⟩
  · cases source with
    | halt => exact True.intro
    | increment _ _ => exact ⟨rfl, rfl⟩
    | decrement _ _ _ => exact ⟨rfl, rfl, rfl⟩
    | goto _ => rfl
  · intro field stable
    have alternatives : field = 1 ∨ field = 2 ∨ field = 3 ∨ field = 4 ∨ field = 8 ∨ field = 9 := by
      obtain ⟨nonzero, range⟩ := stable
      omega
    rcases alternatives with rfl | rfl | rfl | rfl | rfl | rfl <;> cases source <;> rfl

def handlers (mode : Mode) : InstructionHandlers 16 where
  halt := (instructionScript mode .halt).compile context
  increment := (instructionScript mode .increment).compile context
  decrement := (instructionScript mode .decrement).compile context
  jump := (instructionScript mode .jump).compile context

def readBlock (mode : Mode) : Routine 16 := readNext readerBank operandRegisters (handlers mode)

/-- One concrete reader/handler call consumes a source instruction (or
keeps nil for default halt) and emits its exact original row constraints. -/
theorem readBlock_runs {registers states : Nat} (pc : Fin states)
    (code : List (Instruction registers states)) (mode : Mode) (values : Values) (prior : Word)
    (cursor : values 0 = wordCode (list instruction code)) (encoded : values 1 = wordCode prior)
    (registersEq : environment values registersField = registers)
    (statesEq : environment values statesField = states) (pcEq : environment values pcField = pc.val) :
    ∃ finalValues, Runs (readBlock mode) values finalValues ∧
      finalValues 1 = wordCode ((stream mode (CommonCanonicalCounterConstraints.instructionTests pc
        (code.head?.getD .halt))).reverse ++ prior) ∧
      finalValues 0 = wordCode (list instruction code.tail) ∧
      ∀ field, StableField field → environment finalValues field = environment values field := by
  let source := code.head?.getD (.halt : Instruction registers states)
  let decoded := prepared values source (list instruction code.tail)
  obtain ⟨outputSame, cursorSame, operands, stable⟩ := prepared_exact values source (list instruction code.tail)
  have decodedInput : decoded 1 = wordCode prior := outputSame.trans encoded
  have decodedRegisters : environment decoded registersField = registers :=
    (stable registersField (by unfold StableField; decide)).trans registersEq
  have decodedStates : environment decoded statesField = states :=
    (stable statesField (by unfold StableField; decide)).trans statesEq
  have decodedPc : environment decoded pcField = pc.val := (stable pcField (by unfold StableField; decide)).trans pcEq
  obtain ⟨finalValues, handlerRun, result, frame⟩ := script_emits context (instructionScript mode (kind source))
    decoded prior decodedInput
  change finalValues 1 = wordCode (((instructionScript mode (kind source)).tokens (environment decoded)).reverse ++ prior) at result
  rw [instruction_script_exact pc source mode (environment decoded) decodedRegisters decodedStates decodedPc operands] at result
  have readerDistinct : Function.Injective readerBank :=
    fourBank_injective 0 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have outside (field : Fin 3) (index : Fin 4) : operandRegisters field ≠ readerBank index := by
    have bound : (readerBank index).val ≤ 4 := by
      have alternatives : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
      rcases alternatives with rfl | rfl | rfl | rfl <;> decide
    apply Fin.ne_of_val_ne
    change field.val + 10 ≠ (readerBank index).val
    omega
  have selectedEq : (handlers mode).select source = (instructionScript mode (kind source)).compile context := by
    cases source <;> rfl
  have selected : Runs ((handlers mode).select source) decoded finalValues := by
    rw [selectedEq]
    exact handlerRun
  refine ⟨finalValues, readNext_runs readerBank readerDistinct operandRegisters outside (handlers mode)
    code values finalValues cursor selected, result, ?_, ?_⟩
  · exact (frame 0).trans cursorSame
  · intro field kept
    exact (frame field).trans (stable field kept)

def block (mode : Mode) : Routine 16 := append ((partitionScript mode).compile context) (readBlock mode)

theorem block_runs {registers states : Nat} (pc : Fin states)
    (code : List (Instruction registers states)) (mode : Mode) (values : Values) (prior : Word)
    (cursor : values 0 = wordCode (list instruction code)) (encoded : values 1 = wordCode prior)
    (registersEq : environment values registersField = registers)
    (statesEq : environment values statesField = states) (pcEq : environment values pcField = pc.val) :
    ∃ finalValues, Runs (block mode) values finalValues ∧
      finalValues 1 = wordCode ((stream mode (CommonCanonicalCounterConstraints.partitionTests registers pc ++
        CommonCanonicalCounterConstraints.instructionTests pc (code.head?.getD .halt))).reverse ++ prior) ∧
      finalValues 0 = wordCode (list instruction code.tail) ∧
      ∀ field, StableField field → environment finalValues field = environment values field := by
  obtain ⟨middle, partitionRun, partitionWord, partitionFrame⟩ :=
    script_emits context (partitionScript mode) values prior encoded
  change middle 1 = wordCode (((partitionScript mode).tokens (environment values)).reverse ++ prior) at partitionWord
  rw [partition_script_exact registers pc mode (environment values) registersEq statesEq pcEq] at partitionWord
  obtain ⟨finalValues, instructionRun, finalWord, finalCursor, instructionFrame⟩ :=
    readBlock_runs pc code mode middle _ ((partitionFrame 0).trans cursor) partitionWord
      ((partitionFrame registersField).trans registersEq) ((partitionFrame statesField).trans statesEq)
      ((partitionFrame pcField).trans pcEq)
  have combined : stream mode (CommonCanonicalCounterConstraints.partitionTests registers pc ++
      CommonCanonicalCounterConstraints.instructionTests pc (code.head?.getD .halt)) =
      stream mode (CommonCanonicalCounterConstraints.partitionTests registers pc) ++
      stream mode (CommonCanonicalCounterConstraints.instructionTests pc (code.head?.getD .halt)) := by
    cases mode <;> simp only [stream, fixedStream, valueStream, List.flatMap_append]
  refine ⟨finalValues, append_runs partitionRun instructionRun, ?_, finalCursor, ?_⟩
  · simpa only [combined, List.reverse_append, List.append_assoc] using finalWord
  · intro field kept
    exact (instructionFrame field kept).trans (partitionFrame field)

end Yulang.CommonCanonicalReductionMachine
