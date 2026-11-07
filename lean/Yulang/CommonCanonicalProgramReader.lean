import Yulang.CommonCanonicalWordPrograms

/-! Concrete finite-counter readers for the program compiler's input fields. -/

namespace Yulang.CommonCanonicalProgramReader

open CanonicalRegisterMachine
open CanonicalRegisterMachine.Routine
open CommonCanonicalSerialization
open CommonCanonicalWordPrograms

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

end Yulang.CommonCanonicalProgramReader
