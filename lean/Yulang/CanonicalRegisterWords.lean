import Yulang.CanonicalRegisterMacros

/-! Fixed-base finite-word operations in the actual counter model. -/

namespace Yulang.CanonicalRegisterMachine.Routine

abbrev WordBank (registers : Nat) := Fin 4 → Fin (registers + 1)

def wordStore {registers : Nat} (bank : WordBank registers) (frame : Store registers)
    (input quotient remainder countdown : Nat) : Store registers :=
  write (write (write (write frame (bank 0) input) (bank 1) quotient)
    (bank 2) remainder) (bank 3) countdown

/-- Reinitializing the same four bank locations discards their old contents
even when an ordinary register write occurs between the two initializations. -/
theorem wordStore_write_frame {registers : Nat} (bank : WordBank registers)
    (frame : Store registers) (output : Fin (registers + 1)) (value : Nat)
    (oldWord oldQuotient oldRemainder oldCountdown newWord newQuotient newRemainder newCountdown : Nat) :
    wordStore bank (write (wordStore bank frame oldWord oldQuotient oldRemainder oldCountdown) output value)
        newWord newQuotient newRemainder newCountdown =
      wordStore bank (write frame output value) newWord newQuotient newRemainder newCountdown := by
  funext current
  by_cases at0 : current = bank 0
  <;> by_cases at1 : current = bank 1
  <;> by_cases at2 : current = bank 2
  <;> by_cases at3 : current = bank 3
  <;> by_cases atOutput : current = output
  <;> simp_all [wordStore, write]

def updateAll {registers : Nat} (values : Store registers)
    (updates : List (Fin (registers + 1) × Nat)) : Store registers :=
  updates.foldl (fun current update => write current update.1 update.2) values

theorem wordStore_update_frame {registers : Nat} (bank : WordBank registers)
    (frame : Store registers) (updates : List (Fin (registers + 1) × Nat))
    (oldWord oldQuotient oldRemainder oldCountdown newWord newQuotient newRemainder newCountdown : Nat) :
    wordStore bank (updateAll (wordStore bank frame oldWord oldQuotient oldRemainder oldCountdown) updates)
        newWord newQuotient newRemainder newCountdown =
      wordStore bank (updateAll frame updates) newWord newQuotient newRemainder newCountdown := by
  have pointwise (current : Fin (registers + 1)) (first last : Store registers)
      (equal : first current = last current) : updateAll first updates current = updateAll last updates current := by
    induction updates generalizing first last with
    | nil => exact equal
    | cons update updates ih =>
        apply ih
        simp only [write, equal]
  funext current
  by_cases at3 : current = bank 3
  · simp only [wordStore, write, at3, ↓reduceIte]
  · by_cases at2 : current = bank 2
    · simp only [wordStore, write, at2, ↓reduceIte]
    · by_cases at1 : current = bank 1
      · simp only [wordStore, write, at1, ↓reduceIte]
      · by_cases at0 : current = bank 0
        · simp only [wordStore, write, at0, ↓reduceIte]
        · simp only [wordStore, write, at3, at2, at1, at0, ↓reduceIte]
          apply pointwise
          simp only [write, at3, at2, at1, at0, ↓reduceIte]

def wordTick {registers : Nat} (bank : WordBank registers) : Routine registers :=
  branch (bank 3)
    (append (setConstant (bank 3) 63) (append (clear (bank 2)) (increment (bank 1))))
    (increment (bank 2))

/-- One consumed unit advances a base-64 remainder and carries into the
quotient exactly when the remainder reaches 64. -/
theorem wordTick_runs {registers : Nat} (bank : WordBank registers)
    (distinct : Function.Injective bank) (frame : Store registers)
    (input quotient remainder : Nat) (bounded : remainder < 64) :
    Runs (wordTick bank) (wordStore bank frame input quotient remainder (63 - remainder))
      (wordStore bank frame input (quotient + (remainder + 1) / 64)
        ((remainder + 1) % 64) (63 - (remainder + 1) % 64)) := by
  let start := wordStore bank frame input quotient remainder (63 - remainder)
  by_cases boundary : remainder = 63
  · subst remainder
    have empty : start (bank 3) = 0 := by simp [start, wordStore, write]
    apply branch_runs
    rw [ite_eq_left empty]
    have firstRun := setConstant_runs (bank 3) 63 start
    have secondRun := clear_runs (bank 2) (write start (bank 3) 63)
    have lastRun := atomic_runs (.increment (bank 1) ())
      (write (write start (bank 3) 63) (bank 2) 0)
    have combined := append_runs firstRun (append_runs secondRun lastRun)
    have same :
        (Op.eval (write (write start (bank 3) 63) (bank 2) 0) (.increment (bank 1) ())).2 =
        wordStore bank frame input (quotient + (63 + 1) / 64)
          ((63 + 1) % 64) (63 - (63 + 1) % 64) := by
      funext current
      by_cases at0 : current = bank 0
      <;> by_cases at1 : current = bank 1
      <;> by_cases at2 : current = bank 2
      <;> by_cases at3 : current = bank 3
      <;> simp_all [Op.eval, start, wordStore, write, distinct.eq_iff]
    exact same ▸ combined
  · have before : remainder < 63 := by omega
    have nonzero : start (bank 3) ≠ 0 := by
      simp only [start, wordStore, write, ↓reduceIte]
      omega
    apply branch_runs
    rw [ite_eq_right nonzero]
    have executed := atomic_runs (.increment (bank 2) ())
      (write start (bank 3) (start (bank 3) - 1))
    have division : (remainder + 1) / 64 = 0 := Nat.div_eq_of_lt (by omega)
    have modulus : (remainder + 1) % 64 = remainder + 1 := Nat.mod_eq_of_lt (by omega)
    have countdown : 63 - remainder - 1 = 63 - (remainder + 1) := by omega
    have same :
        (Op.eval (write start (bank 3) (start (bank 3) - 1)) (.increment (bank 2) ())).2 =
        wordStore bank frame input (quotient + (remainder + 1) / 64)
          ((remainder + 1) % 64) (63 - (remainder + 1) % 64) := by
      rw [division, modulus]
      funext current
      by_cases at0 : current = bank 0
      <;> by_cases at1 : current = bank 1
      <;> by_cases at2 : current = bank 2
      <;> by_cases at3 : current = bank 3
      <;> simp_all [Op.eval, start, wordStore, write, distinct.eq_iff]
    exact same ▸ executed

def wordDivisionLoop {registers : Nat} (bank : WordBank registers) : Routine registers :=
  loop (bank 0) (wordTick bank)

/-- The concrete division loop terminates on every natural input. The
remainder bound is maintained by the loop itself. -/
theorem wordDivisionLoop_runs {registers : Nat} (bank : WordBank registers)
    (distinct : Function.Injective bank) (frame : Store registers)
    (input quotient remainder : Nat) (bounded : remainder < 64) :
    Runs (wordDivisionLoop bank)
      (wordStore bank frame input quotient remainder (63 - remainder))
      (wordStore bank frame 0 (quotient + (remainder + input) / 64)
        ((remainder + input) % 64) (63 - (remainder + input) % 64)) := by
  apply loop_runs
  induction input generalizing quotient remainder with
  | zero =>
      rw [Nat.add_zero, Nat.div_eq_of_lt bounded, Nat.mod_eq_of_lt bounded, Nat.add_zero]
      apply LoopRuns.done
      simp [wordStore, write, distinct.eq_iff]
  | succ input ih =>
      let start := wordStore bank frame (input + 1) quotient remainder (63 - remainder)
      have positive : start (bank 0) ≠ 0 := by simp [start, wordStore, write, distinct.eq_iff]
      have decreased : write start (bank 0) (start (bank 0) - 1) =
          wordStore bank frame input quotient remainder (63 - remainder) := by
        funext current
        by_cases at0 : current = bank 0
        <;> by_cases at1 : current = bank 1
        <;> by_cases at2 : current = bank 2
        <;> by_cases at3 : current = bank 3
        <;> simp_all [start, wordStore, write, distinct.eq_iff]
      have body := wordTick_runs bank distinct frame input quotient remainder bounded
      rw [← decreased] at body
      have rest := ih (quotient + (remainder + 1) / 64) ((remainder + 1) % 64)
        (Nat.mod_lt _ (by decide))
      have quotientEq : quotient + (remainder + 1) / 64 +
          ((remainder + 1) % 64 + input) / 64 = quotient + (remainder + (input + 1)) / 64 := by
        omega
      have remainderEq : ((remainder + 1) % 64 + input) % 64 =
          (remainder + (input + 1)) % 64 := by omega
      rw [quotientEq, remainderEq] at rest
      exact .next positive body rest

def wordPop {registers : Nat} (bank : WordBank registers) : Routine registers :=
  append (clear (bank 1)) (append (clear (bank 2))
    (append (setConstant (bank 3) 63)
      (append (wordDivisionLoop bank) (drain (bank 1) [bank 0]))))

/-- Pop the least significant base-64 digit. Counter zero of the bank holds
the remaining word, counter two holds the digit; the two scratch counters
have the displayed exact values. Arbitrary prior scratch contents are allowed. -/
theorem wordPop_runs {registers : Nat} (bank : WordBank registers)
    (distinct : Function.Injective bank) (values : Store registers) :
    Runs (wordPop bank) values
      (wordStore bank values (values (bank 0) / 64) 0 (values (bank 0) % 64)
        (63 - values (bank 0) % 64)) := by
  let first := write values (bank 1) 0
  let second := write first (bank 2) 0
  let prepared := write second (bank 3) 63
  have firstRun := clear_runs (bank 1) values
  have secondRun := clear_runs (bank 2) first
  have thirdRun := setConstant_runs (bank 3) 63 second
  have prepareEq : prepared = wordStore bank values (values (bank 0)) 0 0 63 := by
    funext current
    by_cases at0 : current = bank 0
    <;> by_cases at1 : current = bank 1
    <;> by_cases at2 : current = bank 2
    <;> by_cases at3 : current = bank 3
    <;> simp_all [prepared, second, first, wordStore, write, distinct.eq_iff]
  have loopRun := wordDivisionLoop_runs bank distinct values (values (bank 0)) 0 0 (by decide)
  simp only [Nat.zero_add, Nat.sub_zero] at loopRun
  rw [← prepareEq] at loopRun
  let divided := wordStore bank values 0 (values (bank 0) / 64)
    (values (bank 0) % 64) (63 - values (bank 0) % 64)
  have moveRun := drain_runs (bank 1) [bank 0]
    (by simp [distinct.eq_iff]) divided
  have combined := append_runs firstRun (append_runs secondRun
    (append_runs thirdRun (append_runs loopRun moveRun)))
  have finalEq : (fun register => if register = bank 1 then 0
        else divided register + [bank 0].count register * divided (bank 1)) =
      wordStore bank values (values (bank 0) / 64) 0 (values (bank 0) % 64)
        (63 - values (bank 0) % 64) := by
    funext current
    by_cases at0 : current = bank 0
    <;> by_cases at1 : current = bank 1
    <;> by_cases at2 : current = bank 2
    <;> by_cases at3 : current = bank 3
    <;> simp_all [divided, wordStore, write, distinct.eq_iff]
    simp [Ne.symm at0]
  exact finalEq ▸ combined

end Yulang.CanonicalRegisterMachine.Routine
