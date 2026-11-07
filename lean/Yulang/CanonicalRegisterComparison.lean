import Yulang.CanonicalRegisterMacros

/-! Concrete total natural-counter comparison, without an equality oracle. -/

namespace Yulang.CanonicalRegisterMachine.Routine

def comparisonBody {registers : Nat} (first last flag : Fin (registers + 1)) : Routine registers :=
  branch last (append (clear first) (setConstant flag 1)) skip

def comparisonLoop {registers : Nat} (first last flag : Fin (registers + 1)) : Routine registers :=
  loop first (comparisonBody first last flag)

/-- Pairwise decrement consumes the first counter. If the second runs out
early, the loop clears the remaining first counter and records a mismatch. -/
theorem comparisonLoop_runs {registers : Nat} (first last flag : Fin (registers + 1))
    (firstLast : first ≠ last) (firstFlag : first ≠ flag) (lastFlag : last ≠ flag)
    (values : Store registers) (cleared : values flag = 0) :
    Runs (comparisonLoop first last flag) values
      (write (write (write values first 0) last (values last - values first))
        flag (if values last < values first then 1 else 0)) := by
  apply loop_runs
  generalize countEq : values first = count
  induction count generalizing values with
  | zero =>
      have same : write (write (write values first 0) last (values last - 0))
          flag (if values last < 0 then 1 else 0) = values := by
        funext current
        by_cases atFirst : current = first
        <;> by_cases atLast : current = last
        <;> by_cases atFlag : current = flag
        <;> simp_all [write]
      rw [same]
      exact .done countEq
  | succ count ih =>
      let cut := write values first count
      have cutLast : cut last = values last := by simp only [cut, write, Ne.symm firstLast, ↓reduceIte]
      have cutEq : write values first (values first - 1) = cut := by
        simp only [countEq, Nat.add_sub_cancel, cut]
      by_cases empty : values last = 0
      · let final := write (write values first 0) flag 1
        have body : Runs (comparisonBody first last flag) cut final := by
          apply branch_runs
          rw [ite_eq_left (cutLast.trans empty)]
          have execution := append_runs (clear_runs first cut)
            (setConstant_runs flag 1 (write cut first 0))
          simpa only [cut, write_shadow] using execution
        have bodyCorrect : Runs (comparisonBody first last flag)
            (write values first (values first - 1)) final := by
          rw [cutEq]
          exact body
        have finalFirst : final first = 0 := by simp [final, write, firstFlag]
        have same : write (write (write values first 0) last (values last - (count + 1)))
            flag (if values last < count + 1 then 1 else 0) = final := by
          funext current
          by_cases atFirst : current = first
          <;> by_cases atLast : current = last
          <;> by_cases atFlag : current = flag
          <;> simp_all [final, write]
        rw [same]
        exact .next (by omega) bodyCorrect (.done finalFirst)
      · let lower := write cut last (values last - 1)
        have body : Runs (comparisonBody first last flag) cut lower := by
          apply branch_runs
          rw [ite_eq_right (by simpa only [cutLast] using empty)]
          rw [cutLast]
          exact atomic_runs (.jump ()) lower
        have bodyCorrect : Runs (comparisonBody first last flag)
            (write values first (values first - 1)) lower := by
          rw [cutEq]
          exact body
        have lowerFirst : lower first = count := by simp [lower, cut, write, firstLast]
        have lowerFlag : lower flag = 0 := by
          simp [lower, cut, write, Ne.symm lastFlag, Ne.symm firstFlag, cleared]
        have lowerLast : lower last = values last - 1 := by simp [lower, write]
        have remaining := ih lower lowerFlag lowerFirst
        have subtraction : values last - 1 - count = values last - (count + 1) := by omega
        have less : values last - 1 < count ↔ values last < count + 1 := by omega
        have same : write (write (write lower first 0) last (lower last - count))
              flag (if lower last < count then 1 else 0) =
            write (write (write values first 0) last (values last - (count + 1)))
              flag (if values last < count + 1 then 1 else 0) := by
          simp only [lowerLast, subtraction, less]
          funext current
          by_cases atFirst : current = first
          <;> by_cases atLast : current = last
          <;> by_cases atFlag : current = flag
          <;> simp_all [lower, cut, write]
        rw [same] at remaining
        exact .next (by omega) bodyCorrect remaining

def comparisonTail {registers : Nat} (last flag : Fin (registers + 1)) : Routine registers :=
  branch last skip (append (clear last) (setConstant flag 1))

def compareCounters {registers : Nat} (first last flag : Fin (registers + 1)) : Routine registers :=
  append (clear flag) (append (comparisonLoop first last flag) (comparisonTail last flag))

/-- Total equality comparison consumes both input counters and returns zero
for equality, one for inequality. No prior flag contents are assumed. -/
theorem compareCounters_runs {registers : Nat} (first last flag : Fin (registers + 1))
    (firstLast : first ≠ last) (firstFlag : first ≠ flag) (lastFlag : last ≠ flag)
    (values : Store registers) :
    Runs (compareCounters first last flag) values
      (write (write (write values first 0) last 0) flag (if values first = values last then 0 else 1)) := by
  let prepared := write values flag 0
  let middle := write (write (write prepared first 0) last (values last - values first))
    flag (if values last < values first then 1 else 0)
  let final := write (write (write values first 0) last 0)
    flag (if values first = values last then 0 else 1)
  have preparedFirst : prepared first = values first := by simp only [prepared, write, firstFlag, ↓reduceIte]
  have preparedLast : prepared last = values last := by simp only [prepared, write, lastFlag, ↓reduceIte]
  have preparedFlag : prepared flag = 0 := by simp only [prepared, write, ↓reduceIte]
  have loopRun := comparisonLoop_runs first last flag firstLast firstFlag lastFlag prepared preparedFlag
  rw [preparedFirst, preparedLast] at loopRun
  have middleLast : middle last = values last - values first := by simp only [middle, write, lastFlag, ↓reduceIte]
  have tailRun : Runs (comparisonTail last flag) middle final := by
    apply branch_runs
    by_cases empty : values last - values first = 0
    · rw [ite_eq_left (middleLast.trans empty)]
      have flagEq : (if values last < values first then 1 else 0) =
          (if values first = values last then 0 else 1) := by
        by_cases same : values first = values last
        · simp only [same, Nat.lt_irrefl, ↓reduceIte]
        · have less : values last < values first := by omega
          simp only [same, less, ↓reduceIte]
      have storeEq : middle = final := by
        simp only [middle, empty, flagEq, final]
        funext current
        by_cases atFirst : current = first
        <;> by_cases atLast : current = last
        <;> by_cases atFlag : current = flag
        <;> simp_all [prepared, write]
      rw [← storeEq]
      exact atomic_runs (.jump ()) middle
    · rw [ite_eq_right (by simpa only [middleLast] using empty)]
      have unequal : values first ≠ values last := by omega
      have execute := append_runs (clear_runs last (write middle last (middle last - 1)))
        (setConstant_runs flag 1 (write (write middle last (middle last - 1)) last 0))
      simp only [write_shadow] at execute
      have storeEq : write (write middle last 0) flag 1 = final := by
        funext current
        by_cases atFirst : current = first
        <;> by_cases atLast : current = last
        <;> by_cases atFlag : current = flag
        <;> simp_all [middle, prepared, final, write]
      exact storeEq ▸ execute
  exact append_runs (clear_runs flag values) (append_runs loopRun tailRun)

end Yulang.CanonicalRegisterMachine.Routine
