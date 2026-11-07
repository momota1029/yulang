import Yulang.CommonCanonicalEmitters

/-! Finite coordinate-list emission with a runtime bounded loop. -/

namespace Yulang.CommonCanonicalRangeEmitters

open CanonicalRegisterMachine
open CanonicalRegisterMachine.Routine
open CommonCanonicalSerialization
open CommonCanonicalEmitters

def rangeInputs {registers parameters : Nat} (inputs : Fin parameters → Fin (registers + 1))
    (coordinate fuel : Fin (registers + 1)) : Fin (parameters + 2) → Fin (registers + 1) :=
  Fin.addCases inputs (Fin.cases coordinate (fun _ => fuel))

def rangeTokens (tokens : Nat → Word) (start : Nat) : Nat → Word
  | 0 => []
  | count + 1 => tokens start ++ rangeTokens tokens (start + 1) count

def rangeLoop {registers : Nat} (coordinate fuel : Fin (registers + 1))
    (body : Routine registers) : Routine registers :=
  loop fuel (append body (increment coordinate))

/-- A concrete loop emits the exact remaining coordinate range. The body
preserves coordinate and fuel; only the enclosing loop changes them. -/
theorem rangeLoop_runs {registers parameters : Nat}
    (inputs : Fin parameters → Fin (registers + 1)) (output coordinate fuel : Fin (registers + 1))
    (coordinateFuel : coordinate ≠ fuel) (outputCoordinate : output ≠ coordinate) (outputFuel : output ≠ fuel)
    (separated : ∀ index, inputs index ≠ coordinate ∧ inputs index ≠ fuel)
    (body : Routine registers) (tokens : Environment parameters → Nat → Word)
    (bodyCorrect : Emits body (rangeInputs inputs coordinate fuel) output
      (fun environment => tokens (fun index => environment (index.castAdd 2))
        (environment (Fin.natAdd parameters 0))))
    (start count : Nat) (prior : Word) (values : Store registers)
    (fuelEq : values fuel = count) (coordinateEq : values coordinate = start)
    (input : values output = wordCode prior) :
    ∃ finalValues,
      Runs (rangeLoop coordinate fuel body) values finalValues ∧
      finalValues output = wordCode
        ((rangeTokens (tokens (fun index => values (inputs index))) start count).reverse ++ prior) ∧
      finalValues coordinate = start + count ∧ finalValues fuel = 0 ∧
      ∀ index, finalValues (inputs index) = values (inputs index) := by
  suffices ∃ finalValues,
      LoopRuns fuel (append body (increment coordinate)) values finalValues ∧
      finalValues output = wordCode
        ((rangeTokens (tokens (fun index => values (inputs index))) start count).reverse ++ prior) ∧
      finalValues coordinate = start + count ∧ finalValues fuel = 0 ∧
      ∀ index, finalValues (inputs index) = values (inputs index) by
    obtain ⟨finalValues, execution, encoded, finalCoordinate, finalFuel, frame⟩ := this
    exact ⟨finalValues, loop_runs execution, encoded, finalCoordinate, finalFuel, frame⟩
  induction count generalizing start prior values with
  | zero =>
      refine ⟨values, .done fuelEq, ?_, ?_, fuelEq, fun _ => rfl⟩
      · simpa only [rangeTokens, List.reverse_nil, List.nil_append] using input
      · simpa only [Nat.add_zero] using coordinateEq
  | succ count ih =>
      let cut := write values fuel count
      have cutInput : cut output = wordCode prior := by simp only [cut, write, outputFuel, ↓reduceIte, input]
      obtain ⟨middle, bodyRun, middleWord, middleFrame⟩ := bodyCorrect cut prior cutInput
      have environmentEq : (fun index : Fin parameters => cut (rangeInputs inputs coordinate fuel (index.castAdd 2))) =
          (fun index => values (inputs index)) := by
        funext index
        simp only [rangeInputs, Fin.addCases_left, cut, write, (separated index).2, ↓reduceIte]
      have bodyCoordinate : cut (rangeInputs inputs coordinate fuel (Fin.natAdd parameters 0)) = start := by
        simp only [rangeInputs, Fin.addCases_right, Fin.cases_zero, cut, write, coordinateFuel, ↓reduceIte, coordinateEq]
      change middle output = wordCode ((tokens
        (fun index => cut (rangeInputs inputs coordinate fuel (index.castAdd 2)))
        (cut (rangeInputs inputs coordinate fuel (Fin.natAdd parameters 0)))).reverse ++ prior) at middleWord
      rw [environmentEq, bodyCoordinate] at middleWord
      have middleOriginal (index : Fin parameters) : middle (inputs index) = values (inputs index) := by
        simpa only [rangeInputs, Fin.addCases_left, cut, write, (separated index).2, ↓reduceIte]
          using middleFrame (index.castAdd 2)
      have middleCoordinate : middle coordinate = start := by
        simpa only [rangeInputs, Fin.addCases_right, Fin.cases_zero, cut, write, coordinateFuel,
          ↓reduceIte, coordinateEq] using middleFrame (Fin.natAdd parameters 0)
      have middleFuel : middle fuel = count := by
        simpa only [rangeInputs, Fin.addCases_right, Fin.cases_succ, cut, write, ↓reduceIte]
          using middleFrame (Fin.natAdd parameters ((0 : Fin 1).succ))
      let after := write middle coordinate (middle coordinate + 1)
      have incrementRun := atomic_runs (.increment coordinate ()) middle
      have afterCoordinate : after coordinate = start + 1 := by simp only [after, write, ↓reduceIte, middleCoordinate]
      have afterFuel : after fuel = count := by
        simp only [after, write, Ne.symm coordinateFuel, ↓reduceIte, middleFuel]
      have afterInput : after output = wordCode
          ((tokens (fun index => values (inputs index)) start).reverse ++ prior) := by
        simpa only [after, write, outputCoordinate, ↓reduceIte] using middleWord
      have afterOriginal (index : Fin parameters) : after (inputs index) = values (inputs index) := by
        simp only [after, write, (separated index).1, ↓reduceIte, middleOriginal]
      obtain ⟨finalValues, remaining, encoded, finalCoordinate, finalFuel, frame⟩ :=
        ih (start := start + 1) (prior := (tokens (fun index => values (inputs index)) start).reverse ++ prior)
          (values := after) afterFuel afterCoordinate afterInput
      have afterEnvironment : (fun index => after (inputs index)) = (fun index => values (inputs index)) := by
        funext index
        exact afterOriginal index
      rw [afterEnvironment] at encoded
      have cutEq : write values fuel (values fuel - 1) = cut := by simp only [fuelEq, Nat.add_sub_cancel, cut]
      have stepRun : Runs (append body (increment coordinate)) (write values fuel (values fuel - 1)) after := by
        rw [cutEq]
        exact append_runs bodyRun incrementRun
      refine ⟨finalValues, .next (by omega) stepRun remaining, ?_, ?_, finalFuel, ?_⟩
      · simpa only [rangeTokens, List.reverse_append, List.append_assoc] using encoded
      · omega
      · intro index
        exact (frame index).trans (afterOriginal index)

/-- Enumerate coordinates zero through the supplied additional-register
count, inclusive. A source program has that count plus one actual counters. -/
def rangeEmit {registers : Nat} (source coordinate fuel temporary : Fin (registers + 1))
    (body : Routine registers) : Routine registers :=
  append (copy source fuel temporary)
    (append (increment fuel) (append (clear coordinate) (rangeLoop coordinate fuel body)))

theorem emits_range {registers parameters : Nat}
    (inputs : Fin parameters → Fin (registers + 1)) (output coordinate fuel temporary : Fin (registers + 1))
    (coordinateFuel : coordinate ≠ fuel) (fuelTemporary : fuel ≠ temporary)
    (outputCoordinate : output ≠ coordinate) (outputFuel : output ≠ fuel) (outputTemporary : output ≠ temporary)
    (separated : ∀ index, inputs index ≠ coordinate ∧ inputs index ≠ fuel ∧ inputs index ≠ temporary)
    (bound : Fin parameters) (body : Routine registers) (tokens : Environment parameters → Nat → Word)
    (bodyCorrect : Emits body (rangeInputs inputs coordinate fuel) output
      (fun environment => tokens (fun index => environment (index.castAdd 2))
        (environment (Fin.natAdd parameters 0)))) :
    Emits (rangeEmit (inputs bound) coordinate fuel temporary body) inputs output
      (fun environment => rangeTokens (tokens environment) 0 (environment bound + 1)) := by
  intro values prior input
  let copied := write (write values fuel (values (inputs bound))) temporary 0
  let counted := write copied fuel (copied fuel + 1)
  let prepared := write counted coordinate 0
  have copyRun := copy_runs (inputs bound) fuel temporary
    (separated bound).2.1 (separated bound).2.2 fuelTemporary values
  have incrementRun := atomic_runs (.increment fuel ()) copied
  have clearRun := clear_runs coordinate counted
  have copiedFuel : copied fuel = values (inputs bound) := by
    simp only [copied, write, fuelTemporary, ↓reduceIte]
  have preparedFuel : prepared fuel = values (inputs bound) + 1 := by
    simp only [prepared, counted, write, Ne.symm coordinateFuel, ↓reduceIte, copiedFuel]
  have preparedCoordinate : prepared coordinate = 0 := by simp only [prepared, write, ↓reduceIte]
  have preparedOutput : prepared output = wordCode prior := by
    simpa only [prepared, counted, copied, write, outputCoordinate, outputFuel, outputTemporary, ↓reduceIte] using input
  have preparedFrame (index : Fin parameters) : prepared (inputs index) = values (inputs index) := by
    simp only [prepared, counted, copied, write, (separated index).1,
      (separated index).2.1, (separated index).2.2, ↓reduceIte]
  obtain ⟨finalValues, loopRun, encoded, _, _, frame⟩ := rangeLoop_runs inputs output coordinate fuel
    coordinateFuel outputCoordinate outputFuel (fun index => ⟨(separated index).1, (separated index).2.1⟩)
    body tokens bodyCorrect 0 (values (inputs bound) + 1) prior prepared preparedFuel preparedCoordinate preparedOutput
  have environmentEq : (fun index => prepared (inputs index)) = (fun index => values (inputs index)) := by
    funext index
    exact preparedFrame index
  rw [environmentEq] at encoded
  refine ⟨finalValues, append_runs copyRun (append_runs incrementRun (append_runs clearRun loopRun)), encoded, ?_⟩
  intro index
  exact (frame index).trans (preparedFrame index)

end Yulang.CommonCanonicalRangeEmitters
