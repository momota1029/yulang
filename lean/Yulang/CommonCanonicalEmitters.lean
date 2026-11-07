import Yulang.CommonCanonicalWordPrograms
import Yulang.CanonicalRegisterComparison

/-!
# Compositional specifications for actual finite template emitters

`Emits` is a proposition about an already constructed counter routine. Its
word function is a specification, never a primitive machine instruction.
Protected parameter registers make concatenation preserve template inputs.
-/

namespace Yulang.CommonCanonicalEmitters

open CanonicalRegisterMachine
open CanonicalRegisterMachine.Routine
open CommonCanonicalSerialization
open CommonCanonicalWordPrograms

abbrev Environment (parameters : Nat) := Fin parameters → Nat

def Emits {registers parameters : Nat} (routine : Routine registers)
    (inputs : Fin parameters → Fin (registers + 1)) (output : Fin (registers + 1))
    (tokens : Environment parameters → Word) : Prop :=
  ∀ values : Store registers, ∀ prior : Word, values output = wordCode prior →
    ∃ finalValues,
      Runs routine values finalValues ∧
      finalValues output = wordCode ((tokens (fun index => values (inputs index))).reverse ++ prior) ∧
      ∀ index, finalValues (inputs index) = values (inputs index)

/-- A semantic specification for concatenation is proved by linking the
actual finite tables and composing their finite executions. -/
theorem emits_append {registers parameters : Nat} {first last : Routine registers}
    {inputs : Fin parameters → Fin (registers + 1)} {output : Fin (registers + 1)}
    {firstTokens lastTokens : Environment parameters → Word}
    (firstCorrect : Emits first inputs output firstTokens)
    (lastCorrect : Emits last inputs output lastTokens) :
    Emits (append first last) inputs output (fun environment => firstTokens environment ++ lastTokens environment) := by
  intro values prior input
  obtain ⟨middle, firstRun, middleWord, firstFrame⟩ := firstCorrect values prior input
  obtain ⟨finalValues, lastRun, finalWord, lastFrame⟩ := lastCorrect middle
    ((firstTokens (fun index => values (inputs index))).reverse ++ prior) middleWord
  have sameEnvironment : (fun index => middle (inputs index)) = (fun index => values (inputs index)) := by
    funext index
    exact firstFrame index
  rw [sameEnvironment] at finalWord
  refine ⟨finalValues, append_runs firstRun lastRun, ?_, ?_⟩
  · simpa only [List.reverse_append, List.append_assoc] using finalWord
  · intro index
    exact (lastFrame index).trans (firstFrame index)

theorem emits_literal {registers parameters : Nat}
    (inputs : Fin parameters → Fin (registers + 1)) (output temporary : Fin (registers + 1))
    (distinct : output ≠ temporary)
    (separated : ∀ index, inputs index ≠ output ∧ inputs index ≠ temporary) (tokens : Word) :
    Emits (emit output temporary tokens) inputs output (fun _ => tokens) := by
  intro values prior input
  let finalValues := write (write values output (wordCode (tokens.reverse ++ prior))) temporary 0
  refine ⟨finalValues, emit_runs output temporary distinct tokens prior values input, ?_, ?_⟩
  · simp only [finalValues, write, distinct, ↓reduceIte]
  · intro index
    simp only [finalValues, write, (separated index).1, (separated index).2, ↓reduceIte]

theorem emits_natural {registers parameters : Nat} (bank : WordBank registers)
    (distinct : Function.Injective bank) (inputs : Fin parameters → Fin (registers + 1))
    (source : Fin parameters) (sourceEq : bank 1 = inputs source)
    (separated : ∀ index, inputs index ≠ bank 0 ∧ inputs index ≠ bank 2 ∧ inputs index ≠ bank 3) :
    Emits (emitNatural bank) inputs (bank 0) (fun environment => natural (environment source)) := by
  intro values prior input
  let finalValues := write (write (write values (bank 0)
    (wordCode ((natural (values (bank 1))).reverse ++ prior))) (bank 2) 0) (bank 3) 0
  refine ⟨finalValues, emitNatural_runs bank distinct prior values input, ?_, ?_⟩
  · simp only [finalValues, write, distinct.eq_iff, Fin.isValue, Fin.reduceEq, ↓reduceIte, sourceEq]
  · intro index
    simp only [finalValues, write, (separated index).1, (separated index).2.1,
      (separated index).2.2, ↓reduceIte]

theorem emits_sum {registers parameters : Nat} (bank : WordBank registers)
    (distinct : Function.Injective bank) (inputs : Fin parameters → Fin (registers + 1))
    (first last : Fin parameters) (lastEq : bank 1 = inputs last)
    (separated : ∀ index, inputs index ≠ bank 0 ∧ inputs index ≠ bank 2 ∧ inputs index ≠ bank 3) :
    Emits (emitSum bank (inputs first)) inputs (bank 0)
      (fun environment => natural (environment first + environment last)) := by
  intro values prior input
  let finalValues := write (write (write values (bank 0)
    (wordCode ((natural (values (inputs first) + values (bank 1))).reverse ++ prior))) (bank 2) 0) (bank 3) 0
  refine ⟨finalValues, emitSum_runs bank distinct (inputs first)
    (separated first).2.1 (separated first).2.2 prior values input, ?_, ?_⟩
  · simp only [finalValues, write, distinct.eq_iff, Fin.isValue, Fin.reduceEq, ↓reduceIte, lastEq]
  · intro index
    simp only [finalValues, write, (separated index).1, (separated index).2.1,
      (separated index).2.2, ↓reduceIte]

def repeatLiteral {registers : Nat} (bank : WordBank registers) (tokens : Word) : Routine registers :=
  append (copy (bank 1) (bank 2) (bank 3)) (repeatEmit (bank 2) (bank 0) (bank 3) tokens)

theorem emits_repeat_literal {registers parameters : Nat} (bank : WordBank registers)
    (distinct : Function.Injective bank) (inputs : Fin parameters → Fin (registers + 1))
    (source : Fin parameters) (sourceEq : bank 1 = inputs source)
    (separated : ∀ index, inputs index ≠ bank 0 ∧ inputs index ≠ bank 2 ∧ inputs index ≠ bank 3)
    (tokens : Word) :
    Emits (repeatLiteral bank tokens) inputs (bank 0)
      (fun environment => repeatTokens tokens (environment source)) := by
  intro values prior input
  let copied := write (write values (bank 2) (values (bank 1))) (bank 3) 0
  have copyRun := copy_runs (bank 1) (bank 2) (bank 3)
    (by simp [distinct.eq_iff]) (by simp [distinct.eq_iff]) (by simp [distinct.eq_iff]) values
  have copiedInput : copied (bank 0) = wordCode prior := by
    simpa only [copied, write, distinct.eq_iff, Fin.isValue, Fin.reduceEq, ↓reduceIte] using input
  have copiedCount : copied (bank 2) = values (bank 1) := by simp [copied, write, distinct.eq_iff]
  have repetition := repeatEmit_runs (bank 2) (bank 0) (bank 3)
    (by simp [distinct.eq_iff]) (by simp [distinct.eq_iff]) (by simp [distinct.eq_iff]) tokens prior copied copiedInput
  rw [copiedCount] at repetition
  let finalValues := write (write (write copied (bank 2) 0)
    (bank 0) (wordCode ((repeatTokens tokens (values (bank 1))).reverse ++ prior))) (bank 3) 0
  refine ⟨finalValues, append_runs copyRun repetition, ?_, ?_⟩
  · simp only [finalValues, write, distinct.eq_iff, Fin.isValue, Fin.reduceEq, ↓reduceIte, sourceEq]
  · intro index
    simp only [finalValues, copied, write, (separated index).1, (separated index).2.1,
      (separated index).2.2, ↓reduceIte]

def chooseEqual {registers : Nat} (work : WordBank registers)
    (first last : Fin (registers + 1)) (equal different : Routine registers) : Routine registers :=
  append (copy first (work 0) (work 3))
    (append (copy last (work 1) (work 3))
      (append (compareCounters (work 0) (work 1) (work 2)) (branch (work 2) equal different)))

theorem emits_choose_equal {registers parameters : Nat} (work : WordBank registers)
    (distinct : Function.Injective work) (inputs : Fin parameters → Fin (registers + 1))
    (output : Fin (registers + 1)) (outputOutside : ∀ index, output ≠ work index)
    (separated : ∀ parameter index, inputs parameter ≠ work index)
    (first last : Fin parameters) {equal different : Routine registers}
    {equalTokens differentTokens : Environment parameters → Word}
    (equalCorrect : Emits equal inputs output equalTokens)
    (differentCorrect : Emits different inputs output differentTokens) :
    Emits (chooseEqual work (inputs first) (inputs last) equal different) inputs output
      (fun environment => if environment first = environment last then equalTokens environment else differentTokens environment) := by
  intro values prior input
  let copiedFirst := write (write values (work 0) (values (inputs first))) (work 3) 0
  let copiedLast := write (write copiedFirst (work 1) (values (inputs last))) (work 3) 0
  let prepared := write (write (write copiedLast (work 0) 0) (work 1) 0) (work 2)
    (if values (inputs first) = values (inputs last) then 0 else 1)
  have firstRun := copy_runs (inputs first) (work 0) (work 3)
    (separated first 0) (separated first 3) (by simp [distinct.eq_iff]) values
  have lastStable : copiedFirst (inputs last) = values (inputs last) := by
    simp only [copiedFirst, write, separated, ↓reduceIte]
  have lastRun := copy_runs (inputs last) (work 1) (work 3)
    (separated last 1) (separated last 3) (by simp [distinct.eq_iff]) copiedFirst
  rw [lastStable] at lastRun
  have copiedFirstValue : copiedLast (work 0) = values (inputs first) := by
    simp [copiedLast, copiedFirst, write, distinct.eq_iff]
  have copiedLastValue : copiedLast (work 1) = values (inputs last) := by
    simp [copiedLast, write, distinct.eq_iff]
  have compareRun := compareCounters_runs (work 0) (work 1) (work 2)
    (by simp [distinct.eq_iff]) (by simp [distinct.eq_iff]) (by simp [distinct.eq_iff]) copiedLast
  rw [copiedFirstValue, copiedLastValue] at compareRun
  have preparedFrame (index : Fin parameters) : prepared (inputs index) = values (inputs index) := by
    simp only [prepared, copiedLast, copiedFirst, write, separated, ↓reduceIte]
  have preparedOutput : prepared output = wordCode prior := by
    simpa only [prepared, copiedLast, copiedFirst, write, outputOutside, ↓reduceIte] using input
  have preparedFlag : prepared (work 2) = if values (inputs first) = values (inputs last) then 0 else 1 := by
    simp only [prepared, write, ↓reduceIte]
  have branchExecution : ∃ finalValues, Runs (branch (work 2) equal different) prepared finalValues ∧
      finalValues output = wordCode
        ((if values (inputs first) = values (inputs last) then equalTokens (fun index => values (inputs index))
          else differentTokens (fun index => values (inputs index))).reverse ++ prior) ∧
      ∀ index, finalValues (inputs index) = values (inputs index) := by
    by_cases same : values (inputs first) = values (inputs last)
    · obtain ⟨finalValues, execution, encoded, frame⟩ := equalCorrect prepared prior preparedOutput
      have environmentEq : (fun index => prepared (inputs index)) = (fun index => values (inputs index)) := by
        funext index
        exact preparedFrame index
      rw [environmentEq] at encoded
      refine ⟨finalValues, ?_, ?_, ?_⟩
      · apply branch_runs
        simpa only [preparedFlag, same, ↓reduceIte] using execution
      · simpa only [same, ↓reduceIte] using encoded
      · intro index
        exact (frame index).trans (preparedFrame index)
    · let selected := write prepared (work 2) 0
      have selectedOutput : selected output = wordCode prior := by
        simp only [selected, write, outputOutside, ↓reduceIte, preparedOutput]
      have selectedFrame (index : Fin parameters) : selected (inputs index) = values (inputs index) := by
        simp only [selected, write, separated, ↓reduceIte, preparedFrame]
      obtain ⟨finalValues, execution, encoded, frame⟩ := differentCorrect selected prior selectedOutput
      have environmentEq : (fun index => selected (inputs index)) = (fun index => values (inputs index)) := by
        funext index
        exact selectedFrame index
      rw [environmentEq] at encoded
      refine ⟨finalValues, ?_, ?_, ?_⟩
      · apply branch_runs
        simpa only [preparedFlag, same, Nat.one_ne_zero, ↓reduceIte, Nat.sub_self] using execution
      · simpa only [same, ↓reduceIte] using encoded
      · intro index
        exact (frame index).trans (selectedFrame index)
  obtain ⟨finalValues, selectedRun, encoded, frame⟩ := branchExecution
  exact ⟨finalValues, append_runs firstRun (append_runs lastRun (append_runs compareRun selectedRun)), encoded, frame⟩

end Yulang.CommonCanonicalEmitters
