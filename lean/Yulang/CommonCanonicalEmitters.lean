import Yulang.CommonCanonicalWordPrograms

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

end Yulang.CommonCanonicalEmitters
