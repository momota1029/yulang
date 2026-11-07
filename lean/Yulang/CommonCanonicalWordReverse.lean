import Yulang.CommonCanonicalWordPrograms

/-! Reversal of the actual finite-word encoding by finite counter routines. -/

namespace Yulang.CommonCanonicalWordReverse

open CanonicalRegisterMachine
open CanonicalRegisterMachine.Routine
open CommonCanonicalSerialization
open CommonCanonicalWordPrograms

def reverseBody {registers : Nat} (bank : WordBank registers)
    (output : Fin (registers + 1)) : Routine registers :=
  append (increment (bank 0)) (append (wordPop bank) (pushCounter 64 (bank 2) output (bank 1)))

/-- The surrounding while consumes one unit to test positivity. The body
restores it, pops the actual token, then pushes that token onto the other word. -/
theorem reverseBody_runs {registers : Nat} (bank : WordBank registers)
    (distinct : Function.Injective bank) (output : Fin (registers + 1))
    (outside : ∀ index, output ≠ bank index) (token : Token) (rest prior : Word)
    (values : Store registers) (input : values (bank 0) = wordCode (token :: rest))
    (accumulator : values output = wordCode prior) :
    Runs (reverseBody bank output) (write values (bank 0) (values (bank 0) - 1))
      (wordStore bank (write values output (wordCode (token :: prior))) (wordCode rest) 0 0 (63 - token.digit)) := by
  have tokenPositive : 0 < token.digit := by cases token <;> decide
  have inputPositive : 0 < values (bank 0) := by
    change values (bank 0) = token.digit + 64 * wordCode rest at input
    omega
  have restoreRun : Runs (increment (bank 0))
      (write values (bank 0) (values (bank 0) - 1)) values := by
    have execution := atomic_runs (.increment (bank 0) ())
      (write values (bank 0) (values (bank 0) - 1))
    simp only [Op.eval] at execution
    have atSource : write values (bank 0) (values (bank 0) - 1) (bank 0) = values (bank 0) - 1 := by
      simp only [write, ↓reduceIte]
    rw [atSource, write_shadow] at execution
    have restored : values (bank 0) - 1 + 1 = values (bank 0) := by omega
    rw [restored] at execution
    have selfWrite : write values (bank 0) (values (bank 0)) = values := by
      funext current
      by_cases equal : current = bank 0
      · subst current
        simp only [write, ↓reduceIte]
      · simp only [write, equal, ↓reduceIte]
    rw [selfWrite] at execution
    exact execution
  let popped := wordStore bank values (wordCode rest) 0 token.digit (63 - token.digit)
  have popRun := wordPop_token bank distinct values token rest input
  have poppedOutput : popped output = values output := by simp only [popped, wordStore, write, outside, ↓reduceIte]
  have poppedDigit : popped (bank 2) = token.digit := by simp [popped, wordStore, write, distinct.eq_iff]
  have pushRun := pushCounter_runs 64 (bank 2) output (bank 1) (Ne.symm (outside 2))
    (by simp [distinct.eq_iff]) (outside 1) popped
  have pushedCode : 64 * popped output + popped (bank 2) = wordCode (token :: prior) := by
    rw [poppedOutput, poppedDigit, accumulator]
    simp only [wordCode]
    omega
  rw [pushedCode] at pushRun
  have combined := append_runs restoreRun (append_runs popRun pushRun)
  have same : write (write (write popped output (wordCode (token :: prior))) (bank 2) 0) (bank 1) 0 =
      wordStore bank (write values output (wordCode (token :: prior))) (wordCode rest) 0 0 (63 - token.digit) := by
    funext current
    by_cases at0 : current = bank 0
    <;> by_cases at1 : current = bank 1
    <;> by_cases at2 : current = bank 2
    <;> by_cases at3 : current = bank 3
    <;> by_cases atOutput : current = output
    <;> simp_all [popped, wordStore, write, distinct.eq_iff]
  exact same ▸ combined

def reverseLoop {registers : Nat} (bank : WordBank registers)
    (output : Fin (registers + 1)) : Routine registers :=
  loop (bank 0) (reverseBody bank output)

theorem reverseLoop_runs {registers : Nat} (bank : WordBank registers)
    (distinct : Function.Injective bank) (output : Fin (registers + 1))
    (outside : ∀ index, output ≠ bank index) (tokens prior : Word)
    (values : Store registers) (input : values (bank 0) = wordCode tokens)
    (accumulator : values output = wordCode prior) :
    ∃ quotient digit countdown,
      Runs (reverseLoop bank output) values
        (wordStore bank (write values output (wordCode (tokens.reverse ++ prior))) 0 quotient digit countdown) := by
  suffices ∃ quotient digit countdown,
      LoopRuns (bank 0) (reverseBody bank output) values
        (wordStore bank (write values output (wordCode (tokens.reverse ++ prior))) 0 quotient digit countdown) by
    obtain ⟨quotient, digit, countdown, execution⟩ := this
    exact ⟨quotient, digit, countdown, loop_runs execution⟩
  induction tokens generalizing prior values with
  | nil =>
      refine ⟨values (bank 1), values (bank 2), values (bank 3), ?_⟩
      simp only [List.reverse_nil, List.nil_append]
      have same : wordStore bank (write values output (wordCode prior)) 0
          (values (bank 1)) (values (bank 2)) (values (bank 3)) = values := by
        funext current
        by_cases at0 : current = bank 0
        <;> by_cases at1 : current = bank 1
        <;> by_cases at2 : current = bank 2
        <;> by_cases at3 : current = bank 3
        <;> by_cases atOutput : current = output
        <;> simp_all [wordStore, write, wordCode, distinct.eq_iff]
      rw [same]
      exact .done input
  | cons token rest ih =>
      let middle := wordStore bank (write values output (wordCode (token :: prior)))
        (wordCode rest) 0 0 (63 - token.digit)
      have middleInput : middle (bank 0) = wordCode rest := by simp [middle, wordStore, write, distinct.eq_iff]
      have middleOutput : middle output = wordCode (token :: prior) := by
        simp only [middle, wordStore, write, outside, ↓reduceIte]
      obtain ⟨quotient, digit, countdown, remaining⟩ := ih (token :: prior) middle middleInput middleOutput
      change LoopRuns (bank 0) (reverseBody bank output) middle
        (wordStore bank (write (wordStore bank (write values output (wordCode (token :: prior)))
          (wordCode rest) 0 0 (63 - token.digit)) output (wordCode (rest.reverse ++ token :: prior)))
          0 quotient digit countdown) at remaining
      rw [wordStore_write_frame, write_shadow] at remaining
      have order : rest.reverse ++ token :: prior = (token :: rest).reverse ++ prior := by
        simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      rw [order] at remaining
      have body := reverseBody_runs bank distinct output outside token rest prior values input accumulator
      have tokenPositive : 0 < token.digit := by cases token <;> decide
      have positive : values (bank 0) ≠ 0 := by
        change values (bank 0) = token.digit + 64 * wordCode rest at input
        omega
      exact ⟨quotient, digit, countdown, .next positive body remaining⟩

def reverseWord {registers : Nat} (bank : WordBank registers)
    (output : Fin (registers + 1)) : Routine registers :=
  append (clear output) (append (reverseLoop bank output) (clearList [bank 1, bank 2, bank 3]))

/-- Reverse a serialized finite word, consuming its source and clearing all
three scratch registers. Other registers retain their exact prior contents. -/
theorem reverseWord_runs {registers : Nat} (bank : WordBank registers)
    (distinct : Function.Injective bank) (output : Fin (registers + 1))
    (outside : ∀ index, output ≠ bank index) (tokens : Word)
    (values : Store registers) (input : values (bank 0) = wordCode tokens) :
    Runs (reverseWord bank output) values
      (wordStore bank (write values output (wordCode tokens.reverse)) 0 0 0 0) := by
  let prepared := write values output 0
  have prepareRun := clear_runs output values
  have preparedInput : prepared (bank 0) = wordCode tokens := by
    simpa only [prepared, write, Ne.symm (outside 0), ↓reduceIte] using input
  have preparedOutput : prepared output = wordCode [] := by simp only [prepared, write, ↓reduceIte, wordCode]
  obtain ⟨quotient, digit, countdown, loopRun⟩ :=
    reverseLoop_runs bank distinct output outside tokens [] prepared preparedInput preparedOutput
  simp only [List.append_nil, prepared, write_shadow] at loopRun
  let middle := wordStore bank (write values output (wordCode tokens.reverse)) 0 quotient digit countdown
  have cleanup := clearList_runs [bank 1, bank 2, bank 3] middle
  have combined := append_runs prepareRun (append_runs loopRun cleanup)
  have same : (fun register => if register ∈ [bank 1, bank 2, bank 3] then 0 else middle register) =
      wordStore bank (write values output (wordCode tokens.reverse)) 0 0 0 0 := by
    funext current
    by_cases at0 : current = bank 0
    <;> by_cases at1 : current = bank 1
    <;> by_cases at2 : current = bank 2
    <;> by_cases at3 : current = bank 3
    <;> simp_all [middle, wordStore, write, distinct.eq_iff]
  exact same ▸ combined

end Yulang.CommonCanonicalWordReverse
