import Yulang.CanonicalRegisterWords
import Yulang.CommonCanonicalSerialization

/-! The finite-word counter routines operate on the actual syntax serializer. -/

namespace Yulang.CommonCanonicalWordPrograms

open CanonicalRegisterMachine
open CanonicalRegisterMachine.Routine
open CommonCanonicalSerialization

theorem wordPop_token {registers : Nat} (bank : WordBank registers)
    (distinct : Function.Injective bank) (values : Store registers)
    (token : Token) (rest : Word) (input : values (bank 0) = wordCode (token :: rest)) :
    Runs (wordPop bank) values
      (wordStore bank values (wordCode rest) 0 token.digit (63 - token.digit)) := by
  have bounds : 0 < token.digit ∧ token.digit < 64 := by cases token <;> decide
  have encoded : values (bank 0) = token.digit + 64 * wordCode rest := input
  have quotient : values (bank 0) / 64 = wordCode rest := by omega
  have remainder : values (bank 0) % 64 = token.digit := by omega
  have execution := wordPop_runs bank distinct values
  rw [quotient, remainder] at execution
  exact execution

def emit {registers : Nat} (word temporary : Fin (registers + 1)) : Word → Routine registers
  | [] => clear temporary
  | token :: rest => append (pushDigit 64 token.digit word temporary) (emit word temporary rest)

/-- Streaming tokens into a least-significant-digit word reverses their
order. This is the exact accumulator convention used by the interface builder. -/
theorem emit_runs {registers : Nat} (word temporary : Fin (registers + 1))
    (distinct : word ≠ temporary) (tokens prior : Word) (values : Store registers)
    (input : values word = wordCode prior) :
    Runs (emit word temporary tokens) values
      (write (write values word (wordCode (tokens.reverse ++ prior))) temporary 0) := by
  induction tokens generalizing prior values with
  | nil =>
      have same : write values word (wordCode prior) = values := by
        rw [← input]
        funext current
        by_cases equal : current = word
        · subst current
          simp only [write, ↓reduceIte]
        · simp only [write, equal, ↓reduceIte]
      simpa only [emit, List.reverse_nil, List.nil_append, same] using clear_runs temporary values
  | cons token rest ih =>
      let pushed := write (write values word (64 * values word + token.digit)) temporary 0
      have pushedInput : pushed word = wordCode (token :: prior) := by
        simp only [pushed, write, distinct, ↓reduceIte, wordCode, input]
        omega
      have afterPush := ih (token :: prior) pushed pushedInput
      have combined := append_runs (pushDigit_runs 64 token.digit word temporary distinct values) afterPush
      have tokenOrder : rest.reverse ++ token :: prior = (token :: rest).reverse ++ prior := by
        simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      have same : write (write pushed word (wordCode (rest.reverse ++ token :: prior))) temporary 0 =
          write (write values word (wordCode ((token :: rest).reverse ++ prior))) temporary 0 := by
        rw [tokenOrder]
        funext current
        by_cases atWord : current = word
        · subst current
          simp only [write, distinct, ↓reduceIte]
        · by_cases atTemporary : current = temporary
          · subst current
            simp only [write, ↓reduceIte]
          · simp only [write, pushed, atWord, atTemporary, ↓reduceIte]
      exact same ▸ combined

def repeatTokens (tokens : Word) : Nat → Word
  | 0 => []
  | count + 1 => tokens ++ repeatTokens tokens count

def repeatEmit {registers : Nat} (counter word temporary : Fin (registers + 1))
    (tokens : Word) : Routine registers :=
  append (clear temporary) (loop counter (emit word temporary tokens))

/-- Emit a fixed token template a number of times supplied at runtime in a
counter. Both the consumed count and temporary end at zero. -/
theorem repeatEmit_runs {registers : Nat} (counter word temporary : Fin (registers + 1))
    (counterWord : counter ≠ word) (counterTemporary : counter ≠ temporary)
    (wordTemporary : word ≠ temporary) (tokens prior : Word) (values : Store registers)
    (input : values word = wordCode prior) :
    Runs (repeatEmit counter word temporary tokens) values
      (write (write (write values counter 0)
        word (wordCode ((repeatTokens tokens (values counter)).reverse ++ prior))) temporary 0) := by
  have runLoop (count : Nat) (prior : Word) (values : Store registers)
      (countEq : values counter = count) (input : values word = wordCode prior)
      (temporaryEq : values temporary = 0) :
      LoopRuns counter (emit word temporary tokens) values
        (write (write (write values counter 0)
          word (wordCode ((repeatTokens tokens count).reverse ++ prior))) temporary 0) := by
    induction count generalizing prior values with
    | zero =>
        have same : write (write (write values counter 0)
            word (wordCode ((repeatTokens tokens 0).reverse ++ prior))) temporary 0 = values := by
          funext current
          by_cases atCounter : current = counter
          <;> by_cases atWord : current = word
          <;> by_cases atTemporary : current = temporary
          <;> simp_all [repeatTokens, write]
        rw [same]
        exact .done countEq
    | succ count ih =>
        let lower := write values counter count
        let after := write (write lower word (wordCode (tokens.reverse ++ prior))) temporary 0
        have lowerInput : lower word = wordCode prior := by
          simp only [lower, write, Ne.symm counterWord, ↓reduceIte, input]
        have body := emit_runs word temporary wordTemporary tokens prior lower lowerInput
        have afterCount : after counter = count := by
          simp only [after, lower, write, counterTemporary, counterWord, ↓reduceIte]
        have afterInput : after word = wordCode (tokens.reverse ++ prior) := by
          simp only [after, write, wordTemporary, ↓reduceIte]
        have afterTemporary : after temporary = 0 := by simp only [after, write, ↓reduceIte]
        have rest := ih (tokens.reverse ++ prior) after afterCount afterInput afterTemporary
        have order : (repeatTokens tokens count).reverse ++ (tokens.reverse ++ prior) =
            (repeatTokens tokens (count + 1)).reverse ++ prior := by
          simp only [repeatTokens, List.reverse_append, List.append_assoc]
        have same : write (write (write after counter 0)
              word (wordCode ((repeatTokens tokens count).reverse ++ (tokens.reverse ++ prior)))) temporary 0 =
            write (write (write values counter 0)
              word (wordCode ((repeatTokens tokens (count + 1)).reverse ++ prior))) temporary 0 := by
          rw [order]
          funext current
          by_cases atCounter : current = counter
          <;> by_cases atWord : current = word
          <;> by_cases atTemporary : current = temporary
          <;> simp_all [after, lower, write]
        rw [same] at rest
        have lowerEq : write values counter (values counter - 1) = lower := by
          simp only [countEq, Nat.add_sub_cancel, lower]
        have bodyCorrect : Runs (emit word temporary tokens)
            (write values counter (values counter - 1)) after := by
          rw [lowerEq]
          exact body
        exact .next (by omega) bodyCorrect rest
  let prepared := write values temporary 0
  have countEq : prepared counter = values counter := by
    simp only [prepared, write, counterTemporary, ↓reduceIte]
  have preparedInput : prepared word = wordCode prior := by
    simp only [prepared, write, wordTemporary, ↓reduceIte, input]
  have preparedTemporary : prepared temporary = 0 := by simp only [prepared, write, ↓reduceIte]
  have loopRun := loop_runs (runLoop (values counter) prior prepared countEq preparedInput preparedTemporary)
  have combined := append_runs (clear_runs temporary values) loopRun
  have same : write (write (write prepared counter 0)
        word (wordCode ((repeatTokens tokens (values counter)).reverse ++ prior))) temporary 0 =
      write (write (write values counter 0)
        word (wordCode ((repeatTokens tokens (values counter)).reverse ++ prior))) temporary 0 := by
    funext current
    by_cases atCounter : current = counter
    <;> by_cases atWord : current = word
    <;> by_cases atTemporary : current = temporary
    <;> simp_all [prepared, write]
  exact same ▸ combined

def emitNatural {registers : Nat} (bank : WordBank registers) : Routine registers :=
  append (copy (bank 1) (bank 2) (bank 3))
    (append (repeatEmit (bank 2) (bank 0) (bank 3) [.natSucc])
      (emit (bank 0) (bank 3) [.natZero]))

/-- Emit a unary-terminated natural field whose value is supplied at runtime
in bank register one. That source value and every outside register survive. -/
theorem emitNatural_runs {registers : Nat} (bank : WordBank registers)
    (distinct : Function.Injective bank) (prior : Word) (values : Store registers)
    (input : values (bank 0) = wordCode prior) :
    Runs (emitNatural bank) values
      (write (write (write values (bank 0)
        (wordCode ((natural (values (bank 1))).reverse ++ prior))) (bank 2) 0) (bank 3) 0) := by
  have naturalTemplate (count : Nat) : repeatTokens [.natSucc] count ++ [.natZero] = natural count := by
    induction count with
    | zero => rfl
    | succ count ih =>
        simpa only [repeatTokens, natural, List.singleton_append, List.cons_append, List.nil_append] using
          congrArg (List.cons Token.natSucc) ih
  let first := write (write values (bank 2) (values (bank 1))) (bank 3) 0
  have copyRun := copy_runs (bank 1) (bank 2) (bank 3)
    (by simp [distinct.eq_iff]) (by simp [distinct.eq_iff]) (by simp [distinct.eq_iff]) values
  have firstInput : first (bank 0) = wordCode prior := by
    simpa only [first, write, distinct.eq_iff, Fin.isValue, Fin.reduceEq, ↓reduceIte] using input
  have firstCount : first (bank 2) = values (bank 1) := by simp [first, write, distinct.eq_iff]
  have repeatRun := repeatEmit_runs (bank 2) (bank 0) (bank 3)
    (by simp [distinct.eq_iff]) (by simp [distinct.eq_iff]) (by simp [distinct.eq_iff])
    [.natSucc] prior first firstInput
  rw [firstCount] at repeatRun
  let repeatedWord := (repeatTokens [.natSucc] (values (bank 1))).reverse ++ prior
  let second := write (write (write first (bank 2) 0) (bank 0) (wordCode repeatedWord)) (bank 3) 0
  have secondInput : second (bank 0) = wordCode repeatedWord := by
    simp [second, write, distinct.eq_iff]
  have lastRun := emit_runs (bank 0) (bank 3) (by simp [distinct.eq_iff])
    [.natZero] repeatedWord second secondInput
  have combined := append_runs copyRun (append_runs repeatRun lastRun)
  have order : [.natZero].reverse ++ repeatedWord = (natural (values (bank 1))).reverse ++ prior := by
    rw [← naturalTemplate]
    simp only [repeatedWord, List.reverse_append, List.append_assoc]
  have same : write (write second (bank 0) (wordCode ([.natZero].reverse ++ repeatedWord))) (bank 3) 0 =
      write (write (write values (bank 0)
        (wordCode ((natural (values (bank 1))).reverse ++ prior))) (bank 2) 0) (bank 3) 0 := by
    rw [order]
    funext current
    by_cases at0 : current = bank 0
    <;> by_cases at1 : current = bank 1
    <;> by_cases at2 : current = bank 2
    <;> by_cases at3 : current = bank 3
    <;> simp_all [second, first, write, distinct.eq_iff]
  exact same ▸ combined

def readNaturalToken {registers : Nat} (bank : WordBank registers) : Routine registers :=
  append (wordPop bank) (atomic (.decrement (bank 2) () ()))

/-- Read a token and subtract one from its digit. In a natural field this
turns the terminator into zero and each successor token into one. -/
theorem readNaturalToken_runs {registers : Nat} (bank : WordBank registers)
    (distinct : Function.Injective bank) (values : Store registers)
    (token : Token) (rest : Word) (input : values (bank 0) = wordCode (token :: rest)) :
    Runs (readNaturalToken bank) values
      (wordStore bank values (wordCode rest) 0 (token.digit - 1) (63 - token.digit)) := by
  have positive : token.digit ≠ 0 := by cases token <;> decide
  let popped := wordStore bank values (wordCode rest) 0 token.digit (63 - token.digit)
  have popRun := wordPop_token bank distinct values token rest input
  have decRun := atomic_runs (.decrement (bank 2) () ()) popped
  have poppedDigit : popped (bank 2) = token.digit := by
    simp [popped, wordStore, write, distinct.eq_iff]
  have combined := append_runs popRun decRun
  have same : (Op.eval popped (.decrement (bank 2) () ())).2 =
      wordStore bank values (wordCode rest) 0 (token.digit - 1) (63 - token.digit) := by
    simp only [Op.eval, poppedDigit, positive, ↓reduceIte]
    funext current
    by_cases at0 : current = bank 0
    <;> by_cases at1 : current = bank 1
    <;> by_cases at2 : current = bank 2
    <;> by_cases at3 : current = bank 3
    <;> simp_all [popped, wordStore, write, distinct.eq_iff]
  exact same ▸ combined

def readNaturalBody {registers : Nat} (bank : WordBank registers)
    (output : Fin (registers + 1)) : Routine registers :=
  append (increment output) (readNaturalToken bank)

def readNaturalLoop {registers : Nat} (bank : WordBank registers)
    (output : Fin (registers + 1)) : Routine registers :=
  loop (bank 2) (readNaturalBody bank output)

/-- After a successor flag has been read, the loop consumes the remaining
unary field and adds its value plus that first successor to the accumulator. -/
theorem readNaturalLoop_runs {registers : Nat} (bank : WordBank registers)
    (distinct : Function.Injective bank) (output : Fin (registers + 1))
    (outside : ∀ index, output ≠ bank index) (count : Nat) (rest : Word)
    (values : Store registers) (input : values (bank 0) = wordCode (natural count ++ rest))
    (flag : values (bank 2) = 1) :
    Runs (readNaturalLoop bank output) values
      (wordStore bank (write values output (values output + count + 1)) (wordCode rest) 0 0 62) := by
  have bodyExecution (token : Token) (tail : Word) (values : Store registers)
      (input : values (bank 0) = wordCode (token :: tail)) (flag : values (bank 2) = 1) :
      Runs (readNaturalBody bank output) (write values (bank 2) (values (bank 2) - 1))
        (wordStore bank (write values output (values output + 1))
          (wordCode tail) 0 (token.digit - 1) (63 - token.digit)) := by
    let lower := write values (bank 2) 0
    let increased := write lower output (values output + 1)
    have lowerOutput : lower output = values output := by simp only [lower, write, outside 2, ↓reduceIte]
    have incRun := atomic_runs (.increment output ()) lower
    simp only [Op.eval, lowerOutput] at incRun
    have increasedInput : increased (bank 0) = wordCode (token :: tail) := by
      simpa only [increased, lower, write, Ne.symm (outside 0), distinct.eq_iff,
        Fin.isValue, Fin.reduceEq, ↓reduceIte] using input
    have readRun := readNaturalToken_runs bank distinct increased token tail increasedInput
    have combined := append_runs incRun readRun
    have same : wordStore bank increased (wordCode tail) 0 (token.digit - 1) (63 - token.digit) =
        wordStore bank (write values output (values output + 1))
          (wordCode tail) 0 (token.digit - 1) (63 - token.digit) := by
      funext current
      by_cases at0 : current = bank 0
      <;> by_cases at1 : current = bank 1
      <;> by_cases at2 : current = bank 2
      <;> by_cases at3 : current = bank 3
      <;> simp_all [increased, lower, wordStore, write, distinct.eq_iff]
    have lowerEq : write values (bank 2) (values (bank 2) - 1) = lower := by
      simp only [flag, Nat.sub_self, lower]
    rw [lowerEq]
    exact same ▸ combined
  apply loop_runs
  induction count generalizing values with
  | zero =>
      have encoded : values (bank 0) = wordCode (.natZero :: rest) := by
        simpa only [natural, List.singleton_append] using input
      have body := bodyExecution .natZero rest values encoded flag
      simp only [Token.digit, Nat.sub_self, Nat.reduceSub] at body
      apply LoopRuns.next (by omega) body
      simpa only [Nat.add_zero] using
        (LoopRuns.done (register := bank 2) (body := readNaturalBody bank output)
          (values := wordStore bank (write values output (values output + 1)) (wordCode rest) 0 0 62)
          (by simp [wordStore, write, distinct.eq_iff]))
  | succ count ih =>
      have encoded : values (bank 0) = wordCode (.natSucc :: (natural count ++ rest)) := by
        simpa only [natural, List.cons_append] using input
      have body := bodyExecution .natSucc (natural count ++ rest) values encoded flag
      simp only [Token.digit, Nat.reduceSub] at body
      let middle := wordStore bank (write values output (values output + 1))
        (wordCode (natural count ++ rest)) 0 1 61
      have middleInput : middle (bank 0) = wordCode (natural count ++ rest) := by
        simp [middle, wordStore, write, distinct.eq_iff]
      have middleFlag : middle (bank 2) = 1 := by simp [middle, wordStore, write, distinct.eq_iff]
      have middleOutput : middle output = values output + 1 := by
        simp only [middle, wordStore, write, outside, ↓reduceIte]
      have remaining := ih middle middleInput middleFlag
      have same : wordStore bank (write middle output (middle output + count + 1)) (wordCode rest) 0 0 62 =
          wordStore bank (write values output (values output + (count + 1) + 1)) (wordCode rest) 0 0 62 := by
        rw [middleOutput]
        have addition : values output + 1 + count + 1 = values output + (count + 1) + 1 := by omega
        rw [addition]
        funext current
        by_cases at0 : current = bank 0
        <;> by_cases at1 : current = bank 1
        <;> by_cases at2 : current = bank 2
        <;> by_cases at3 : current = bank 3
        <;> by_cases atOutput : current = output
        <;> simp_all [middle, wordStore, write, distinct.eq_iff]
      rw [same] at remaining
      exact .next (by omega) body remaining

def readNatural {registers : Nat} (bank : WordBank registers)
    (output : Fin (registers + 1)) : Routine registers :=
  append (clear output) (append (readNaturalToken bank) (readNaturalLoop bank output))

/-- Decode the actual unary-terminated serializer, including its exact
unconsumed suffix. All prior output and scratch contents may be arbitrary. -/
theorem readNatural_runs {registers : Nat} (bank : WordBank registers)
    (distinct : Function.Injective bank) (output : Fin (registers + 1))
    (outside : ∀ index, output ≠ bank index) (count : Nat) (rest : Word)
    (values : Store registers) (input : values (bank 0) = wordCode (natural count ++ rest)) :
    Runs (readNatural bank output) values
      (wordStore bank (write values output count) (wordCode rest) 0 0 62) := by
  let prepared := write values output 0
  have firstRun := clear_runs output values
  have preparedInput : prepared (bank 0) = wordCode (natural count ++ rest) := by
    simpa only [prepared, write, Ne.symm (outside 0), ↓reduceIte] using input
  cases count with
  | zero =>
      have encoded : prepared (bank 0) = wordCode (.natZero :: rest) := by
        simpa only [natural, List.singleton_append] using preparedInput
      have tokenRun := readNaturalToken_runs bank distinct prepared .natZero rest encoded
      simp only [Token.digit, Nat.sub_self, Nat.reduceSub] at tokenRun
      have loopRun : Runs (readNaturalLoop bank output)
          (wordStore bank prepared (wordCode rest) 0 0 62)
          (wordStore bank prepared (wordCode rest) 0 0 62) :=
        loop_runs (.done (by simp [wordStore, write, distinct.eq_iff]))
      exact append_runs firstRun (append_runs tokenRun loopRun)
  | succ count =>
      have encoded : prepared (bank 0) = wordCode (.natSucc :: (natural count ++ rest)) := by
        simpa only [natural, List.cons_append] using preparedInput
      have tokenRun := readNaturalToken_runs bank distinct prepared .natSucc (natural count ++ rest) encoded
      simp only [Token.digit, Nat.reduceSub] at tokenRun
      let middle := wordStore bank prepared (wordCode (natural count ++ rest)) 0 1 61
      have middleInput : middle (bank 0) = wordCode (natural count ++ rest) := by
        simp [middle, wordStore, write, distinct.eq_iff]
      have middleFlag : middle (bank 2) = 1 := by simp [middle, wordStore, write, distinct.eq_iff]
      have middleOutput : middle output = 0 := by simp only [middle, prepared, wordStore, write, outside, ↓reduceIte]
      have loopRun := readNaturalLoop_runs bank distinct output outside count rest middle middleInput middleFlag
      have combined := append_runs firstRun (append_runs tokenRun loopRun)
      have same : wordStore bank (write middle output (middle output + count + 1)) (wordCode rest) 0 0 62 =
          wordStore bank (write values output (count + 1)) (wordCode rest) 0 0 62 := by
        rw [middleOutput, Nat.zero_add]
        funext current
        by_cases at0 : current = bank 0
        <;> by_cases at1 : current = bank 1
        <;> by_cases at2 : current = bank 2
        <;> by_cases at3 : current = bank 3
        <;> by_cases atOutput : current = output
        <;> simp_all [middle, prepared, wordStore, write, distinct.eq_iff]
      exact same ▸ combined

end Yulang.CommonCanonicalWordPrograms
