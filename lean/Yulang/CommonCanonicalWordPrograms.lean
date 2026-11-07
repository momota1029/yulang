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

end Yulang.CommonCanonicalWordPrograms
