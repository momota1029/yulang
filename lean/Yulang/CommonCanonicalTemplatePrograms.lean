import Yulang.CommonCanonicalRangeEmitters

/-! A finite template language compiled to the actual counter routines.
The evaluator specifies emitted words; it is not an instruction of the VM. -/

namespace Yulang.CommonCanonicalTemplatePrograms

open CanonicalRegisterMachine
open CanonicalRegisterMachine.Routine
open CommonCanonicalSerialization
open CommonCanonicalEmitters
open CommonCanonicalWordPrograms
open CommonCanonicalRangeEmitters

def fourBank {registers : Nat} (a b c d : Fin (registers + 1)) : WordBank registers :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

theorem fourBank_injective {registers : Nat} (a b c d : Fin (registers + 1))
    (ab : a ≠ b) (ac : a ≠ c) (ad : a ≠ d) (bc : b ≠ c) (bd : b ≠ d) (cd : c ≠ d) :
    Function.Injective (fourBank a b c d) := by
  have cases (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  intro i j same
  rcases cases i with rfl | rfl | rfl | rfl <;>
    rcases cases j with rfl | rfl | rfl | rfl <;>
    first | rfl
          | exact False.elim (ab same) | exact False.elim (ab same.symm)
          | exact False.elim (ac same) | exact False.elim (ac same.symm)
          | exact False.elim (ad same) | exact False.elim (ad same.symm)
          | exact False.elim (bc same) | exact False.elim (bc same.symm)
          | exact False.elim (bd same) | exact False.elim (bd same.symm)
          | exact False.elim (cd same) | exact False.elim (cd same.symm)

structure Context (registers parameters : Nat) where
  inputs : Fin parameters → Fin (registers + 1)
  output : Fin (registers + 1)
  work : WordBank registers
  distinct : Function.Injective work
  outputOutside : ∀ index, output ≠ work index
  inputsOutside : ∀ parameter index, inputs parameter ≠ work index
  inputsOutput : ∀ parameter, inputs parameter ≠ output

def Context.naturalBank {registers parameters : Nat} (context : Context registers parameters)
    (source : Fin parameters) : WordBank registers :=
  fourBank context.output (context.inputs source) (context.work 0) (context.work 1)

inductive Template (parameters : Nat) where
  | literal (tokens : Word)
  | number (source : Fin parameters)
  | sum (first last : Fin parameters)
  | copies (source : Fin parameters) (tokens : Word)
  | append (first last : Template parameters)
  | choose (first last : Fin parameters) (equal different : Template parameters)

def Template.tokens {parameters : Nat} : Template parameters → Environment parameters → Word
  | .literal word, _ => word
  | .number source, environment => natural (environment source)
  | .sum first last, environment => natural (environment first + environment last)
  | .copies source word, environment => repeatTokens word (environment source)
  | .append first last, environment => first.tokens environment ++ last.tokens environment
  | .choose first last equal different, environment =>
      if environment first = environment last then equal.tokens environment else different.tokens environment

def Template.compile {registers parameters : Nat} (context : Context registers parameters) :
    Template parameters → Routine registers
  | .literal word => emit context.output (context.work 1) word
  | .number source => emitNatural (context.naturalBank source)
  | .sum first last => emitSum (context.naturalBank last) (context.inputs first)
  | .copies source word => repeatLiteral (context.naturalBank source) word
  | .append first last => Routine.append (first.compile context) (last.compile context)
  | .choose first last equal different => chooseEqual context.work (context.inputs first) (context.inputs last)
      (equal.compile context) (different.compile context)

/-- Every finite template has an actual finite counter routine with the
specified word output and preservation of its entire readonly roster. -/
theorem template_emits {registers parameters : Nat} (context : Context registers parameters)
    (template : Template parameters) :
    Emits (template.compile context) context.inputs context.output template.tokens := by
  have bankInjective (source : Fin parameters) : Function.Injective (context.naturalBank source) := by
    apply fourBank_injective
    · exact Ne.symm (context.inputsOutput source)
    · exact context.outputOutside 0
    · exact context.outputOutside 1
    · exact context.inputsOutside source 0
    · exact context.inputsOutside source 1
    · exact fun same => (by decide : (0 : Fin 4) ≠ 1) (context.distinct same)
  have bankSeparated (source index : Fin parameters) :
      context.inputs index ≠ context.naturalBank source 0 ∧
      context.inputs index ≠ context.naturalBank source 2 ∧
      context.inputs index ≠ context.naturalBank source 3 :=
    ⟨context.inputsOutput index, context.inputsOutside index 0, context.inputsOutside index 1⟩
  induction template with
  | literal word =>
      exact emits_literal context.inputs context.output (context.work 1) (context.outputOutside 1)
        (fun index => ⟨context.inputsOutput index, context.inputsOutside index 1⟩) word
  | number source =>
      exact emits_natural (context.naturalBank source) (bankInjective source) context.inputs source rfl
        (bankSeparated source)
  | sum first last =>
      exact emits_sum (context.naturalBank last) (bankInjective last) context.inputs first last rfl
        (bankSeparated last)
  | copies source word =>
      exact emits_repeat_literal (context.naturalBank source) (bankInjective source) context.inputs source rfl
        (bankSeparated source) word
  | append first last firstCorrect lastCorrect =>
      exact emits_append firstCorrect lastCorrect
  | choose first last equal different equalCorrect differentCorrect =>
      exact emits_choose_equal context.work context.distinct context.inputs context.output
        context.outputOutside context.inputsOutside first last equalCorrect differentCorrect

end Yulang.CommonCanonicalTemplatePrograms
