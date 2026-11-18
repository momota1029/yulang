import Yulang.GeneralDictionarySearchCost258
namespace Yulang.GeneralDictionaryFastFill258
open GeneralNominalCommonBridge (Assignment)

def lower (name : Nat) : Bool := if name ≤ 4 then false else GeneralDictionaryEarlySearch258.fastLower name
def upper (name : Nat) : Bool := if name ≤ 4 then false else GeneralDictionaryEarlySearch258.fastUpper name

theorem lower_exact (name : Nat) : lower name = GeneralDictionaryFamilyRecognition258.isLower name := by
 by_cases small : name ≤ 4
 · simp only [lower,small,ite_true,(GeneralDictionaryFamilyRecognition258.small name small).1]
 · simp only [lower,small,ite_false,GeneralDictionaryEarlySearch258.lower_refines]

theorem upper_exact (name : Nat) : upper name = GeneralDictionaryFamilyRecognition258.isUpper name := by
 by_cases small : name ≤ 4
 · simp only [upper,small,ite_true,(GeneralDictionaryFamilyRecognition258.small name small).2]
 · simp only [upper,small,ite_false,GeneralDictionaryEarlySearch258.upper_refines]

def fill (assignment : Assignment) (name : Nat) :=
 if lower name = true then ((assignment 2).1,(assignment name).2)
 else if upper name = true then ((assignment 4).1,(assignment name).2)
 else assignment name

theorem fill_exact (assignment : Assignment) : fill assignment = GeneralDictionaryUniformFill258.fill assignment := by
 funext name
 simp only [fill,lower_exact,upper_exact,GeneralDictionaryUniformFill258.fill]

def complete (assignment : Assignment) := fill (GeneralDictionaryInitialFill258.bind assignment)

theorem complete_exact (assignment : Assignment) : complete assignment = GeneralDictionaryInitialFill258.complete assignment :=
 fill_exact _

theorem all_stages (assignment : Assignment) :
 (∀ n, GeneralNominalVersionedJournal232.Models (GeneralDictionaryLooseIterationIteration240.state n) (complete assignment)) ↔
 GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot assignment := by
 rw [complete_exact]
 exact GeneralDictionaryInitialFill258.all_stages assignment

theorem public_agrees (assignment : Assignment) : GeneralDictionaryInitialProjection257.Agree (complete assignment) assignment := by
 rw [complete_exact]
 exact GeneralDictionaryInitialFill258.public_agrees assignment

theorem idempotent (assignment : Assignment) : fill (fill assignment) = fill assignment := by
 simp only [fill_exact,GeneralDictionaryUniformFill258.idempotent]
end Yulang.GeneralDictionaryFastFill258
