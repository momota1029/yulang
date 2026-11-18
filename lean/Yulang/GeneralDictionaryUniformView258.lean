import Yulang.GeneralDictionaryUniformBlock258
namespace Yulang.GeneralDictionaryUniformView258
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryUniformFill258 (fill)
open GeneralDictionaryFiveSlot257 (view)
open GeneralNominalViewSupport249 (support)

theorem support_small (n name : Nat) (present : name ∈ support (view n)) : name ≤ 4 := by
 rcases GeneralDictionaryFiniteView257.two_views n with initial | positive
 · rw [initial] at present
   have all : ∀ name ∈ support (view 0), name ≤ 4 := by decide
   exact all name present
 · rw [positive] at present
   have all : ∀ name ∈ support (view 1), name ≤ 4 := by decide
   exact all name present

theorem view_exact (n : Nat) (assignment : Assignment) :
 (view n).Models (fill assignment) ↔ (view n).Models assignment := by
 apply GeneralNominalViewSupport249.models_iff _ _ _ (GeneralDictionaryUniformFill258.rows assignment)
 intro name present
 exact congrArg Prod.fst (GeneralDictionaryUniformFill258.initial assignment name (support_small n name present))

theorem binder_exact (assignment : Assignment) :
 GeneralDictionaryBinderFact257.Holds (fill assignment) ↔ GeneralDictionaryBinderFact257.Holds assignment := by
 unfold GeneralDictionaryBinderFact257.Holds
 rw [GeneralDictionaryUniformFill258.actual_fixed,GeneralDictionaryUniformFill258.initial assignment 2 (by decide)]

theorem journal_view_exact (n : Nat) (assignment : Assignment) :
 (GeneralDictionaryFiniteJournal257.view n).Models (fill assignment) ↔
 (GeneralDictionaryFiniteJournal257.view n).Models assignment := by
 rw [GeneralDictionaryFiniteJournal257.models_exact,GeneralDictionaryFiniteJournal257.models_exact,
   view_exact,binder_exact]

theorem raw_exact (n : Nat) (assignment : Assignment) :
 GeneralNominalState.Models (GeneralDictionaryLooseIterationBook240.context n).state (fill assignment) ↔
 (view n).Models assignment := by
 rw [← GeneralDictionaryCompactView257.recovered n (fill assignment) (GeneralDictionaryUniformBlock258.all_blocks assignment n)]
 rw [GeneralDictionaryFiveSlot257.models_exact,view_exact]

theorem journal_exact (n : Nat) (assignment : Assignment) :
 GeneralNominalVersionedJournal232.Models (GeneralDictionaryLooseIterationIteration240.state (n+1)) (fill assignment) ↔
 (GeneralDictionaryFiniteJournal257.view 1).Models assignment := by
 rw [GeneralDictionaryJournalRepair257.exact,raw_exact,binder_exact,
   ← GeneralDictionaryFiniteJournal257.models_exact,GeneralDictionaryFiniteJournal257.stable]
end Yulang.GeneralDictionaryUniformView258
