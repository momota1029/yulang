import Yulang.GeneralDictionaryUniformAlias258
namespace Yulang.GeneralDictionaryDirectView258
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryUniformAlias258 (mapping)
open GeneralDictionaryUniformFill258 (fill)
open GeneralDictionaryLooseIterationBook240 (context)

/-- Direct name-alias compilation uses no historical substitution list.
Its slots and ordinary list still have the size of the original raw state. -/
def view (n : Nat) := GeneralNominalRebaseRawView243.compile (context n).state mapping

theorem raw_exact (n : Nat) (assignment : Assignment) :
 (view n).Models assignment ↔ GeneralNominalState.Models (context n).state (fill assignment) := by
 rw [view,GeneralNominalRebaseRawView243.compile_exact]
 change GeneralNominalState.Models (context n).state (GeneralNominalRebaseRawView243.read mapping assignment) ↔ _
 rw [GeneralDictionaryUniformAlias258.read_exact]

theorem finite_exact (n : Nat) (assignment : Assignment) :
 (view n).Models assignment ↔ (GeneralDictionaryFiveSlot257.view n).Models assignment :=
 (raw_exact n assignment).trans (GeneralDictionaryUniformView258.raw_exact n assignment)

theorem positive_exact (n : Nat) (assignment : Assignment) :
 (view (n+1)).Models assignment ∧ GeneralDictionaryBinderFact257.Holds assignment ↔
 GeneralNominalVersionedJournal232.Models (GeneralDictionaryLooseIterationIteration240.state (n+1)) (fill assignment) := by
 rw [raw_exact,GeneralDictionaryJournalRepair257.exact,GeneralDictionaryUniformView258.binder_exact]

theorem slots (n : Nat) : (view n).slots = n+5 := rfl

theorem ordinary_length (n : Nat) : (view n).ordinary.length = 4+16*n := by
 change (((context n).state.base.ordinary.map _) ++ ((context n).state.ordinary.map _)).length = _
 simp only [List.length_append,List.length_map]
 change 4 + (GeneralDictionaryLooseIterationBook240.atoms n).length = _
 rw [GeneralDictionaryOrdinaryShape257.length_atoms]

theorem public_models (n : Nat) (boundary : Assignment) :
 (∃ assignment, GeneralDictionaryInitialProjection257.Agree assignment boundary ∧
   (view n).Models assignment) ↔
 (∃ assignment, GeneralDictionaryInitialProjection257.Agree assignment boundary ∧
   GeneralNominalState.Models (context n).state assignment) := by
 rw [GeneralDictionaryInitialProjection257.public_models]
 apply exists_congr
 intro assignment
 exact and_congr Iff.rfl (finite_exact n assignment)
end Yulang.GeneralDictionaryDirectView258
