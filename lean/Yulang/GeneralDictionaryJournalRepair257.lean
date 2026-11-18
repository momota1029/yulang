import Yulang.GeneralDictionaryPastPacket257
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryJournalRepair257
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryLooseIterationBook240 (context plan)
open GeneralDictionaryLooseIterationIteration240 (state stages)
open GeneralNominalVersionedJournal232 (Models)

theorem earlier_journal (n index : Nat) (before : index ≤ n) (assignment : Assignment)
 (valid : GeneralNominalState.Models (context n).state assignment)
 (binder : GeneralDictionaryBinderFact257.Holds assignment) : Models (state index) assignment := by
 induction index with
 | zero =>
   apply (GeneralNominalVersionedJournal232.initial_models ..).mpr
   exact ⟨GeneralDictionaryHistoricalValues257.raw_initial n assignment valid,
     fun _ => ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩⟩
 | succ index ih =>
   have prior := ih (by omega)
   have packet := GeneralDictionaryPastPacket257.holds n index (by omega) assignment valid binder
   exact GeneralDictionaryLooseIterationRound240.models_general (stages index).shape
     (stages index).recorded assignment prior packet

/-- For this exact source family the missing journal semantics is repaired by
one fixed binder equality. This is a model theorem, not a new transition rule. -/
theorem exact (n : Nat) (assignment : Assignment) :
 Models (state (n+1)) assignment ↔
 GeneralNominalState.Models (context (n+1)).state assignment ∧
 GeneralDictionaryBinderFact257.Holds assignment := by
 constructor
 · intro valid
   have raw := valid.1.1
   rw [(stages (n+1)).shape.current] at raw
   exact ⟨raw,GeneralDictionaryBinderFact257.journal_requires n assignment valid⟩
 · rintro ⟨raw,binder⟩
   exact earlier_journal (n+1) (n+1) (by omega) assignment raw binder
end Yulang.GeneralDictionaryJournalRepair257
