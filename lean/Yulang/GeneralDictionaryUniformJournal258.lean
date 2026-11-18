import Yulang.GeneralDictionaryUniformView258
namespace Yulang.GeneralDictionaryUniformJournal258
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryUniformFill258 (fill)
open GeneralDictionaryLooseIterationIteration240 (state)
open GeneralDictionaryFiniteJournal257 (Agree)
open GeneralNominalVersionedJournal232 (Models)

/-- One fixed reconstruction works at every stage, including the initial one.
The antecedent is the positive finite journal, not the weaker initial journal. -/
theorem all_stages (assignment : Assignment) :
 (∀ n, Models (state n) (fill assignment)) ↔
 (GeneralDictionaryFiniteJournal257.view 1).Models assignment := by
 constructor
 · intro valid
   exact (GeneralDictionaryUniformView258.journal_exact 0 assignment).mp (valid 1)
 · intro small n
   cases n with
   | zero =>
     have full := (GeneralDictionaryUniformView258.journal_exact 0 assignment).mpr small
     have both := (GeneralDictionaryJournalRepair257.exact 0 (fill assignment)).mp full
     exact GeneralDictionaryJournalRepair257.earlier_journal 1 0 (by omega) (fill assignment) both.1 both.2
   | succ n => exact (GeneralDictionaryUniformView258.journal_exact n assignment).mpr small

theorem agree_trans (first middle last : Assignment) (one : Agree first middle) (two : Agree middle last) :
 Agree first last :=
 ⟨fun name kept => (one.1 name kept).trans (two.1 name kept),fun name => (one.2 name).trans (two.2 name)⟩

/-- This exchanges exists-assignment/forall-stage constructively for this
specific family, using one fill function rather than a compactness principle. -/
theorem simultaneous_models (boundary : Assignment) :
 (∃ assignment, Agree assignment boundary ∧ ∀ n, Models (state n) assignment) ↔
 (∃ assignment, Agree assignment boundary ∧ (GeneralDictionaryFiniteJournal257.view 1).Models assignment) := by
 constructor
 · rintro ⟨assignment,same,all⟩
   exact (GeneralDictionaryFiniteJournal257.public_models 0 boundary).mp ⟨assignment,same,all 1⟩
 · rintro ⟨assignment,same,small⟩
   exact ⟨fill assignment,agree_trans _ _ _ (GeneralDictionaryUniformFill258.agrees assignment) same,
     (all_stages assignment).mpr small⟩

theorem positive_models (n : Nat) (boundary : Assignment) :
 (∃ assignment, Agree assignment boundary ∧ Models (state (n+1)) assignment) ↔
 (∃ assignment, Agree assignment boundary ∧ ∀ index, Models (state index) assignment) := by
 rw [simultaneous_models,GeneralDictionaryFiniteJournal257.public_models,
   GeneralDictionaryFiniteJournal257.stable]

theorem recovered (n : Nat) (assignment : Assignment) (valid : Models (state (n+1)) assignment) :
 (GeneralDictionaryFiniteJournal257.view 1).Models assignment := by
 obtain ⟨raw,binder⟩ := (GeneralDictionaryJournalRepair257.exact n assignment).mp valid
 have blockValid : PresenceNormalForm.All CommonNominalFullCarrier.model assignment
   (GeneralPresenceDefinitionRewrite244.block (GeneralDictionaryUpperHistory257.history (n+1))) :=
   fun atom member => raw.2.2 atom (GeneralDictionaryUpperHistory257.block_in_source (n+1) member)
 have compact := (GeneralDictionaryCompactView257.recovered (n+1) assignment blockValid).mpr raw
 have small := (GeneralDictionaryFiveSlot257.models_exact (n+1) assignment).mp compact
 have full := (GeneralDictionaryFiniteJournal257.models_exact (n+1) assignment).mpr ⟨small,binder⟩
 rwa [GeneralDictionaryFiniteJournal257.stable] at full

theorem future (n : Nat) (assignment : Assignment) (valid : Models (state (n+1)) assignment) :
 ∀ index, Models (state index) (fill assignment) :=
 (all_stages assignment).mpr (recovered n assignment valid)
end Yulang.GeneralDictionaryUniformJournal258
