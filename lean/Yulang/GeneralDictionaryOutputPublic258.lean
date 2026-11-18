import Yulang.GeneralDictionaryOutputEvidence258
namespace Yulang.GeneralDictionaryOutputPublic258
open GeneralDictionaryOutputDepth252
open GeneralDictionaryOutputFrame258 (complete)
open GeneralNominalCommonBridge (Assignment)

def Agree (first last : Assignment) : Prop :=
 (∀ name, name ≠ 3 → first name = last name) ∧ (∀ name, (first name).2 = (last name).2)

theorem completion_agrees (assignment : Assignment) : Agree (complete assignment) assignment :=
 ⟨GeneralDictionaryOutputFrame258.outside assignment,GeneralDictionaryOutputFrame258.rows assignment⟩

theorem source_agree (first last : Assignment) (same : Agree first last) :
 GeneralNominalState.Models snapshot first ↔ GeneralNominalState.Models snapshot last :=
 GeneralDictionaryOutputFrame258.source_iff first last same.2
   (fun name small => congrArg Prod.fst (same.1 name (by omega)))

theorem installed_initial (assignment : Assignment)
 (valid : GeneralNominalVersionedJournal232.Models GeneralDictionaryOutputDepthInstall252.installed assignment) :
 GeneralNominalState.Models snapshot assignment :=
 (valid.2.1 plan List.mem_cons_self).1

theorem installed_exact (assignment : Assignment) :
 GeneralNominalVersionedJournal232.Models GeneralDictionaryOutputDepthInstall252.installed (complete assignment) ↔
 GeneralNominalState.Models snapshot assignment := by
 constructor
 · intro valid
   exact (GeneralDictionaryOutputFrame258.source_exact assignment).mp (installed_initial _ valid)
 · exact GeneralDictionaryOutputCompletion258.installed_models assignment

/-- Exact existential model extension for the actual checked installation:
only the designated requested output3 is released; every row is retained. -/
theorem public_models (boundary : Assignment) :
 (∃ assignment, Agree assignment boundary ∧
 GeneralNominalVersionedJournal232.Models GeneralDictionaryOutputDepthInstall252.installed assignment) ↔
 GeneralNominalState.Models snapshot boundary := by
 constructor
 · rintro ⟨assignment,same,valid⟩
   exact (source_agree assignment boundary same).mp (installed_initial assignment valid)
 · intro source
   exact ⟨complete boundary,completion_agrees boundary,
     GeneralDictionaryOutputCompletion258.installed_models boundary source⟩
end Yulang.GeneralDictionaryOutputPublic258
