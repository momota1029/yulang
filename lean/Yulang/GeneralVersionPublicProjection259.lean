import Yulang.GeneralVersionBoundaryCompletion259
namespace Yulang.GeneralVersionPublicProjection259
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryVersionLoopSource237 (snapshot initial)
open GeneralDictionaryVersionLoopIteration239 (state stages)
open GeneralNominalVersionedJournal232 (Models)
open GeneralVersionBoundaryCompletion259 (Agree complete)

theorem initial_exact (assignment : Assignment) : Models initial assignment ↔
 GeneralNominalState.Models snapshot assignment := by
 rw [GeneralNominalVersionedJournal232.initial_models]
 constructor
 · exact And.left
 · intro source; exact ⟨source,fun _ => ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩⟩

theorem source_agree (first last : Assignment) (same : Agree first last) :
 GeneralNominalState.Models snapshot first ↔ GeneralNominalState.Models snapshot last := by
 rw [← initial_exact,← initial_exact]
 apply GeneralNominalVersionedJournalFrame236.models_iff
 intro name member
 have bounded := GeneralDictionaryVersionLoopPatched239.initial_support member
 simp only [List.mem_cons,List.not_mem_nil,or_false] at bounded
 have small : name ≤ 3 := by omega
 exact same.1 name small

theorem model_source (n : Nat) (assignment : Assignment) (valid : Models (state n) assignment) :
 GeneralNominalState.Models snapshot assignment := by
 have source := valid.1.2.1
 rw [(stages n).shape.source] at source
 exact source

theorem stage_models (n : Nat) (boundary : Assignment) :
 (∃ assignment, Agree assignment boundary ∧ Models (state n) assignment) ↔
 GeneralNominalState.Models snapshot boundary := by
 constructor
 · rintro ⟨assignment,same,valid⟩
   exact (source_agree assignment boundary same).mp (model_source n assignment valid)
 · intro source
   exact ⟨complete boundary,GeneralVersionBoundaryCompletion259.agrees boundary,
     GeneralVersionBoundaryCompletion259.all_stages boundary source n⟩

theorem simultaneous_models (boundary : Assignment) :
 (∃ assignment, Agree assignment boundary ∧ ∀ n, Models (state n) assignment) ↔
 GeneralNominalState.Models snapshot boundary := by
 constructor
 · rintro ⟨assignment,same,all⟩; exact (stage_models 0 boundary).mp ⟨assignment,same,all 0⟩
 · intro source
   exact ⟨complete boundary,GeneralVersionBoundaryCompletion259.agrees boundary,
     GeneralVersionBoundaryCompletion259.all_stages boundary source⟩
end Yulang.GeneralVersionPublicProjection259
