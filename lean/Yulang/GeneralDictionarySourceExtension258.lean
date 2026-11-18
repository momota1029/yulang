import Yulang.GeneralDictionaryInitialFill258
namespace Yulang.GeneralDictionarySourceExtension258
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryLooseIterationIteration240 (state stages)
open GeneralDictionaryInitialProjection257 (Agree)
open GeneralDictionaryInitialFill258 (complete)
open GeneralNominalVersionedJournal232 (Models)

theorem view_agree (n : Nat) (first last : Assignment) (same : Agree first last) :
 (GeneralDictionaryFiveSlot257.view n).Models first ↔ (GeneralDictionaryFiveSlot257.view n).Models last := by
 apply GeneralNominalViewSupport249.models_iff _ _ _ same.2
 intro name present
 exact congrArg Prod.fst (same.1 name (GeneralDictionaryUniformView258.support_small n name present))

theorem model_initial (n : Nat) (assignment : Assignment) (valid : Models (state n) assignment) :
 GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot assignment := by
 have raw := valid.1.1
 rw [(stages n).shape.current] at raw
 exact GeneralDictionaryHistoricalValues257.raw_initial n assignment raw

/-- The public source boundary excludes the internally allocated actual binder;
all row values are still fixed. No private binder preservation is asserted. -/
theorem simultaneous_models (boundary : Assignment) :
 (∃ assignment, Agree assignment boundary ∧ ∀ n, Models (state n) assignment) ↔
 GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot boundary := by
 constructor
 · rintro ⟨assignment,same,all⟩
   have source := model_initial 0 assignment (all 0)
   have small := (GeneralDictionaryInitialFill258.raw_initial assignment).mpr source
   have bound := (view_agree 0 assignment boundary same).mp small
   exact (GeneralDictionaryInitialFill258.raw_initial boundary).mp bound
 · intro source
   exact ⟨complete boundary,GeneralDictionaryInitialFill258.public_agrees boundary,
     (GeneralDictionaryInitialFill258.all_stages boundary).mpr source⟩

theorem stage_models (n : Nat) (boundary : Assignment) :
 (∃ assignment, Agree assignment boundary ∧ Models (state n) assignment) ↔
 GeneralNominalState.Models GeneralDictionaryLooseLoopSource240.snapshot boundary := by
 constructor
 · rintro ⟨assignment,same,valid⟩
   have small := (GeneralDictionaryInitialFill258.raw_initial assignment).mpr (model_initial n assignment valid)
   exact (GeneralDictionaryInitialFill258.raw_initial boundary).mp ((view_agree 0 assignment boundary same).mp small)
 · intro source
   exact ⟨complete boundary,GeneralDictionaryInitialFill258.public_agrees boundary,
     (GeneralDictionaryInitialFill258.all_stages boundary).mpr source n⟩

theorem exchange (boundary : Assignment) :
 (∀ n, ∃ assignment, Agree assignment boundary ∧ Models (state n) assignment) ↔
 (∃ assignment, Agree assignment boundary ∧ ∀ n, Models (state n) assignment) := by
 rw [simultaneous_models]
 constructor
 · intro stages; exact (stage_models 0 boundary).mp (stages 0)
 · intro source n; exact (stage_models n boundary).mpr source
end Yulang.GeneralDictionarySourceExtension258
