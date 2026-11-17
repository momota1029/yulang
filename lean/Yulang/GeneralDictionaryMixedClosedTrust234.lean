import Yulang.GeneralDictionaryMixedClosedSnapshot234
import Yulang.GeneralNominalVersionedMixedObservations233
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryMixedClosedTrust234
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralNominalVersionedSupport233
open CommonNominalFullCarrier
open GeneralDictionaryMixedClosedBase234

 theorem first_readback : Readback installed [] GeneralDictionaryOptionalInstall229.plan := by
  intro slot member test observation head model valid
  exact GeneralCanonicalObservations.recorded_sound snapshot model valid.1
    (GeneralNominalSupport.head_recorded head)

 theorem first_trusted : Trusted installed [.input GeneralDictionaryOptionalInstall229.plan] :=
  .input _ .source (List.mem_cons_of_mem _ (List.mem_cons_self ..)) first_readback

 theorem old_upper {model : GeneralNominalCommonBridge.Assignment}
    (valid : SliceModels installed [.input GeneralDictionaryOptionalInstall229.plan] model) :
    Equivalent (model oldHi).1 .emptyRecord := by
  have input := valid.2.2 (.input GeneralDictionaryOptionalInstall229.plan) (List.mem_cons_self ..)
  have merges := input.1.2.1
  rw [GeneralDictionaryOptionalInstall229.bindings_exact] at merges
  change PresenceNormalForm.All CommonNominalFullCarrier.model model
    ((GeneralNominalAllocation.equations _ (.union (.var 4) (.var 4)) ++
      GeneralNominalAllocation.equations oldHi (.inter (.var 2) (.var 2))) ++ _) at merges
  have upper := (GeneralNominalCaptureMerges.equations_exact ..).mp
    ((PresenceNormalForm.all_append ..).mp ((PresenceNormalForm.all_append ..).mp merges).1).2
  change Equivalent (model oldHi).1 (.inter (model 2).1 (model 2).1) at upper
  have width := valid.1.1.2.1 (2 : Fin 5) .emptyRecord rfl
  have meet : Equivalent (.inter (model 2).1 (model 2).1) (model 2).1 :=
    ⟨((common_inter_is_meet ..).mp (subtype_refl _)).1,
      (common_inter_is_meet ..).mpr ⟨subtype_refl _,subtype_refl _⟩⟩
  exact ⟨subtype_trans upper.1 (subtype_trans meet.1 width.1),
    subtype_trans width.2 (subtype_trans meet.2 upper.2)⟩

 theorem justified (slot : Fin 8) (high : 5 ≤ slot.val) :
    ∃ facts, Trusted installed facts ∧ ∀ m, SliceModels installed facts m →
      Equivalent (m (source slot)).1 .emptyRecord := by
  have cases : slot = 5 ∨ slot = 6 ∨ slot = 7 := by have bound := slot.isLt; omega
  rcases cases with rfl | rfl | rfl
  · exact ⟨_,first_trusted,fun _ valid => old_upper valid⟩
  · exact ⟨_,GeneralDictionaryVersionedTrusted233.input_trusted,
      fun _ valid => (GeneralDictionaryVersionedTrusted233.aggregates valid).1⟩
  · exact ⟨_,GeneralDictionaryVersionedTrusted233.input_trusted,
      fun _ valid => (GeneralDictionaryVersionedTrusted233.aggregates valid).2⟩

 theorem supported (slot : Fin 8) : source slot ∈
    GeneralNominalState.sources installed.core.erased.current.context.state := by
  revert slot
  decide +kernel
end Yulang.GeneralDictionaryMixedClosedTrust234
