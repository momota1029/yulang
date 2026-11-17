import Yulang.GeneralDictionaryVersionedSecondSelected233
import Yulang.GeneralNominalVersionedTerminalStable233
import Yulang.GeneralDictionaryUpper230Equality
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace Yulang.GeneralDictionaryVersionedSecondRaw233
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryVersionedSecondInstall233 (installed plan)
open GeneralDictionaryVersionedPointStage233 (allocated reserved ordinary)
open GeneralNominalVersionedPlans231
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
variable {model : Assignment}

abbrev oldPlan := GeneralDictionaryOptionalInstall229.plan

theorem parts (valid : GeneralNominalState.Models installed.core.erased.current.context.state model) :
    GeneralNominalState.Models snapshot model ∧ Ordinary oldPlan.packet model ∧ Ordinary plan.packet model := by
  have current := (private_models_iff plan.packet model).mp
    ((GeneralNominalVersionedInstallation231.replay_private_models plan model).mp valid)
  have previous : GeneralNominalState.Models
      GeneralDictionaryVersionedInitialFrame233.installed.core.erased.current.context.state model :=
    (GeneralDictionaryJournalRefinement228Reobserve.extended_models_iff allocated reserved ordinary model).mp current.1
  have first := (private_models_iff oldPlan.packet model).mp
    ((GeneralNominalVersionedInstallation231.replay_private_models oldPlan model).mp previous)
  exact ⟨first.1,first.2,current.2⟩

abbrev oldLo := GeneralDictionaryVersionedInitialModel233.names 0
abbrev oldHi := GeneralDictionaryVersionedInitialModel233.names 1
abbrev newLo := GeneralDictionaryVersionedNames231.freshName 0
abbrev newHi := GeneralDictionaryVersionedNames231.freshName 1
abbrev pool := [0,1,2,3,4,oldLo,oldHi,newLo,newHi]

theorem source_support : GeneralNominalState.sources installed.core.erased.current.context.state ⊆ pool := by decide +kernel

theorem union_self (a : Ty) : Equivalent (.union a a) a :=
  ⟨(common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩,
    (common_union_is_join _ _ _).mp (subtype_refl _) |>.1⟩
theorem inter_self (a : Ty) : Equivalent (.inter a a) a :=
  ⟨(common_inter_is_meet _ _ _).mp (subtype_refl _) |>.1,
    (common_inter_is_meet _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩⟩

theorem raw_old (valid : GeneralNominalState.Models installed.core.erased.current.context.state model) :
    Equivalent (model oldLo).1 (model 4).1 ∧ Equivalent (model oldHi).1 (model 2).1 := by
  have merges := (parts valid).2.1.2.1
  rw [GeneralDictionaryOptionalInstall229.bindings_exact] at merges
  have pair := (PresenceNormalForm.all_append ..).mp merges |>.1
  change PresenceNormalForm.All CommonNominalFullCarrier.model model
    (GeneralNominalAllocation.equations oldLo (.union (.var 4) (.var 4)) ++
      GeneralNominalAllocation.equations oldHi (.inter (.var 2) (.var 2))) at pair
  rw [PresenceNormalForm.all_append,GeneralNominalCaptureMerges.equations_exact,
    GeneralNominalCaptureMerges.equations_exact] at pair
  have lo := union_self (model 4).1
  have hi := inter_self (model 2).1
  exact ⟨⟨subtype_trans pair.1.1 lo.1,subtype_trans lo.2 pair.1.2⟩,
    ⟨subtype_trans pair.2.1 hi.1,subtype_trans hi.2 pair.2.2⟩⟩

theorem raw_new (valid : GeneralNominalState.Models installed.core.erased.current.context.state model) :
    Equivalent (model newLo).1 (model 2).1 ∧ Equivalent (model newHi).1 (model 2).1 := by
  have merges := (parts valid).2.2.2.1
  rw [GeneralDictionaryVersionedPoint233.bindings_exact] at merges
  have pair := (PresenceNormalForm.all_append ..).mp merges |>.1
  change PresenceNormalForm.All CommonNominalFullCarrier.model model
    (GeneralNominalAllocation.equations newLo (.union (.var 2) (.var 2)) ++
      GeneralNominalAllocation.equations newHi (.inter (.var 2) (.var 2))) at pair
  rw [PresenceNormalForm.all_append,GeneralNominalCaptureMerges.equations_exact,
    GeneralNominalCaptureMerges.equations_exact] at pair
  have lo := union_self (model 2).1
  have hi := inter_self (model 2).1
  exact ⟨⟨subtype_trans pair.1.1 lo.1,subtype_trans lo.2 pair.1.2⟩,
    ⟨subtype_trans pair.2.1 hi.1,subtype_trans hi.2 pair.2.2⟩⟩

end Yulang.GeneralDictionaryVersionedSecondRaw233
