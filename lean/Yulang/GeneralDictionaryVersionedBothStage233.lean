import Yulang.GeneralDictionaryVersionedBothPacket233
import Yulang.GeneralDictionaryVersionedPointStage233
import Yulang.GeneralDictionaryVersionedPointFrame233
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedBothStage233
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryOptionalInstall229 (plan packet)
open GeneralDictionaryVersionedBothModel233
open GeneralDictionaryVersionedInitialFrame233 (before effect installed children_empty)
open GeneralNominalCenters
theorem class_effects : GeneralNominalVersionedEffects231.ClassEffects before.core root plan extended := by
  apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
  constructor
  · intro output member body found
    cases GeneralDictionaryOptionalInstall229.request_exact member
    have same : body = .explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩ := Option.some.inj found |>.symm
    subst body
    intro equation present
    cases List.mem_singleton.mp present
    change CommonNominalFullCarrier.Equivalent (extended 4).1 GeneralDictionaryOptionalOutput229.value
    rw [old_value 4 (by simp [pool])]
    exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩
  · intro first one last two _
    cases GeneralDictionaryOptionalInstall229.request_exact one
    cases GeneralDictionaryOptionalInstall229.request_exact two
    exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem installation_models : GeneralNominalVersionedInstall232.InstallationModels before effect extended := by
  refine ⟨initial_model,GeneralDictionaryVersionedBothPacket233.packet_holds,
    ⟨GeneralDictionaryVersionedBothPacket233.head_model,class_effects⟩,?_,?_,?_⟩
  · exact (GeneralNominalVersionedFrameTransport232.class_effects_iff
      (fun _ => GeneralNominalVersionedTerminal232.requests_iff children_empty)).mpr class_effects
  · intro prior member; cases member
  · intro prior member; cases member

theorem installed_model : GeneralNominalVersionedJournal232.Models installed extended :=
  (GeneralNominalVersionedInstall232.install_models rfl).mpr installation_models


theorem point_model : GeneralNominalVersionedJournal232.Models GeneralDictionaryVersionedPointStage233.point extended :=
  (GeneralDictionaryVersionedPointStage233.models_iff _).mpr installed_model

theorem values : GeneralDictionaryVersionedPoint233.Values extended := by
  refine ⟨?_,?_,?_,?_,next_value 0,next_value 1⟩
  · rw [old_value 0 (by simp [pool,GeneralDictionaryVersionedInitialModel233.pool])]; rfl
  · rw [old_value 2 (by simp [pool,GeneralDictionaryVersionedInitialModel233.pool])]; rfl
  · rw [old_value GeneralDictionaryOptionalInstall229.actual (by simp [pool,GeneralDictionaryVersionedInitialModel233.pool])]
    exact GeneralDictionaryOptionalInstall229.actual_value
  · rw [old_value 4 (by simp [pool,GeneralDictionaryVersionedInitialModel233.pool])]; rfl

theorem point_packet : GeneralNominalVersionedPlans231.Holds
    (GeneralDictionaryVersionedPoint233.plan GeneralDictionaryVersionedPointStage233.allocated
      GeneralDictionaryVersionedPointStage233.reserved GeneralDictionaryVersionedPointStage233.ordinary) extended :=
  GeneralDictionaryVersionedPoint233.packet_holds _ _ _ values point_model.1.1

end Yulang.GeneralDictionaryVersionedBothStage233
