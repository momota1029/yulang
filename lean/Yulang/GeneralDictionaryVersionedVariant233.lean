import Yulang.GeneralDictionaryVersionedInitialTransport233
import Yulang.GeneralDictionaryVersionedBothStage233
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace Yulang.GeneralDictionaryVersionedVariant233
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryOptionalInstall229 (plan packet model lo hi actual)
open GeneralDictionaryVersionedInitialFrame233 (before effect installed children_empty)
open GeneralDictionaryVersionedInitialModel233 (names pool)
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)

noncomputable def variant (value : Ty) : Assignment := GeneralNominalCenteredModelExtension.assign
  GeneralDictionaryVersionedInitialModel233.extended GeneralDictionaryVersionedBothModel233.nextNames (fun _ => value)

theorem next_value (value : Ty) (index : Fin 2) :
    ((variant value) (GeneralDictionaryVersionedBothModel233.nextNames index)).1 = value :=
  GeneralNominalCenteredModelExtension.assign_value _ _ _ (by intro _ _ _; rfl) index

theorem old_name (value : Ty) (index : Fin 2) :
    variant value (names index) = GeneralDictionaryVersionedInitialModel233.extended (names index) :=
  GeneralNominalCenteredModelExtension.assign_outside _ _ _
    (fun other => GeneralDictionaryVersionedBothModel233.versions_distinct other index)

theorem old_value (value : Ty) (name : Nat) (present : name ∈ pool) : variant value name = model name := by
  rw [show variant value name = GeneralDictionaryVersionedInitialModel233.extended name from
    GeneralNominalCenteredModelExtension.assign_outside _ _ _ (fun index same =>
      GeneralDictionaryVersionedNames231.fresh_outside index.val (by
        change GeneralDictionaryVersionedNames231.freshName index.val = name at same
        rw [same]
        simpa only [pool,GeneralDictionaryVersionedSupport231.pool] using present))]
  exact GeneralDictionaryVersionedInitialModel233.old_value name present

theorem old_packet (value : Ty) : GeneralNominalCenteredHeadMatStepPackets.Holds plan (variant value) :=
  (GeneralDictionaryDefaultPacketSupport213.packet_iff plan
    (fun name member => (old_value value name
      (GeneralDictionaryVersionedInitialModel233.packet_support member)).symm)).mp
    GeneralDictionaryOptionalInstall229.packet_holds

theorem first_packet (value : Ty) : GeneralNominalVersionedPlans231.Holds plan (variant value) := by
  apply GeneralDictionaryVersionedInitialTransport233.packet_holds (old_packet value)
  · rw [old_name,GeneralDictionaryVersionedInitialModel233.fresh_value,
      old_value value lo (by simp [pool]),GeneralDictionaryOptionalInstall229.lower_value]
    rfl
  · rw [old_name,GeneralDictionaryVersionedInitialModel233.fresh_value,
      old_value value hi (by simp [pool]),GeneralDictionaryOptionalInstall229.upper_value]
    rfl

theorem classes (value : Ty) : GeneralNominalVersionedEffects231.ClassEffects before.core root plan (variant value) := by
  apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
  constructor
  · intro output member body found
    cases GeneralDictionaryOptionalInstall229.request_exact member
    have same : body = .explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩ := Option.some.inj found |>.symm
    subst body
    intro equation present
    cases List.mem_singleton.mp present
    change Equivalent ((variant value) 4).1 GeneralDictionaryOptionalOutput229.value
    rw [old_value value 4 (by simp [pool])]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro first one last two _
    cases GeneralDictionaryOptionalInstall229.request_exact one
    cases GeneralDictionaryOptionalInstall229.request_exact two
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem installed_model (value : Ty) : GeneralNominalVersionedJournal232.Models installed (variant value) := by
  apply (GeneralNominalVersionedInstall232.install_models rfl).mpr
  refine ⟨?_,first_packet value,⟨GeneralNominalVersionedPlans231.head_models (first_packet value),classes value⟩,?_,?_,?_⟩
  · exact (GeneralNominalVersionedJournal232.initial_models _ _ _).mpr
      ⟨(old_packet value).1,GeneralNominalCenters.point_root_holds _ _ root_point _⟩
  · exact (GeneralNominalVersionedFrameTransport232.class_effects_iff
      (fun _ => GeneralNominalVersionedTerminal232.requests_iff children_empty)).mpr (classes value)
  · intro prior member; cases member
  · intro prior member; cases member

theorem point_model (value : Ty) : GeneralNominalVersionedJournal232.Models
    GeneralDictionaryVersionedPointStage233.point (variant value) :=
  (GeneralDictionaryVersionedPointStage233.models_iff _).mpr (installed_model value)

end Yulang.GeneralDictionaryVersionedVariant233
