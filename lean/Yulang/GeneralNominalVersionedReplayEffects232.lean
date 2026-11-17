import Yulang.GeneralNominalVersionedInstallation231
import Yulang.GeneralNominalVersionedEvidence231
set_option backward.isDefEq.respectTransparency false

/-! Exact associated-output semantics under fixed-observation context replay.
The packet is rebuilt with the same source interpretation and actual centers.
This does not assert consistency of arbitrary added atoms or changed reports. -/
namespace Yulang.GeneralNominalVersionedReplayEffects232
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedTransport231
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryAssociatedProvenance (Body)
variable (reserved : List Nat) (atoms : List (PresenceNormalForm.Atom Nat))
  (allocated : List GeneralNominalIdentities.Origin)

theorem compile_body_eq (plan : Plan roles) (body : Body) :
    GeneralNominalCenteredHeadMatEffects.compileBody (extendedPlan reserved atoms allocated plan) body = GeneralNominalCenteredHeadMatEffects.compileBody plan body := by
  cases body <;> rfl

theorem body_schema_eq (plan : Plan roles) (target : Nat) (body : Body) :
    GeneralNominalCenteredHeadMatEffects.bodySchema (extendedPlan reserved atoms allocated plan) target body = GeneralNominalCenteredHeadMatEffects.bodySchema plan target body := by
  unfold GeneralNominalCenteredHeadMatEffects.bodySchema
  rw [compile_body_eq]

theorem body_variables_eq (plan : Plan roles) (model : Assignment) (body : Body) :
    GeneralNominalVersionedEffects231.bodyVariables (extendedPlan reserved atoms allocated plan) model body =
      GeneralNominalVersionedEffects231.bodyVariables plan model body := by
  cases body with
  | explicit => exact variables_eq reserved atoms allocated plan model
  | default => rfl

theorem body_holds_iff (plan : Plan roles) (target : Nat) (model : Assignment) (body : Body) :
    GeneralNominalVersionedEffects231.BodyHolds (extendedPlan reserved atoms allocated plan) target model body ↔
      GeneralNominalVersionedEffects231.BodyHolds plan target model body := by
  unfold GeneralNominalVersionedEffects231.BodyHolds
  rw [body_schema_eq,body_variables_eq]

theorem old_body_holds_iff (plan : Plan roles) (target : Nat) (model : Assignment) (body : Body) :
    GeneralNominalCenteredHeadMatEffects.BodyHolds (extendedPlan reserved atoms allocated plan) target model body ↔ GeneralNominalCenteredHeadMatEffects.BodyHolds plan target model body := by
  rw [← GeneralNominalVersionedEffects231.body_holds_iff,← GeneralNominalVersionedEffects231.body_holds_iff]
  exact body_holds_iff reserved atoms allocated plan target model body

theorem ready_iff (state : GeneralNominalCenteredSteps.State roles) (root : Occurrence roles) (plan : Plan roles) :
    GeneralNominalCenteredHeadMatEffects.Ready state root (extendedPlan reserved atoms allocated plan) ↔ GeneralNominalCenteredHeadMatEffects.Ready state root plan := by
  unfold GeneralNominalCenteredHeadMatEffects.Ready
  simp only [plan_packet,packet_declaration,body_schema_eq]

theorem class_effects_iff (state : GeneralNominalCenteredSteps.State roles) (root : Occurrence roles)
    (plan : Plan roles) (model : Assignment) :
    GeneralNominalVersionedEffects231.ClassEffects state root (extendedPlan reserved atoms allocated plan) model ↔
      GeneralNominalVersionedEffects231.ClassEffects state root plan model := by
  unfold GeneralNominalVersionedEffects231.ClassEffects
  simp only [plan_packet,packet_declaration,body_holds_iff]

theorem output_witness_iff (plan : Plan roles) (model : Assignment) (output : GeneralSourceState.Output) :
    GeneralDictionaryDefaultEvidence204.OutputWitness (extendedPlan reserved atoms allocated plan) model output ↔
      GeneralDictionaryDefaultEvidence204.OutputWitness plan model output := by
  unfold GeneralDictionaryDefaultEvidence204.OutputWitness
  simp only [plan_packet,packet_declaration,compile_body_eq,old_body_holds_iff]

theorem replay_ready_iff (state : GeneralNominalCenteredSteps.State roles) (root : Occurrence roles) (plan : Plan roles) :
    GeneralNominalCenteredHeadMatEffects.Ready state root (GeneralNominalVersionedInstallation231.replayPlan plan) ↔ GeneralNominalCenteredHeadMatEffects.Ready state root plan :=
  ready_iff _ _ _ state root plan

theorem replay_class_effects_iff (state : GeneralNominalCenteredSteps.State roles) (root : Occurrence roles)
    (plan : Plan roles) (model : Assignment) :
    GeneralNominalVersionedEffects231.ClassEffects state root (GeneralNominalVersionedInstallation231.replayPlan plan) model ↔
      GeneralNominalVersionedEffects231.ClassEffects state root plan model :=
  class_effects_iff _ _ _ state root plan model

theorem replay_output_witness_iff (plan : Plan roles) (model : Assignment) (output : GeneralSourceState.Output) :
    GeneralDictionaryDefaultEvidence204.OutputWitness (GeneralNominalVersionedInstallation231.replayPlan plan) model output ↔
      GeneralDictionaryDefaultEvidence204.OutputWitness plan model output :=
  output_witness_iff _ _ _ plan model output

end Yulang.GeneralNominalVersionedReplayEffects232
