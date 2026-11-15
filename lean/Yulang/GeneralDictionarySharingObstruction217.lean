import Yulang.GeneralDictionaryCurrentAgreement217
import Yulang.GeneralDictionaryTotalEvidence206

/-! Necessary actual sharing for a certificate, independent of reachability.
Failure for one frame is not failure for all possible certificates. -/
namespace Yulang.GeneralDictionarySharingObstruction217
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveInspection GeneralNominalMaterialization
open GeneralNominalQueryProvenance183 (headInspection)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalOriginTerms
open GeneralDictionaryCountedProjection216 (Agreement)
variable {roles : Roles.RoleDecls}

theorem schema_agreement (plan : Plan roles) (model : Assignment)
    (schema : plan.SchemaHolds plan.headSchema model) : Agreement plan model := by
  intro a one b two names first last atFirst atLast
  obtain ⟨x,atX,usedX⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    plan.packet.context.state _ plan.packet.bounds _ 0 a one
  obtain ⟨y,atY,usedY⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    plan.packet.context.state _ plan.packet.bounds _ 0 b two
  cases Option.some.inj (atX.symm.trans atFirst)
  cases Option.some.inj (atY.symm.trans atLast)
  have left : Same model first (.source (plan.binder a.name)) := by
    simpa only [ite_true] using schema.2 _ usedX
  have right : Same model last (.source (plan.binder b.name)) := by
    simpa only [ite_true] using schema.2 _ usedY
  rw [names] at left
  exact same_trans left (same_symm right)

theorem head_agreement (plan : Plan roles) (model : Assignment)
    (head : GeneralNominalCenteredHeadOutputs.HeadEquations plan model) : Agreement plan model :=
  schema_agreement plan model head.2.2

theorem packet_agreement (plan : Plan roles) (model : Assignment)
    (packet : GeneralNominalCenteredHeadMatStepPackets.Holds plan model) : Agreement plan model :=
  head_agreement plan model (GeneralNominalCenteredHeadMatStepPackets.head_equations packet)

theorem certificate_agreement (plan : Plan roles) (model : Assignment)
    (certificate : GeneralDictionaryTotalEvidence206.Certificate registry state model root key children plan) :
    Agreement plan model := packet_agreement plan model certificate.packet

def Impossible (registry : Registry) (state : GeneralNominalCenteredSteps.State roles)
    (model : Assignment) (root : Occurrence roles) (key : Nat) : Prop :=
  ∀ plan, GeneralNominalCenteredHeadOutputs.Frame registry state root key plan → ¬ Agreement plan model

theorem no_instance (impossible : Impossible registry state model root key) (children) :
    ¬ GeneralDictionaryTotalEvidence206.Instance registry state model root key children := by
  rintro ⟨plan,certificate⟩
  exact impossible plan certificate.frame (certificate_agreement plan model certificate)

theorem no_evidence (impossible : Impossible registry state model root key) (dictionaries) :
    ¬ GeneralDictionaryTotalEvidence206.Evidence registry state model root (.node key dictionaries) := by
  intro evidence
  have payload := (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr evidence
  cases payload with
  | node source children => exact no_instance impossible _ source

theorem no_chosen_head
    (impossible : ∀ model, GeneralNominalCenteredHeadMatStepJournal.Models state model →
      Impossible registry state.core model root key) :
    ¬ ∃ model, GeneralNominalCenteredHeadMatStepJournal.Models state model ∧
      GeneralNominalCenteredHeadMatStepLocal.ChosenHead registry state root key model := by
  rintro ⟨model,valid,_,plan,frame,_,head⟩
  exact impossible model valid plan frame (head_agreement plan model head)

theorem no_output_conflict
    (impossible : ∀ model, GeneralNominalCenteredHeadMatStepJournal.Models state model →
      Impossible registry state.core model root key) :
    ¬ GeneralNominalCenteredHeadMatStepLocal.OutputConflict registry state root key :=
  fun conflict => no_chosen_head impossible conflict.1
end Yulang.GeneralDictionarySharingObstruction217
