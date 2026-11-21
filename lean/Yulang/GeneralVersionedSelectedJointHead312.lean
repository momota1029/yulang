import Yulang.GeneralVersionedCurrentFrame312
import Yulang.GeneralVersionedAliasReport312
import Yulang.GeneralNominalVersionedMixedSelectedWitness236
import Yulang.GeneralNominalVersionedCurrentHead237

set_option backward.isDefEq.respectTransparency false
/-! The real selector's output-conflict check supplies joint head/class
semantics once a current head witness exists. Functional current frames
prevent replacing the certificate's plan by an unrelated plan. -/
namespace Yulang.GeneralVersionedSelectedJointHead312
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open GeneralNominalVersionedDiagnostic232 (ChosenHead HeadEquations)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedEffects231 (ClassEffects)
open GeneralNominalVersionedPlans231 (SchemaHolds HeadModels)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : State roles}
  {root focus : Occurrence roles} {m : Assignment} {plan : Plan roles}

theorem head_of_schema
    (frame : Frame (Compiled registry) state.core focus key plan)
    (valid : Models state m)
    (head : HeadModels plan.packet m) (schema : SchemaHolds plan plan.headSchema m) :
    HeadEquations plan m :=
  ⟨valid.1.2.2.2.1 plan.input frame.center_recorded,
    fun name present => GeneralNominalVersionedCurrentHead237.capture_fits plan frame valid head schema name (.inl present),
    schema⟩

theorem effects_for_frame
    (checked : (boundary roles).Checked registry)
    (path : B4TargetV8.Reachable (boundary roles) registry root state)
    (picked : Local registry state focus (.selected key children))
    (frame : Frame (Compiled registry) state.core focus key plan)
    (head : ∃ m, Models state m ∧ HeadEquations plan m) :
    ∃ m, Models state m ∧ HeadEquations plan m ∧ ClassEffects state.core focus plan m := by
  obtain ⟨m,valid,good⟩ := head
  have mixed := GeneralNominalVersionedMixedSourceBoundary234.local_iff.mp picked
  have diag := GeneralNominalVersionedMixedBoundary234.local_iff.mp mixed
  have unique := GeneralNominalVersionedMixedCurrentEvidence235.selected_unique mixed
  have ready := GeneralNominalVersionedMixedReady235.ready checked path frame
  have chosen : ChosenHead (Compiled registry) state focus key m :=
    ⟨⟨children,unique⟩,plan,frame,ready,good⟩
  obtain ⟨next,model,_,other,otherFrame,_,headAndClass,classes⟩ :=
    GeneralNominalVersionedMixedSelectedWitness236.effects diag ⟨m,valid,chosen⟩
  have same := GeneralVersionedCurrentFrame312.frame_exact checked path frame otherFrame
  exact ⟨next,model,same.symm ▸ headAndClass,same.symm ▸ classes⟩

theorem report_for_frame
    (frame : Frame (Compiled registry) state.core focus key plan)
    (valid : Models state m) (head : HeadEquations plan m) :
    (GeneralNominalPacketSupport.report plan.packet).conflicts = [] ∧
    GeneralVersionedProtectedPeer312.Raw plan.packet m := by
  have locate := frame.occurrence_eq.symm ▸ frame.located
  exact GeneralVersionedAliasReport312.from_tests plan frame.context_eq frame.center_recorded locate m valid
    head.2.2.1 (GeneralDictionaryHeadSharing220.agreement_of_holds plan m
      (GeneralNominalVersionedHeadSharing232.schema_holds plan m head.2.2))

end Yulang.GeneralVersionedSelectedJointHead312
