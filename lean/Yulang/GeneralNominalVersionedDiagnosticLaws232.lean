import Yulang.GeneralNominalVersionedDiagnostic232
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalVersionedDiagnosticLaws232
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedDiagnostic232
open CommonRoleOutermostResolver

theorem output_clear
    (valid : Models state model)
    (unique : GeneralNominalVersionedCandidates231.Unique registry state.core.erased.current.context root key children)
    (frame : GeneralNominalVersionedEvidence231.Frame registry state.core root key plan)
    (ready : GeneralNominalCenteredHeadMatEffects.Ready state.core root plan)
    (packet : GeneralNominalVersionedPlans231.Holds plan model)
    (effects : GeneralNominalVersionedEffects231.ClassEffects state.core root plan model) :
    ¬ OutputConflict registry state root key := by
  intro conflict
  exact conflict.2 ⟨model,valid,⟨⟨children,unique⟩,plan,frame,ready,head_equations packet,effects⟩⟩

theorem sharing_clear
    (valid : Models state model)
    (unique : GeneralNominalVersionedCandidates231.Unique registry state.core.erased.current.context root key children)
    (frame : GeneralNominalVersionedEvidence231.Frame registry state.core root key plan)
    (packet : GeneralNominalVersionedPlans231.Holds plan model) :
    ¬ SharingConflict registry state root := by
  rintro ⟨other,kids,chosen,_,bad⟩
  have same : other = key := (unique.2 other kids chosen.1).1
  subst other
  exact bad.2.2 ⟨model,valid,plan,frame,GeneralNominalVersionedHeadSharing232.packet_holds plan model packet⟩

/-- The V8 selection rule is unchanged. All semantic feasibility premises are
explicit, not inferred just from head applicability. -/
theorem selected_of_model
    (safe : B4TargetV8.SafeKnown (boundary roles) registry state root)
    (unique : GeneralNominalVersionedCandidates231.Unique registry state.core.erased.current.context root key children)
    (valid : Models state model)
    (frame : GeneralNominalVersionedEvidence231.Frame registry state.core root key plan)
    (ready : GeneralNominalCenteredHeadMatEffects.Ready state.core root plan)
    (packet : GeneralNominalVersionedPlans231.Holds plan model)
    (effects : GeneralNominalVersionedEffects231.ClassEffects state.core root plan model)
    (merged : ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict state root) :
    Local registry state root (.selected key children) :=
  .ordinary (sharing_clear valid unique frame packet)
    (.ordinary merged (.selected safe unique (output_clear valid unique frame ready packet effects)))

end Yulang.GeneralNominalVersionedDiagnosticLaws232
