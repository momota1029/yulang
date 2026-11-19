import Yulang.GeneralRebaseCompactDiagnostics279

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseCompactMerged279
open GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedMergedConflict232
open GeneralNominalCenteredHeadOutputs (EqualOutputs)
open GeneralRebaseCompactEdgeInstall279
open GeneralRebaseInstallNovelty279 (Edge)
open GeneralNominalCommonBridge (Assignment)

variable {roles : Roles.RoleDecls} {state : State roles} {new : List (Edge roles)}
variable {root : Occurrence roles} {m : Assignment}

theorem equal_outputs_iff :
    EqualOutputs (replaceEdges state new).core root m ↔ EqualOutputs state.core root m := by
  simp only [EqualOutputs,requests_exact]

theorem legacy_class_iff :
    Old.ClassEquations (replaceEdges state new).legacy root m ↔ Old.ClassEquations state.legacy root m := by
  unfold Old.ClassEquations GeneralNominalCenteredHeadAllocMergedConflict.ClassEquations
  have live (eff : GeneralNominalCenteredHeadMatStepJournal.Effect roles) :
      eff.Live (replaceEdges state new).core m ↔ eff.Live state.core m :=
    GeneralNominalVersionedFrameTransport232.class_effects_iff
      (requests_exact state new eff.plan.packet.site.occurrence) |>.trans
        (GeneralNominalVersionedEffects231.class_effects_iff _ _ _ _)
    |> (GeneralNominalVersionedEffects231.class_effects_iff _ _ _ _).symm.trans
  simp only [equal_outputs_iff,aliases_exact,live]
  rfl

theorem class_iff : ClassEquations (replaceEdges state new) root m ↔ ClassEquations state root m := by
  unfold ClassEquations
  have live (eff : GeneralNominalVersionedJournal232.Effect roles) :
      eff.Live (replaceEdges state new).core m ↔ eff.Live state.core m :=
    classes_exact state new _ _ m
  simp only [legacy_class_iff,aliases_exact,live]
  rfl

theorem context_iff (atoms : List (PresenceNormalForm.Atom Nat)) (classes : List (Occurrence roles)) :
    ContextModels (replaceEdges state new) atoms classes m ↔ ContextModels state atoms classes m := by
  unfold ContextModels
  simp only [class_iff]
  rfl

theorem merged_class_iff :
    Old.MergedClass (replaceEdges state new).legacy root ↔ Old.MergedClass state.legacy root := by
  unfold Old.MergedClass GeneralNominalCenteredHeadAllocMergedConflict.MergedClass
  simp only [aliases_exact]
  rfl

theorem conflict_iff :
    MergedOutputConflict (replaceEdges state new) root ↔ MergedOutputConflict state root := by
  unfold MergedOutputConflict
  simp only [merged_class_iff,context_iff,class_iff]
  rfl

end Yulang.GeneralRebaseCompactMerged279
