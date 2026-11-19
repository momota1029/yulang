import Yulang.GeneralRebaseCompactEdgeInstall279
import Yulang.GeneralNominalVersionedMixedSourceBoundary234

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 7200000
namespace Yulang.GeneralRebaseCompactDiagnostics279
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models)
open GeneralRebaseCompactEdgeInstall279 (replaceEdges models_exact aliases_exact requests_exact frame_exact classes_exact)
open GeneralNominalVersionedDiagnostic232
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedCycles232 (Cyclic RootCycle CandidateCycle)
open GeneralNominalRecursiveInspection (Origin)
open GeneralRebaseInstallNovelty279 (Edge)

variable {roles : Roles.RoleDecls} {state : State roles} {new : List (Edge roles)}
variable {registry : Registry} {root : Occurrence roles} {key : Nat} {m : Assignment}

theorem same_models : Models (replaceEdges state new) = Models state :=
  funext fun m => propext (models_exact state new m)

theorem cyclic_iff (origin : Origin) : Cyclic (replaceEdges state new) origin ↔ Cyclic state origin :=
  GeneralNominalVersionedCycles232.full_models_only same_models

theorem root_cycle_iff : RootCycle (replaceEdges state new) root ↔ RootCycle state root := by
  unfold RootCycle
  simp only [cyclic_iff]
  rfl

theorem candidate_cycle_iff : CandidateCycle registry (replaceEdges state new) root ↔
    CandidateCycle registry state root := by
  unfold CandidateCycle
  simp only [cyclic_iff,frame_exact]

theorem safe_iff (plan : Plan roles) :
    GeneralNominalVersionedCycles232.Safe (replaceEdges state new) plan ↔
      GeneralNominalVersionedCycles232.Safe state plan := by
  unfold GeneralNominalVersionedCycles232.Safe
  simp only [cyclic_iff]

theorem ready_iff (plan : Plan roles) :
    GeneralNominalCenteredHeadMatEffects.Ready (replaceEdges state new).core root plan ↔
      GeneralNominalCenteredHeadMatEffects.Ready state.core root plan :=
  GeneralNominalVersionedFrameTransport232.ready_iff (requests_exact state new root)

theorem administrative_iff : AdministrativeReady (replaceEdges state new) root ↔
    AdministrativeReady state root := by
  unfold AdministrativeReady
  simp only [same_models,aliases_exact]
  rfl

theorem chosen_head_iff : ChosenHead registry (replaceEdges state new) root key m ↔
    ChosenHead registry state root key m := by
  unfold ChosenHead
  simp only [frame_exact,ready_iff]
  rfl

theorem chosen_effects_iff : ChosenEffects registry (replaceEdges state new) root key m ↔
    ChosenEffects registry state root key m := by
  unfold ChosenEffects
  simp only [frame_exact,ready_iff,classes_exact]
  rfl

theorem output_conflict_iff : OutputConflict registry (replaceEdges state new) root key ↔
    OutputConflict registry state root key := by
  simp only [OutputConflict,models_exact,chosen_head_iff,chosen_effects_iff]

theorem feasible_iff : Feasible registry (replaceEdges state new) root key ↔ Feasible registry state root key := by
  simp only [Feasible,models_exact,frame_exact]

theorem at_key_iff : AtKey registry (replaceEdges state new) root key ↔ AtKey registry state root key := by
  simp only [AtKey,models_exact,frame_exact,feasible_iff]

end Yulang.GeneralRebaseCompactDiagnostics279
