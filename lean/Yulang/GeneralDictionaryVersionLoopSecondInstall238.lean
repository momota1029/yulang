import Yulang.GeneralDictionaryVersionLoopSecondSafety238
import Yulang.GeneralDictionaryVersionLoopSecondFull238
import Yulang.GeneralNominalVersionedMixedQuietInstall235
import Yulang.GeneralNominalVersionedFrameFunctional232
import Yulang.GeneralNominalVersionedMixedKernelCache234
namespace Yulang.GeneralDictionaryVersionLoopSecondInstall238
open GeneralDictionaryVersionLoopSource237
open GeneralDictionaryVersionLoopSecondPacket238
open GeneralDictionaryVersionLoopSecondFrame238 GeneralDictionaryVersionLoopSecondSafety238
open GeneralDictionaryVersionLoopSecondFull238
open GeneralDictionaryVersionLoopNext237 (current)
open GeneralDictionaryVersionLoopRetarget237 (retargeted retargeted_model)
open GeneralNominalVersionedMixedKernel234

theorem classes (assignment) : GeneralNominalVersionedEffects231.ClassEffects retargeted.core root plan assignment := by
 apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
 constructor <;> intro output member <;> simp [requests_empty] at member

theorem common : GeneralNominalVersionedInstall232.InstallationModels retargeted effect model := by
 apply (GeneralNominalVersionedMixedQuietInstall235.installation_models_iff rfl
   (GeneralNominalVersionedMixedQuietInstall235.terminal_quiet children_empty) model).mpr
 exact ⟨retargeted_model,packet_holds,head_model,classes _⟩

theorem frame_plan {candidate : GeneralNominalCenters.Plan roles} {key}
 (framed : GeneralNominalVersionedEvidence231.Frame registry retargeted.core root key candidate) : candidate = plan :=
 GeneralNominalVersionedFrameFunctional232.frame_plan_unique rfl raw_sites centers framed frame

theorem positions : GeneralNominalVersionedCycles232.Safe retargeted plan :=
 ⟨by decide +kernel,fun entry _ => acyclic entry.1⟩

theorem installable : Installable registry retargeted effect := by
 refine ⟨rfl,rfl,safe,?_,?_,?_,positions,?_,model,common⟩
 · exact GeneralNominalVersionedMixedKernelCache234.reachable_cache
     (GeneralNominalVersionedMixedSourceBoundary234.reachable_compiled GeneralDictionaryVersionLoopPrefix238.reachable)
 · change (GeneralNominalVersionedPlans231.emittedSchema plan).unknown = false
   rw [emitted_empty]
 · intro packet member
   change packet ∈ [GeneralDictionaryVersionLoopPacket237.packet] at member
   cases List.mem_singleton.mp member
   intro _; rfl
 · intro candidate input framed
   change GeneralNominalVersionedEvidence231.Frame registry retargeted.core root candidate.packet.declaration.id candidate at framed
   cases frame_plan framed
   exact positions
noncomputable def installed := GeneralNominalVersionedInstall232.install retargeted effect

theorem installed_model : GeneralNominalVersionedJournal232.Models installed model :=
 (GeneralNominalVersionedInstall232.install_models rfl).mpr common
end Yulang.GeneralDictionaryVersionLoopSecondInstall238
