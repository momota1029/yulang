import Yulang.GeneralRebaseDepthTerminalFrame285
import Yulang.GeneralRebaseNonleafCommitted276

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 12000000
namespace Yulang.GeneralRebaseDepthCommit285
open GeneralDictionaryOutputDepth252 (snapshot plan root registry roles declaration model)
open GeneralDictionaryOutputDepthInstall252 (installed installed_model)
open GeneralRebaseDepthScalar285 (old target refreshed fixed_models preserves_known)
open GeneralNominalCenters (Plan)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalVersionedMixedKernel234 (Committed Installable)
open GeneralNominalVersionedJournal232 (Effect Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseRetarget275 (Observed retarget)
open GeneralNominalRefinements (Refines)

noncomputable def ref : Refines snapshot target.state where
  base := (GeneralNominalRefinements.refl snapshot).base
  heads := (GeneralNominalRefinements.refl snapshot).heads
  nominals := (GeneralNominalRefinements.refl snapshot).nominals
  ordinary := fun _ member => List.mem_append_left _ member
  known := preserves_known
  reserved := fun _ member => List.mem_append_left _ member
  allocated := fun _ member => List.mem_append_left _ member
  seed := rfl
  constructors := rfl

theorem interp : target.interpretation = plan.packet.context.interpretation := rfl

theorem seen : Observed plan := by
 unfold Observed
 simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,GeneralNominalInspection.translate]
 exact .cons .variables .nil

noncomputable def finalPlan : Plan roles := retarget plan ref

theorem located : GeneralNominalRecursiveCandidates.arguments target root = some [((2 : Fin 4),(2 : Fin 4))] := by
 decide +kernel

theorem emitted_none : GeneralNominalVersionedChildren232.emitted plan = [] := by
 unfold GeneralNominalVersionedChildren232.emitted
 simp [GeneralCanonicalChildOrder.canonicalRequirements]

theorem raw_sites : refreshed.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root] := by
 change _ ++ GeneralNominalVersionedChildren232.rawSites plan = _
 unfold GeneralNominalVersionedChildren232.rawSites
 rw [emitted_none]
 rfl

theorem center_sites : refreshed.core.sites = [plan.input] := by
 change _ ++ GeneralNominalVersionedChildren232.emitted plan = _
 rw [emitted_none]
 rfl

theorem no_edges : refreshed.core.erased.current.edges = [] := by
 change _ ++ GeneralNominalVersionedChildren232.edges plan = _
 unfold GeneralNominalVersionedChildren232.edges
 rw [GeneralDictionaryOutputDepth252.children_empty]
 rfl

theorem exact_plan {p : Plan roles} {key : Nat}
    (frame : Frame registry refreshed.core root key p) : p = finalPlan := by
 rcases p with ⟨⟨reg,ctx,site,decl,verified,bounds⟩,input,inputEq⟩
 have rg : reg = registry := frame.registry_eq
 have c : ctx = target := frame.context_eq
 have dg : decl = declaration := List.mem_singleton.mp frame.visible
 have ss : site = GeneralNominalDemandMerging.pointSite root :=
   List.mem_singleton.mp (raw_sites ▸ frame.raw_recorded)
 have ii : input = plan.input := List.mem_singleton.mp (center_sites ▸ frame.center_recorded)
 subst reg; subst ctx; subst site; subst decl; subst input
 have bb : [((2 : Fin 4),(2 : Fin 4))] = bounds :=
   Option.some.inj (located.symm.trans frame.located)
 subst bounds
 rfl

theorem classes (m : Assignment) (held : Models refreshed m) :
    GeneralNominalVersionedEffects231.ClassEffects refreshed.core root finalPlan m := by
 have original := (GeneralNominalVersionedInstallStep232.installed_committed
   GeneralDictionaryOutputDepth252.initial GeneralDictionaryOutputDepthInstall252.effect).1 m ((fixed_models m).mp held)
 have transported := (GeneralNominalVersionedFrameTransport232.class_effects_iff
    (before := refreshed.core) (after := installed.core)
    (fun _ => GeneralNominalVersionedRefresh232.refresh_requests installed target)
    (plan := plan) (model := m) (root := root)).mpr original.2
 exact GeneralRebaseRetargetEffects275.class_effects plan ref interp _ seen m transported

theorem committed : Committed refreshed finalPlan := by
 refine ⟨?_,?_⟩
 · intro m held
   have original := (GeneralNominalVersionedInstallStep232.installed_committed
     GeneralDictionaryOutputDepth252.initial GeneralDictionaryOutputDepthInstall252.effect).1 m ((fixed_models m).mp held)
   exact ⟨(GeneralRebaseNonleafRetarget276.holds_iff plan ref interp seen m).mpr
     ⟨held.1.1,original.1.2.1,original.1.2.2⟩,classes m held⟩
 · intro child member
   change child ∈ GeneralNominalVersionedFrame231.children (retarget plan ref).packet at member
   rw [GeneralRebaseNonleafRetarget276.children_eq plan ref interp seen,
     GeneralDictionaryOutputDepth252.children_empty] at member
   cases member

theorem no_install (e : Effect roles) (good : Installable registry refreshed e)
    (atRoot : e.plan.packet.site.occurrence = root) : Committed refreshed e.plan := by
  have frame := e.frame
  rw [good.registry_eq,good.snapshot_eq,atRoot] at frame
  rw [exact_plan frame]
  exact committed

end Yulang.GeneralRebaseDepthCommit285
