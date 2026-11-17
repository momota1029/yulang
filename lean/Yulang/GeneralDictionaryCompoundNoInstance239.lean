import Yulang.GeneralDictionaryCompoundObstruction239
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryCompoundNoInstance239
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryCompoundSource238 GeneralDictionaryCompoundRefresh239 GeneralDictionaryCompoundSnapshot239
open GeneralDictionaryCompoundObstruction239 GeneralDictionaryCompoundSites238
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedEvidence231
open GeneralNominalCommonBridge (Assignment)

theorem frame_plan {candidate : Plan roles}
    (framed : Frame registry refreshed.core root key candidate) : candidate = currentPlan := by
  rcases candidate with ⟨⟨reg,ctx,site,decl,check,bounds⟩,input,inputEq⟩
  have regEq : reg = registry := framed.registry_eq
  have ctxEq : ctx = extendedContext :=
    framed.context_eq
  have declEq : decl = declaration := List.mem_singleton.mp framed.visible
  have siteEq : site = GeneralNominalDemandMerging.pointSite root := root_raw framed.raw_recorded framed.occurrence_eq
  have inputSame : input = rootSite snapshot.seed root := root_center framed.center_recorded (inputEq.trans framed.occurrence_eq)
  subst reg; subst ctx; subst decl; subst site; subst input
  have located : GeneralNominalRecursiveCandidates.arguments extendedContext (GeneralNominalVersionedCandidates231.inputs root) = some [(0,0)] := by decide +kernel
  have boundsEq : [(0,0)] = bounds := Option.some.inj (located.symm.trans framed.located)
  subst bounds
  rfl

theorem no_instance (model : Assignment) (valid : GeneralNominalVersionedJournal232.Models refreshed model)
    (key : Nat) (children : List (Occurrence roles)) : ¬ Instance registry refreshed.core model root key children := by
  rintro ⟨candidate,certificate⟩
  have same := frame_plan certificate.frame
  subst candidate
  exact no_current_packet model valid certificate.packet

end Yulang.GeneralDictionaryCompoundNoInstance239
