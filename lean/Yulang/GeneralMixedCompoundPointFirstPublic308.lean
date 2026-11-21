import Yulang.GeneralMixedCompoundPointFirstInstall308
import Yulang.GeneralRebaseCompoundReplacementPublic273
import Yulang.GeneralMixedIndexedPlanSemantics305

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 13000000
namespace Yulang.GeneralMixedCompoundPointFirstPublic308
open GeneralDictionaryJournalRefinement228Source (roles root snapshot root_point)
open GeneralDictionaryCompoundSource238 (sourceRegistry registry checked)
open GeneralDictionaryCompoundFrame238 (before installed)
open GeneralDictionaryCompoundPoint238 (point)
open GeneralDictionaryCompoundObstruction238 (currentPlan)
open GeneralMixedCompoundSourcePrefix308 (pointBefore reobserve_models)
open GeneralMixedCompoundPointFirstPlan308 (plan pointFirst effect ctx same_plan request_exact)
open GeneralMixedCompoundPointFirstInstall308 (before_reachable)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedPlans231 (Holds)
open GeneralNominalVersionedEffects231 (ClassEffects)
open GeneralNominalVersionedInstall232 (InstallationModels install_models)
open GeneralNominalCenteredHeadOutputs (requests mem_requests_iff)
open GeneralRebaseCompoundPublic273 (Fixed)
open GeneralRebaseCompoundRows273 (Agrees)
open GeneralRebaseCompoundReplacementFrame273 (Meaning output_necessary)
open GeneralRebaseCompoundSourceTypes273 (PublicSource Body source_reads restricted_exact)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

theorem before_of_raw (m : Assignment) (raw : GeneralNominalState.Models ctx.state m) : Models pointBefore m := by
  apply (reobserve_models m).mpr
  exact (GeneralNominalVersionedJournal232.initial_models _ _ _).mpr
    ⟨(GeneralDictionaryJournalRefinement228Reobserve.point_models_iff m).mp raw,
      GeneralNominalCenters.point_root_holds _ _ root_point m⟩

theorem raw_of_held (m : Assignment) (held : Holds currentPlan m) :
    GeneralNominalState.Models ctx.state m :=
  ⟨held.1.1,held.1.2.1,fun _ absent => nomatch absent⟩

theorem old_request : (⟨0,4⟩ : GeneralSourceState.Output) ∈ requests point.core root := by
  apply mem_requests_iff.mpr
  refine ⟨GeneralNominalDemandMerging.pointSite root,?_,.refl _,List.mem_singleton_self _⟩
  rw [GeneralDictionaryCompoundSites238.raw_sites]
  exact List.mem_cons_self

theorem class_of_meaning (m : Assignment) (valid : Meaning m) :
    ClassEffects pointBefore.core root plan m := by
  constructor
  · intro output included body found
    cases request_exact output included
    exact (GeneralMixedIndexedPlanSemantics305.body_same same_plan 4 body m).mp
      (valid.2.1 _ old_request body found)
  · intro a one b two _
    cases request_exact a one
    cases request_exact b two
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem install_of_meaning (m : Assignment) (valid : Meaning m) : Models pointFirst m := by
  apply (install_models rfl).mpr
  apply (GeneralNominalVersionedMixedCommon235.installation_models_iff ⟨rfl,checked⟩ before_reachable rfl rfl).mpr
  have raw := raw_of_held m valid.1
  exact ⟨before_of_raw m raw,GeneralDeferredLadderTransport302.held_of_reindex same_plan m valid.1 raw,
    class_of_meaning m valid⟩

theorem installed_held (m : Assignment) (valid : Models pointFirst m) : Holds plan m :=
  valid.2.1 _ (List.mem_cons_self)

theorem output_value (m : Assignment) (valid : Holds plan m) : Body m := by
  have h := valid.2.2
  unfold GeneralNominalVersionedPlans231.Outputs at h
  have a := GeneralDeferredLadderTransport302.emitted_eq same_plan
  have b := GeneralRebaseCompoundReplacement273.emitted_same
  rw [← a,b,GeneralDictionaryCompoundVersionedPacket238.emitted_schema,GeneralDictionaryCompoundTotal238.emitted_schema] at h
  exact h _ List.mem_cons_self

theorem every_public (m : Assignment) (valid : Models pointFirst m) : Fixed m := by
  have held := installed_held m valid
  have raw := (GeneralDictionaryJournalRefinement228Reobserve.point_models_iff m).mp held.1
  exact (restricted_exact m).mpr ⟨source_reads m raw,output_value m held⟩

theorem exact_projection (boundary : Assignment) : (∃ m, Agrees m boundary ∧ Models pointFirst m) ↔ Fixed boundary := by
  constructor
  · rintro ⟨m,agree,valid⟩ id small
    rw [← agree.1 id small]
    exact every_public m valid id small
  · intro fixed
    exact ⟨_,GeneralRebaseCompoundReplacementPublic273.agrees boundary,
      install_of_meaning _ (GeneralRebaseCompoundReplacementPublic273.completed boundary fixed)⟩

theorem same_projection (boundary : Assignment) :
    (∃ m, Agrees m boundary ∧ Models pointFirst m) ↔ (∃ m, Agrees m boundary ∧ Models installed m) :=
  (exact_projection boundary).trans (GeneralRebaseCompoundRows273.public_exact boundary).symm

end Yulang.GeneralMixedCompoundPointFirstPublic308
