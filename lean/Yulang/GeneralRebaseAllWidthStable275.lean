import Yulang.GeneralRebaseAllWidthFrame275

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 7800000
namespace Yulang.GeneralRebaseAllWidthStable275
open GeneralRebaseAllWidthPlan275
open GeneralRebaseAllWidthFrame275
open GeneralRebaseAllWidthPacket275 (packet_holds)
open GeneralRebaseAllWidthRealized275 (successor model_exact)
open GeneralRebaseAllWidthCertificate275 (context)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models Effect)
open GeneralNominalVersionedMixedKernel234 (Installable Stable Committed Step)
open GeneralNominalVersionedEvidence231 (Evidence)
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryOptionalInitial229 (registry declaration)
open GeneralDictionaryVersionedSecondInstall233 (installed effect)
open GeneralDictionaryVersionedPointStage233 (allocated reserved ordinary)
open GeneralDictionaryAssociatedProvenance (Body)
open GeneralNominalVersionedEffects231 (BodyHolds ClassEffects bodyVariables)
open GeneralNominalCenteredHeadMatEffects (Ready bodySchema)
open GeneralNominalCenteredHeadOutputs (requests)

theorem same_body_schema (target : Nat) (body : Body) :
 bodySchema plan target body = bodySchema retained target body := by cases body <;> rfl

theorem same_body_values (m : Assignment) (body : Body) :
 bodyVariables plan m body = bodyVariables retained m body := by
 cases body with
 | explicit => exact funext fun mode => funext (unchanged_variables m mode)
 | default => rfl

theorem same_body_holds (target : Nat) (m : Assignment) (body : Body) :
 BodyHolds plan target m body ↔ BodyHolds retained target m body := by
 unfold BodyHolds
 rw [same_body_schema,same_body_values]

theorem ready : Ready successor.core root plan := by
 intro output present
 obtain ⟨body,check,compiled⟩ := GeneralDictionaryVersionedPointFrame233.ready allocated reserved ordinary
   raw_sites output present
 refine ⟨body,check,?_⟩
 rw [same_body_schema]
 exact compiled


theorem classes (m : Assignment) (valid : Models successor m) : ClassEffects successor.core root plan m := by
 have old := (model_exact m).mp valid
 have retainedClasses : ClassEffects successor.core root retained m :=
   (GeneralNominalVersionedRefresh232.refresh_live_iff installed context effect m).mpr
     (old.2.2 effect List.mem_cons_self).2
 refine ⟨?_,retainedClasses.2⟩
 intro output present body found
 exact (same_body_holds output.target m body).mpr (retainedClasses.1 output present body found)

theorem committed : Committed successor plan := by
 refine ⟨fun m valid => ⟨packet_holds m valid,classes m valid⟩,?_⟩
 intro child present
 rw [children_empty] at present
 cases present

theorem any_install_committed (candidate : Effect roles) (enabled : Installable registry successor candidate)
 (rooted : candidate.plan.packet.site.occurrence = root) : Committed successor candidate.plan := by
 have proposal := candidate.frame
 rw [enabled.registry_eq,enabled.snapshot_eq,rooted] at proposal
 rw [singleton_frame candidate.plan _ proposal]
 exact committed

theorem stable : Stable registry successor root :=
 GeneralNominalVersionedMixedTerminalStable234.stable raw_sites centers edges_empty
  GeneralRebaseAllWidthRefinement275.point_closed GeneralRebaseAllWidthRealized275.headless
  GeneralRebaseAllWidthRealized275.equality_closed any_install_committed

theorem halted : ∀ next, ¬ Step registry root successor next := by
 rintro next ⟨focus,generated,operation⟩
 exact stable focus generated next operation

theorem evidence (m : Assignment) (valid : Models successor m) :
 Evidence registry successor.core m root (.node declaration.id []) := by
 apply GeneralNominalVersionedEvidence231.evidence_leaf
 exact ⟨plan,GeneralNominalVersionedEvidence231.certificate_of_semantics
   frame children_empty.symm (packet_holds m valid) ready (classes m valid)⟩

theorem normalized_endpoints (m : Assignment) :
 Models successor m ↔ Models installed m ∧ Evidence registry successor.core m root (.node declaration.id []) :=
 ⟨fun valid => ⟨(model_exact m).mp valid,evidence m valid⟩,fun pair => (model_exact m).mpr pair.1⟩

end Yulang.GeneralRebaseAllWidthStable275
