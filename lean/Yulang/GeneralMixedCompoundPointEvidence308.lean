import Yulang.GeneralMixedCompoundPointRoot308
import Yulang.GeneralNominalVersionedMixedSelectedFrame235

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 16000000
namespace Yulang.GeneralMixedCompoundPointEvidence308
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryCompoundSource238 (registry sourceRegistry declaration checked)
open GeneralDictionaryCompoundSites238 (childSite)
open GeneralMixedCompoundPointFirstPlan308 (candidateModel)
open GeneralMixedCompoundPointViewTrust308 (observed)
open GeneralMixedCompoundPointChild308 (no_evidence reachable same_request)
open GeneralMixedCompoundPointSites308 (request_exact equal_outputs)
open GeneralMixedCompoundPointRoot308 (plan frame frame_plan held models_observed child_exact)
open GeneralNominalVersionedEvidence231 (Certificate Evidence)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready observed.core root plan :=
  GeneralNominalVersionedMixedReady235.ready ⟨rfl,checked⟩ reachable frame

theorem class_effects : GeneralNominalVersionedEffects231.ClassEffects observed.core root plan candidateModel := by
  refine ⟨?_,equal_outputs _ root⟩
  intro output member body found
  cases request_exact root output member
  have exactBody : body = .explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩ :=
    (Option.some.inj found).symm
  subst body
  intro atom present
  cases List.mem_singleton.mp present
  change Equivalent (candidateModel 4).1 GeneralDictionaryOptionalOutput229.value
  rw [GeneralRebaseCompoundReplacement273.values.output]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem local_certificate :
    Certificate registry observed.core candidateModel root declaration.id [childSite.occurrence] plan :=
  GeneralNominalVersionedEvidence231.certificate_of_semantics frame child_exact.symm
    (held _ models_observed) ready class_effects

theorem witnessed_request :
    GeneralDictionaryDefaultEvidence204.OutputWitness plan candidateModel ⟨0,4⟩ :=
  local_certificate.outputs _ (List.mem_singleton_self _)

theorem no_recursive_root (m : Assignment) (payload : GeneralDictionaryReadback.Payload) :
    ¬ Evidence registry observed.core m root payload := by
  intro ev
  have indexed := (GeneralDictionaryReadback.payload_iff_erased _ _ _).mpr ev
  cases indexed with
  | node instanceProof kids =>
    obtain ⟨p,certificate⟩ := instanceProof
    have exactPlan := frame_plan certificate.frame
    subst p
    have exactChildren := certificate.children_eq.trans child_exact
    rw [exactChildren] at kids
    cases kids with
    | cons child _ => exact no_evidence m _ ((GeneralDictionaryReadback.payload_iff_erased _ _ _).mp child)

/-- The request-bearing parent has an actual current local certificate and a
real generated child; the recursive construction still cannot produce even one
tree, as the mandatory child has no current evidence. -/
theorem certificate_not_tree :
    (∃ p, Certificate registry observed.core candidateModel root declaration.id [childSite.occurrence] p) ∧
    (∀ payload, ¬ Evidence registry observed.core candidateModel root payload) :=
  ⟨⟨plan,local_certificate⟩,no_recursive_root _⟩

end Yulang.GeneralMixedCompoundPointEvidence308
