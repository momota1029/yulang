import Yulang.GeneralMixedCompoundSourcePrefix308
import Yulang.GeneralRebaseCompoundReplacement273
import Yulang.GeneralDeferredLadderTransport302

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 19000
set_option maxHeartbeats 9500000
namespace Yulang.GeneralMixedCompoundPointFirstPlan308
open GeneralDictionaryJournalRefinement228Source (roles root snapshot root_point source_bound)
open GeneralDictionaryCompoundSource238 (registry declaration declaration_checked source sourceRegistry)
open GeneralDictionaryCompoundFrame238 (before)
open GeneralDictionaryCompoundObstruction238 (currentPlan)
open GeneralMixedCompoundSourcePrefix308 (pointBefore early_reobservation)
open GeneralDictionaryCompoundCurrent238 (currentContext report_exact bindings_exact)
open GeneralNominalVersionedJournal232 (Models Effect)
open GeneralNominalVersionedCandidates231 (inputs Prepared Survivor Unique)
open GeneralNominalVersionedPlans231 (Holds HeadModels head_models)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCenteredHeadMatPlanData (Same)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (Plan rootSite)
open CommonNominalFullCarrier

abbrev ctx := currentContext [] [] []
abbrev pkt := GeneralDictionaryCompoundCurrent238.packet [] [] []
abbrev plan := GeneralDictionaryCompoundCurrent238.plan [] [] []
noncomputable abbrev candidateModel :=
  GeneralRebaseCompoundReplacement273.patch GeneralDictionaryCompoundPointModel238.extended

theorem same_plan : Same currentPlan plan :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,by
    change GeneralNominalReportErasure.erase _ (GeneralNominalRecursiveCandidates.report _ declaration [(0,0)]) =
      GeneralNominalReportErasure.erase _ (GeneralNominalRecursiveCandidates.report _ declaration [(0,0)])
    rw [report_exact,report_exact]; rfl⟩

theorem raw_model : GeneralNominalState.Models ctx.state candidateModel :=
  ⟨GeneralRebaseCompoundReplacement273.holds.1.1,GeneralRebaseCompoundReplacement273.holds.1.2.1,
    fun _ absent => nomatch absent⟩

theorem held : Holds plan candidateModel :=
  GeneralDeferredLadderTransport302.held_of_reindex same_plan _ GeneralRebaseCompoundReplacement273.holds raw_model

theorem model : Models pointBefore candidateModel := by
  apply (GeneralMixedCompoundSourcePrefix308.reobserve_models _).mpr
  exact (GeneralNominalVersionedJournal232.initial_models _ _ _).mpr
    ⟨(GeneralDictionaryJournalRefinement228Reobserve.point_models_iff _).mp raw_model,
      GeneralNominalCenters.point_root_holds _ _ root_point _⟩

theorem fresh : GeneralNominalVersionedAllocation231.Fresh ctx.state registry root.identity pkt.bindings := by
  intro key _ present
  have bound := source_bound _ present
  have higher := GeneralNominalIdentities.source_above_seed snapshot.seed key
  change 4 < GeneralNominalIdentities.source snapshot.seed key at higher
  change GeneralNominalIdentities.source snapshot.seed key ≤ 4 at bound
  omega

theorem known : ¬ GeneralNominalState.RootPending ctx.state root.demand := by
  rintro ⟨index,notKnown⟩
  exact notKnown ⟨0,rfl,Or.inr ⟨_,rfl⟩⟩

theorem located : GeneralNominalRecursiveCandidates.arguments ctx (inputs root) = some [(0,0)] := by
  decide +kernel

theorem prepared : Prepared registry ctx root declaration := by
  refine ⟨source.metadata,⟨source.linked.1,fun _ absent => nomatch absent⟩,[(0,0)],located,fresh,?_,candidateModel,head_models held⟩
  rw [report_exact]; exact ⟨rfl,rfl,rfl⟩

theorem frame : Frame registry pointBefore.core root declaration.id plan :=
  ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,List.mem_singleton_self _,rfl,located,prepared⟩

theorem unique : Unique registry ctx root declaration.id (GeneralNominalVersionedFrame231.children pkt) := by
  have one : Survivor registry ctx root declaration.id (GeneralNominalVersionedFrame231.children pkt) :=
    ⟨known,declaration,List.mem_singleton_self _,declaration_checked,rfl,rfl,[(0,0)],located,prepared,rfl⟩
  refine ⟨one,?_⟩
  intro key kids other
  have copy := other
  obtain ⟨_,d,visible,_,eq,_⟩ := copy
  cases List.mem_singleton.mp visible
  subst key
  exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional GeneralDictionaryCompoundSource238.checked other one⟩

theorem request_exact (output : GeneralSourceState.Output)
    (member : output ∈ GeneralNominalCenteredHeadOutputs.requests pointBefore.core root) : output = ⟨0,4⟩ := by
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  cases List.mem_singleton.mp present
  exact List.mem_singleton.mp within

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready pointBefore.core root plan := by
  intro output member
  cases request_exact output member
  exact ⟨.explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩,rfl,rfl⟩

theorem class_effects : GeneralNominalVersionedEffects231.ClassEffects pointBefore.core root plan candidateModel := by
  constructor
  · intro output member body found
    cases request_exact output member
    have exactBody : body = .explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩ :=
      (Option.some.inj found).symm
    subst body
    intro atom present
    cases List.mem_singleton.mp present
    change Equivalent (candidateModel 4).1 GeneralDictionaryOptionalOutput229.value
    rw [GeneralRebaseCompoundReplacement273.values.output]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro a one b two _
    cases request_exact a one
    cases request_exact b two
    exact ⟨subtype_refl _,subtype_refl _⟩

noncomputable def effect : Effect roles :=
  ⟨registry,pointBefore.core,plan,frame,unique,ready⟩

noncomputable abbrev pointFirst := GeneralNominalVersionedInstall232.install pointBefore effect

end Yulang.GeneralMixedCompoundPointFirstPlan308
