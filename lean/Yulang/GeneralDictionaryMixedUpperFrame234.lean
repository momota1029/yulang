import Yulang.GeneralDictionaryMixedUpperPlan234
import Yulang.GeneralDictionaryMixedUpperStep234
import Yulang.GeneralDictionaryVersionedSecondSelected233
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
set_option maxHeartbeats 1000000
namespace Yulang.GeneralDictionaryMixedUpperFrame234
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryMixedUpperPlan234
open GeneralDictionaryMixedUpperStep234 (next)
open GeneralDictionaryVersionedUpperSnapshot233 (extendedContext pointDesc)
open GeneralNominalVersionedPlans231
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters

 theorem raw_sites : next.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root] :=
  GeneralDictionaryVersionedSecondSelected233.raw_sites

theorem centers : next.core.sites = [rootSite snapshot.seed root] :=
  GeneralDictionaryVersionedSecondSelected233.centers

theorem owned (member : key ∈ GeneralNominalVersionedAllocation231.keys registry root.identity packet.bindings) :
    key ∈ extendedContext.state.allocated := by
  apply GeneralNominalVersionedInstallation231.replay_keys_owned GeneralDictionaryVersionedSecondInstall233.plan
  change key ∈ GeneralNominalVersionedAllocation231.keys registry root.identity
    GeneralDictionaryVersionedSecondInstall233.plan.packet.bindings
  rw [GeneralDictionaryVersionedPoint233.bindings_exact]
  simpa only [bindings_exact] using member

theorem prepared {model : Assignment} (valid : Holds plan model) :
    GeneralNominalVersionedCandidates231.Prepared registry extendedContext root declaration := by
  refine ⟨source.metadata,⟨?_,by intro output member; cases member⟩,[(0,0)],rfl,?_,?_,model,?_⟩
  · intro index
    constructor <;> exact GeneralNominalAllocationSupport.slot_source extendedContext.state (0 : Fin 6)
  · change GeneralNominalVersionedAllocation231.Fresh extendedContext.state registry root.identity packet.bindings
    intro key member _
    exact owned member
  · rw [report_exact]
    exact ⟨rfl,rfl,rfl⟩
  · exact GeneralNominalVersionedPlans231.head_models valid

theorem known : ¬ GeneralNominalState.RootPending extendedContext.state root.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨0,rfl,Or.inr ⟨pointDesc,rfl⟩⟩

theorem frame {model : Assignment} (valid : Holds plan model) :
    GeneralNominalVersionedEvidence231.Frame registry next.core root declaration.id plan := by
  refine ⟨rfl,rfl,rfl,rfl,?_,?_,List.mem_singleton_self _,rfl,rfl,prepared valid⟩
  · rw [raw_sites]; exact List.mem_singleton_self _
  · rw [centers]; exact List.mem_singleton_self _

theorem unique {model : Assignment} (valid : Holds plan model) :
    GeneralNominalVersionedCandidates231.Unique registry extendedContext root declaration.id [] := by
  have survivor : GeneralNominalVersionedCandidates231.Survivor registry extendedContext root declaration.id [] :=
    ⟨known,declaration,List.mem_singleton_self _,declaration_checked,rfl,rfl,[(0,0)],rfl,
      prepared valid,children_empty.symm⟩
  refine ⟨survivor,?_⟩
  intro key kids other
  have copy := other
  obtain ⟨_,d,visible,_,identity,_⟩ := other
  cases List.mem_singleton.mp visible
  have same : key = declaration.id := identity.symm
  subst key
  exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional checked copy survivor⟩

theorem request_exact (member : output ∈ GeneralNominalCenteredHeadOutputs.requests next.core root) :
    output = ⟨0,4⟩ := GeneralDictionaryVersionedPointFrame233.request_exact raw_sites member

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready next.core root plan := by
  intro output member
  cases request_exact member
  exact ⟨.explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩,rfl,rfl⟩

theorem class_effects {model : Assignment} (valid : Holds plan model) :
    GeneralNominalVersionedEffects231.ClassEffects next.core root plan model := by
  apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
  constructor
  · intro request member body found
    cases request_exact member
    have equal : body = .explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩ := Option.some.inj found |>.symm
    subst body
    intro equation present
    cases List.mem_singleton.mp present
    change CommonNominalFullCarrier.Equivalent (model 4).1 GeneralDictionaryOptionalOutput229.value
    have out := valid.2.2
    unfold Outputs at out
    rw [emitted_schema] at out
    have held := out ⟨4,.actual,GeneralDictionaryOptionalExpression229.expression⟩ (List.mem_singleton_self _)
    change CommonNominalFullCarrier.Equivalent (model 4).1 GeneralDictionaryOptionalOutput229.value at held
    exact held
  · intro first one last two _
    cases request_exact one
    cases request_exact two
    exact ⟨CommonNominalFullCarrier.subtype_refl _,CommonNominalFullCarrier.subtype_refl _⟩

theorem evidence {model : Assignment} (valid : Holds plan model) :
    GeneralNominalVersionedEvidence231.Evidence registry next.core model root (.node declaration.id []) :=
  GeneralNominalVersionedEvidence231.evidence_leaf ⟨plan,
    GeneralNominalVersionedEvidence231.certificate_of_semantics (frame valid) children_empty.symm
      valid ready (class_effects valid)⟩

end Yulang.GeneralDictionaryMixedUpperFrame234
