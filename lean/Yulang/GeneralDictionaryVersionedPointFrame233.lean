import Yulang.GeneralDictionaryVersionedPoint233
import Yulang.GeneralNominalVersionedEvidence231
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedPointFrame233
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryVersionedPoint233
open GeneralDictionaryVersionedNames231 (newBindings freshName)
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

variable (allocated reserved ordinary)

theorem fresh
    (outside : ∀ purpose ∈ [0,1], freshName purpose ∉ GeneralNominalState.sources (context allocated reserved ordinary).state) :
    GeneralNominalVersionedAllocation231.Fresh (context allocated reserved ordinary).state registry root.identity newBindings := by
  intro k member collision
  change k ∈ [GeneralNominalAggregateVersion231.key root.identity declaration.id 0 0 newBindings,
    GeneralNominalAggregateVersion231.key root.identity declaration.id 1 0 newBindings,
    GeneralNominalAggregateVersion231.key root.identity declaration.id 0 0 newBindings,
    GeneralNominalAggregateVersion231.key root.identity declaration.id 1 0 newBindings] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals exfalso
  all_goals first | exact outside 0 (by simp) collision | exact outside 1 (by simp) collision

theorem prepared {model : Assignment} (values : Values model)
    (valid : GeneralNominalState.Models (context allocated reserved ordinary).state model)
    (outside : ∀ purpose ∈ [0,1], freshName purpose ∉ GeneralNominalState.sources (context allocated reserved ordinary).state) :
    GeneralNominalVersionedCandidates231.Prepared registry (context allocated reserved ordinary) root declaration := by
  refine ⟨source.metadata,⟨?_,by intro output member; cases member⟩,[(0,0)],rfl,?_,?_,model,?_⟩
  · intro index
    constructor <;> exact GeneralNominalAllocationSupport.slot_source (context allocated reserved ordinary).state (0 : Fin 5)
  · change GeneralNominalVersionedAllocation231.Fresh (context allocated reserved ordinary).state registry root.identity
      (packet allocated reserved ordinary).bindings
    rw [bindings_exact]
    exact fresh allocated reserved ordinary outside
  · rw [GeneralDictionaryOptionalCurrent229.report_exact]
    exact ⟨rfl,rfl,rfl⟩
  · exact head_models allocated reserved ordinary values valid

theorem known : ¬ GeneralNominalState.RootPending (context allocated reserved ordinary).state root.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨0,rfl,Or.inr ⟨descriptor (2,2),rfl⟩⟩

theorem survivor {model : Assignment} (values : Values model)
    (valid : GeneralNominalState.Models (context allocated reserved ordinary).state model)
    (outside : ∀ purpose ∈ [0,1], freshName purpose ∉ GeneralNominalState.sources (context allocated reserved ordinary).state) :
    GeneralNominalVersionedCandidates231.Survivor registry (context allocated reserved ordinary) root declaration.id [] := by
  refine ⟨known allocated reserved ordinary,declaration,List.mem_singleton_self _,declaration_checked,
    rfl,rfl,[(0,0)],rfl,prepared allocated reserved ordinary values valid outside,?_⟩
  exact (children_empty allocated reserved ordinary).symm

theorem unique {model : Assignment} (values : Values model)
    (valid : GeneralNominalState.Models (context allocated reserved ordinary).state model)
    (outside : ∀ purpose ∈ [0,1], freshName purpose ∉ GeneralNominalState.sources (context allocated reserved ordinary).state) :
    GeneralNominalVersionedCandidates231.Unique registry (context allocated reserved ordinary) root declaration.id [] := by
  have found := survivor allocated reserved ordinary values valid outside
  refine ⟨found,?_⟩
  intro key kids other
  have copy := other
  obtain ⟨_,d,visible,_,identity,_⟩ := other
  cases List.mem_singleton.mp visible
  have same : key = declaration.id := identity.symm
  subst key
  exact ⟨rfl,GeneralNominalVersionedCandidates231.survivor_children_functional checked copy found⟩

variable {state : GeneralNominalCenteredSteps.State roles}

theorem frame {model : Assignment} (values : Values model)
    (valid : GeneralNominalState.Models (context allocated reserved ordinary).state model)
    (outside : ∀ purpose ∈ [0,1], freshName purpose ∉ GeneralNominalState.sources (context allocated reserved ordinary).state)
    (same : state.erased.current.context = context allocated reserved ordinary)
    (raw : state.erased.current.sites = [GeneralNominalDemandMerging.pointSite root])
    (centers : state.sites = [rootSite snapshot.seed root]) :
    GeneralNominalVersionedEvidence231.Frame registry state root declaration.id (plan allocated reserved ordinary) := by
  refine ⟨rfl,same.symm,rfl,rfl,?_,?_,List.mem_singleton_self _,rfl,rfl,?_⟩
  · rw [raw]; exact List.mem_singleton_self _
  · rw [centers]; exact List.mem_singleton_self _
  · rw [same]; exact prepared allocated reserved ordinary values valid outside

theorem request_exact (raw : state.erased.current.sites = [GeneralNominalDemandMerging.pointSite root])
    (member : output ∈ GeneralNominalCenteredHeadOutputs.requests state root) : output = ⟨0,4⟩ := by
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  rw [raw] at present
  cases List.mem_singleton.mp present
  exact List.mem_singleton.mp within

theorem ready (raw : state.erased.current.sites = [GeneralNominalDemandMerging.pointSite root]) :
    GeneralNominalCenteredHeadMatEffects.Ready state root (plan allocated reserved ordinary) := by
  intro output member
  cases request_exact raw member
  exact ⟨.explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩,rfl,rfl⟩

theorem class_effects {model : Assignment} (output : (model 4).1 = GeneralDictionaryOptionalOutput229.value)
    (raw : state.erased.current.sites = [GeneralNominalDemandMerging.pointSite root]) :
    GeneralNominalVersionedEffects231.ClassEffects state root (plan allocated reserved ordinary) model := by
  apply (GeneralNominalVersionedEffects231.class_effects_iff ..).mpr
  constructor
  · intro request member body found
    cases request_exact raw member
    have equal : body = .explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩ := Option.some.inj found |>.symm
    subst body
    intro equation present
    cases List.mem_singleton.mp present
    change Equivalent (model 4).1 GeneralDictionaryOptionalOutput229.value
    rw [output]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro first one last two _
    cases request_exact raw one
    cases request_exact raw two
    exact ⟨subtype_refl _,subtype_refl _⟩

theorem evidence {model : Assignment} (values : Values model)
    (valid : GeneralNominalState.Models (context allocated reserved ordinary).state model)
    (outside : ∀ purpose ∈ [0,1], freshName purpose ∉ GeneralNominalState.sources (context allocated reserved ordinary).state)
    (same : state.erased.current.context = context allocated reserved ordinary)
    (raw : state.erased.current.sites = [GeneralNominalDemandMerging.pointSite root])
    (centers : state.sites = [rootSite snapshot.seed root]) :
    GeneralNominalVersionedEvidence231.Evidence registry state model root (.node declaration.id []) := by
  apply GeneralNominalVersionedEvidence231.evidence_leaf
  refine ⟨plan allocated reserved ordinary,?_⟩
  exact GeneralNominalVersionedEvidence231.certificate_of_semantics
    (frame allocated reserved ordinary values valid outside same raw centers)
    (children_empty allocated reserved ordinary).symm
    (packet_holds allocated reserved ordinary values valid)
    (ready allocated reserved ordinary raw)
    (class_effects allocated reserved ordinary values.output raw)

end Yulang.GeneralDictionaryVersionedPointFrame233
