import Yulang.GeneralDictionaryOptionalInitial229
import Yulang.GeneralDictionaryReachableRest227
import Yulang.GeneralNominalCenteredHeadMatCompletionLive

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryOptionalInstall229
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalCenters GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open CommonNominalFullCarrier
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229

abbrev packet : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,context,GeneralNominalDemandMerging.pointSite root,declaration,declaration_checked,[(0,0)]⟩
abbrev plan : Plan roles := ⟨packet,rootSite snapshot.seed root,rfl⟩
abbrev lo := fresh snapshot.seed root.identity declaration.id 0 0 0
abbrev hi := fresh snapshot.seed root.identity declaration.id 1 0 0
abbrev actual := fresh snapshot.seed root.identity declaration.id 8 0 0

def model : GeneralNominalCommonBridge.Assignment := fun n =>
  if n ≤ 4 then GeneralDictionaryOptionalSource229.modelLow n else (if n = lo then GeneralDictionaryOptionalOutput229.value else .emptyRecord,Common.rowEmpty)

theorem fresh_large (purpose : Nat) : 4 < fresh snapshot.seed root.identity declaration.id purpose 0 0 :=
  GeneralNominalIdentities.source_above_seed snapshot.seed _

theorem lower_value : (model lo).1 = GeneralDictionaryOptionalOutput229.value := by simp [model,Nat.not_le.mpr (fresh_large 0)]
theorem upper_value : (model hi).1 = .emptyRecord := by
  have ne : hi ≠ lo := GeneralNominalCenteredAllocation.fresh_namespaces (by decide : (1:Nat) ≠ 0)
  simp [model,Nat.not_le.mpr (fresh_large 1),ne]
theorem actual_value : (model actual).1 = .emptyRecord := by
  have ne : actual ≠ lo := GeneralNominalCenteredAllocation.fresh_namespaces (by decide : (8:Nat) ≠ 0)
  simp [model,Nat.not_le.mpr (fresh_large 8),ne]

theorem source_model : GeneralNominalState.Models snapshot model :=
  (GeneralDictionaryDefaultRawSupport213.models_iff snapshot (first := GeneralDictionaryOptionalSource229.modelLow) (last := model)
    (fun n member => by simp [model,source_bound n (GeneralDictionaryDefaultRawSupport213.subset snapshot member)])).mp
      GeneralDictionaryOptionalSource229.source_models

theorem inhabited : GeneralNominalCenteredHeadMatStepJournal.Models start model :=
  (GeneralNominalCenteredHeadMatStepJournal.point_initial_models root_point).mpr source_model

theorem query : GeneralNominalInspection.queries snapshot interpretation declaration =
    [.nominal 0 [.variables [0],.variables [0]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
    GeneralNominalInspection.translate,interpretation]

abbrev origin0 : Origin := .nominal (.source 0) 0 0
abbrev origin1 : Origin := .nominal (.source 0) 0 1
abbrev calculated : Report snapshot where
  captures := [⟨0,(4,2),some origin0⟩,⟨0,(4,2),some origin1⟩]
  inspected := [(0,0)]
  checked := [(0,0),(0,0),(4,2),(4,2)]
  anchors := [(origin0,(4,2)),(origin1,(4,2))]

theorem report_exact : report context declaration [(0,0)] = calculated := by
  unfold report
  rw [query]
  simp [inspectMany,inspect,Report.visit,Report.append,typeArguments,calculated,snapshot,state]
  rw [inspectMany.eq_2,inspectMany.eq_2,inspectMany.eq_1]
  simp only [inspect.eq_1,Report.append]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem bindings_exact : packet.bindings = [(0,4,2),(0,4,2)] := by
  change bindings snapshot (report context declaration [(0,0)]) = _
  rw [report_exact]; rfl

theorem seen0 : Observes model origin0 .emptyRecord :=
  .nominal (.source 0) ⟨subtype_refl _,subtype_refl _⟩ rfl
theorem seen1 : Observes model origin1 .emptyRecord :=
  .nominal (.source 0) ⟨subtype_refl _,subtype_refl _⟩ rfl

theorem observed_value (index : Nat) (small : index < 2) (seen : Observes model (.nominal (.source 0) 0 index) value) :
    Equivalent value .emptyRecord := by
  have observed : Observes model (.nominal (.source 0) 0 index) .emptyRecord := by
    rcases (show index = 0 ∨ index = 1 by omega) with rfl | rfl
    · exact seen0
    · exact seen1
  exact nominal_observation_unique model (.argument (.source 0) 0 index) value .emptyRecord seen observed

theorem fit_observed (index : Nat) (small : index < 2) (seen : Observes model (.nominal (.source 0) 0 index) value) :
    Fits snapshot model (4,2) value := by
  have equal := observed_value index small seen
  exact ⟨subtype_trans GeneralDictionaryOptionalOutput229.below_width equal.2,equal.1⟩

theorem raw_projection : ProjectionModels snapshot (report context declaration [(0,0)]) model := by
  rw [report_exact]
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨⟨_,seen0⟩,fun _ seen => fit_observed 0 (by decide) seen⟩
    · cases List.mem_singleton.mp member
      exact ⟨⟨_,seen1⟩,fun _ seen => fit_observed 1 (by decide) seen⟩
  · intro test member; cases member
  · intro first one last two _ origin located value seen
    rcases List.mem_cons.mp one with rfl | one
    all_goals first | cases List.mem_singleton.mp one | skip
    all_goals cases Option.some.inj located
    all_goals rcases List.mem_cons.mp two with rfl | two
    all_goals first | cases List.mem_singleton.mp two | skip
    all_goals first | exact fit_observed 0 (by decide) seen | exact fit_observed 1 (by decide) seen
  · intro first one last two _ a b firstOrigin lastOrigin x y seenX seenY
    rcases List.mem_cons.mp one with rfl | one
    all_goals first | cases List.mem_singleton.mp one | skip
    all_goals cases Option.some.inj firstOrigin
    all_goals rcases List.mem_cons.mp two with rfl | two
    all_goals first | cases List.mem_singleton.mp two | skip
    all_goals cases Option.some.inj lastOrigin
    all_goals
      have ex : Equivalent x .emptyRecord := by first | exact observed_value 0 (by decide) seenX | exact observed_value 1 (by decide) seenX
      have ey : Equivalent y .emptyRecord := by first | exact observed_value 0 (by decide) seenY | exact observed_value 1 (by decide) seenY
      exact ⟨subtype_trans ex.1 ey.2,subtype_trans ey.1 ex.2⟩

theorem merge_model : PresenceNormalForm.All CommonNominalFullCarrier.model model
    (GeneralNominalAllocation.merges snapshot registry root.identity declaration packet.bindings) := by
  rw [bindings_exact]
  have pair : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalAllocation.equations lo (.union (.var 4) (.var 4)) ++
        GeneralNominalAllocation.equations hi (.inter (.var 2) (.var 2))) := by
    rw [PresenceNormalForm.all_append,GeneralNominalCaptureMerges.equations_exact,
      GeneralNominalCaptureMerges.equations_exact]
    change Equivalent (model lo).1 (.union GeneralDictionaryOptionalOutput229.value GeneralDictionaryOptionalOutput229.value) ∧
      Equivalent (model hi).1 (.inter .emptyRecord .emptyRecord)
    rw [lower_value,upper_value]
    exact ⟨⟨(common_union_is_join _ _ _).mp (subtype_refl _) |>.1,
      (common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩⟩,
      ⟨(common_inter_is_meet _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩,
      (common_inter_is_meet _ _ _).mp (subtype_refl _) |>.1⟩⟩
  change PresenceNormalForm.All CommonNominalFullCarrier.model model (_ ++ _)
  exact (PresenceNormalForm.all_append ..).mpr ⟨pair,pair⟩

theorem head_model : GeneralNominalCenteredHeadCandidates.HeadModels registry context root declaration [(0,0)] model := by
  refine ⟨?_,raw_projection⟩
  unfold privateState
  apply (GeneralNominalState.extend_models ..).mpr
  refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨source_model,?_,merge_model⟩,?_⟩
  · change GeneralNominalAllocation.Compatible packet.bindings model
    rw [bindings_exact]
    intro first one last two _
    rcases List.mem_cons.mp one with rfl | one
    all_goals first | cases List.mem_singleton.mp one | skip
    all_goals rcases List.mem_cons.mp two with rfl | two
    all_goals first | cases List.mem_singleton.mp two | skip
    all_goals exact GeneralDictionaryOptionalOutput229.below_width
  · rw [report_exact]
    intro atom member
    simp only [selfChecks,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals first | exact subtype_refl _ | exact GeneralDictionaryOptionalOutput229.below_width

theorem prepared : GeneralNominalCenteredHeadCandidates.Prepared registry context root declaration := by
  refine ⟨source.metadata,⟨source.linked.1,by intro output member; cases member⟩,GeneralNominalSourceFormation.initial_fresh _ source _,
    [(0,0)],?_,?_,model,head_model⟩
  · decide +kernel
  · rw [report_exact]; exact ⟨rfl,rfl,rfl⟩

theorem frame : GeneralNominalCenteredHeadOutputs.Frame registry start.core root declaration.id plan :=
  ⟨rfl,rfl,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,List.mem_singleton_self _,rfl,
    by decide +kernel,prepared⟩

theorem head_schema : plan.headSchema =
    { tests := [(.source 0,.nominal 0 2)]
      variables := [⟨0,origin0,.actual⟩,⟨0,origin1,.actual⟩] } := by
  unfold Plan.headSchema
  rw [query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,List.ofFn_succ,plan,rootSite,origin0,origin1]

theorem binder_exact : plan.binder 0 = actual := by decide +kernel

theorem head_holds : plan.SchemaHolds plan.headSchema model := by
  rw [head_schema]
  constructor
  · intro test member
    cases List.mem_singleton.mp member
    refine ⟨⟨_,.source 0⟩,?_⟩
    intro value seen
    cases seen
    exact ⟨[.inl .emptyRecord,.inl .emptyRecord],rfl,subtype_refl _,subtype_refl _⟩
  · intro entry member
    rcases List.mem_cons.mp member with rfl | member
    all_goals first | cases List.mem_singleton.mp member | skip
    all_goals
      simp only [ite_true]
      refine ⟨?_,⟨_,.source _⟩,?_⟩
      · first | exact ⟨_,seen0⟩ | exact ⟨_,seen1⟩
      · intro x y seenX seenY
        cases seenY
        rw [binder_exact,actual_value]
        first | exact observed_value 0 (by decide) seenX | exact observed_value 1 (by decide) seenX

theorem emitted_schema : GeneralNominalCenteredHeadMatPlans.emittedSchema plan =
    ⟨[⟨4,.actual,GeneralDictionaryOptionalExpression229.expression⟩],false⟩ := by
  unfold GeneralNominalCenteredHeadMatPlans.emittedSchema GeneralNominalCenteredHeadMatSchemas.requests
  simp only [GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
    GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  rfl

theorem emitted_holds : (GeneralNominalCenteredHeadMatPlans.emittedSchema plan).Holds
    (GeneralNominalCenteredHeadMatEffects.variables plan model) model := by
  rw [emitted_schema]
  intro equation member
  cases List.mem_singleton.mp member
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem packet_holds : GeneralNominalCenteredHeadMatStepPackets.Holds plan model := by
  apply (GeneralDictionaryReachableRest227.packet_characterization plan frame model inhabited).mpr
  exact ⟨merge_model,head_holds,emitted_holds,by intro clause member; cases member⟩

theorem known : ¬ GeneralNominalState.RootPending snapshot root.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨0,rfl,Or.inr ⟨descriptor (4,2),rfl⟩⟩

theorem children_empty : packet.children = [] := by
  unfold GeneralNominalSaturationState.Packet.children GeneralNominalAllocation.children
    GeneralDictionaryEmissionPlans.children GeneralCanonicalChildOrder.canonicalEmit
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_nil]
  rfl

theorem survivor : GeneralNominalCenteredHeadCandidates.Survivor registry context root declaration.id packet.children :=
  ⟨known,declaration,List.mem_singleton_self _,declaration_checked,rfl,rfl,[(0,0)],by decide +kernel,prepared,rfl⟩

theorem unique : GeneralNominalCenteredHeadCandidates.Unique registry context root declaration.id packet.children := by
  refine ⟨survivor,?_⟩
  intro key kids found
  have copy := found
  obtain ⟨_,d,visible,_,identity,_⟩ := found
  cases List.mem_singleton.mp visible
  have same : key = declaration.id := identity.symm
  subst key
  exact ⟨rfl,GeneralNominalCenteredHeadCandidates.survivor_children_functional checked copy survivor⟩

theorem request_exact (member : output ∈ GeneralNominalCenteredHeadOutputs.requests start.core root) : output = ⟨0,4⟩ := by
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  cases List.mem_singleton.mp present
  exact List.mem_singleton.mp within

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready start.core root plan := by
  intro output member
  cases request_exact member
  exact ⟨.explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩,rfl,rfl⟩

theorem class_effects : GeneralNominalCenteredHeadMatEffects.ClassEffects start.core root plan model := by
  constructor
  · intro output member body found
    cases request_exact member
    have equal : body = .explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩ := Option.some.inj found |>.symm
    subst body
    intro equation present
    cases List.mem_singleton.mp present
    exact ⟨subtype_refl _,subtype_refl _⟩
  · intro first one last two _
    cases request_exact one
    cases request_exact two
    exact ⟨subtype_refl _,subtype_refl _⟩

noncomputable def effect : GeneralNominalCenteredHeadMatStepJournal.Effect roles :=
  ⟨registry,start.core,plan,frame,unique,ready⟩
noncomputable def installed := GeneralNominalCenteredHeadMatStepJournal.install start effect

theorem legacy_reachable : B4TargetV6.Reachable
    (GeneralNominalCenteredHeadMatStepBoundary.boundary roles) registry root start :=
  ⟨start,⟨context,labels,source,root_point,ground,coverage,rfl⟩,.refl⟩

theorem effect_holds : effect.Holds model := ⟨GeneralNominalCenteredHeadMatStepPackets.head_equations packet_holds,class_effects⟩

theorem common : GeneralNominalCenteredHeadMatStepJournal.InstallationModels start effect model :=
  (GeneralNominalCenteredHeadMatCompletionLive.installation_models_iff checked legacy_reachable rfl rfl model).mpr
    ⟨inhabited,packet_holds,effect_holds⟩

theorem installed_model : GeneralNominalCenteredHeadMatStepJournal.Models installed model :=
  GeneralNominalCenteredHeadMatCompletionLive.common_successor_model checked legacy_reachable rfl rfl
    inhabited packet_holds effect_holds

end Yulang.GeneralDictionaryOptionalInstall229
