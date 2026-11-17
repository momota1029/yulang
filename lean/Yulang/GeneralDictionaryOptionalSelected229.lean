import Yulang.GeneralDictionaryOptionalStageSafety229
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryOptionalSelected229
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryOptionalInstall229
open GeneralDictionaryOptionalStage229
open GeneralDictionaryOptionalRawStage229
open GeneralDictionaryOptionalStageSafety229
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open CommonNominalFullCarrier
abbrev currentPlan := GeneralDictionaryOptionalCurrent229.plan allocated reserved ordinary
abbrev currentPacket := currentPlan.packet

theorem survivor : GeneralNominalCenteredHeadCandidates.Survivor registry current root declaration.id currentPacket.children :=
  ⟨known,declaration,List.mem_singleton_self _,declaration_checked,rfl,rfl,[(0,0)],rfl,current_prepared,rfl⟩

theorem unique : GeneralNominalCenteredHeadCandidates.Unique registry current root declaration.id currentPacket.children := by
  refine ⟨survivor,?_⟩
  intro key kids found
  have copy := found
  obtain ⟨_,d,visible,_,identity,_⟩ := found
  cases List.mem_singleton.mp visible
  have same : key = declaration.id := identity.symm
  subst key
  exact ⟨rfl,GeneralNominalCenteredHeadCandidates.survivor_children_functional checked copy survivor⟩

theorem frame : GeneralNominalCenteredHeadOutputs.Frame registry stage.core root declaration.id currentPlan :=
  ⟨rfl,context_eq.symm,rfl,rfl,List.mem_singleton_self _,List.mem_singleton_self _,List.mem_singleton_self _,rfl,rfl,current_prepared⟩

theorem request_exact (member : output ∈ GeneralNominalCenteredHeadOutputs.requests stage.core root) : output = ⟨0,4⟩ := by
  obtain ⟨site,present,_,within⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
  cases List.mem_singleton.mp present
  exact List.mem_singleton.mp within

theorem ready : GeneralNominalCenteredHeadMatEffects.Ready stage.core root currentPlan := by
  intro output member
  cases request_exact member
  exact ⟨.explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩,rfl,rfl⟩

theorem class_effects : GeneralNominalCenteredHeadMatEffects.ClassEffects stage.core root currentPlan model := by
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

theorem capture_inputs : (GeneralNominalPacketSupport.capture currentPacket).inputs 0 = (lo,hi) := by
  unfold GeneralNominalPacketSupport.capture
  rw [GeneralDictionaryOptionalCurrent229.bindings_exact]
  rfl

theorem binder_exact : currentPlan.binder 0 = actual := by
  unfold Plan.binder
  change (if 0 ∈ declaration.outputNames then _ else if _ then _ else _) = actual
  simp only [show ¬ 0 ∈ declaration.outputNames by decide, ite_false]
  rw [capture_inputs]
  have distinct : lo ≠ hi := Ne.symm (GeneralNominalCenteredAllocation.fresh_namespaces (by decide : (1:Nat) ≠ 0))
  simp only [distinct,ite_false]
  rfl

theorem schema_equal : currentPlan.headSchema = plan.headSchema := rfl

theorem current_head_holds : currentPlan.SchemaHolds currentPlan.headSchema model := by
  rw [schema_equal,head_schema]
  constructor
  · simpa only [head_schema] using head_holds.1
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

theorem head_equations : GeneralNominalCenteredHeadOutputs.HeadEquations currentPlan model := by
  refine ⟨?_,?_,?_⟩
  · exact GeneralNominalCenteredHeadMatStepPackets.head_equations packet_holds |>.1
  · intro name member
    have same : name = 0 := by
      simpa [Declaration.inputNames,GeneralDeclarationPatterns.variablesArgs,
        GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
        GeneralDeclarationPatterns.Pattern.variables] using member
    subst name
    rw [capture_inputs,binder_exact]
    change Subtype (model lo).1 (model actual).1 ∧ Subtype (model actual).1 (model hi).1
    rw [lower_value,actual_value,upper_value]
    exact ⟨GeneralDictionaryOptionalOutput229.below_width,subtype_refl _⟩
  · exact current_head_holds

theorem selected_v6 : GeneralNominalCenteredHeadMatStepBoundary.Local registry stage root
    (.selected declaration.id currentPacket.children) := by
  refine .selected safe unique ?_
  intro conflict
  exact conflict.2 ⟨model,stage_model,⟨currentPacket.children,unique⟩,currentPlan,frame,ready,head_equations,class_effects⟩

theorem selected : GeneralDictionaryHeadSharingBoundary220.Local sourceRegistry stage root
    (.selected declaration.id currentPacket.children) := by
  have noMerged : ¬ GeneralNominalCenteredHeadAllocMergedConflict.MergedOutputConflict stage root := by
    rintro ⟨⟨first,last,member,_,_⟩,_⟩
    cases member
  have v7 : GeneralDictionaryDefaultBoundary208.Local sourceRegistry stage root
      (.selected declaration.id currentPacket.children) :=
    .ordinary noMerged (GeneralDictionaryDefaultBoundary208.ordinary_iff.mpr
      (GeneralNominalCenteredHeadAllocBoundary.local_iff.mpr selected_v6))
  refine .ordinary ?_ v7
  rintro ⟨key,children,one,_,_,_,impossible⟩
  have same : key = declaration.id := (unique.2 key children one.1).1
  subst key
  apply impossible
  refine ⟨model,stage_model,currentPlan,frame,?_⟩
  exact GeneralDictionaryHeadSharing220.head_holds currentPlan model head_equations

end Yulang.GeneralDictionaryOptionalSelected229
