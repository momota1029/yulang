import Yulang.GeneralGeneratedNestedInstallInterface299

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralDepthTwoRootPlan300
open GeneralGeneratedNestedSource299
open GeneralGeneratedNestedPredictions299
open GeneralNominalExamples (interpretation registry)
open GeneralDeclarationExamples (roles display display_checked)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalCenters
open GeneralNominalVersionedPlans231
open GeneralNominalVersionedFrame231 (binder capture childSite)
open GeneralNominalRecursiveInspection
open GeneralNominalUnaryCaptureFacts

abbrev plan : Plan roles := ⟨parentPacket,rootSite snapshot.seed root,rfl⟩
abbrev origin : Origin := .nominal (.source 0) 0 0
abbrev child : Site roles := childSite plan GeneralDeclarationExamples.displayChild
  (display_checked.signature.2.2.2 _ (by simp))

theorem bindings : parentPacket.bindings = [(0,(1,1))] := by
  change GeneralNominalRecursiveInspection.bindings snapshot
    (GeneralNominalRecursiveCandidates.report context display [(0,0)]) = _
  rw [root_report]; rfl

theorem center : binder plan 0 = 1 := by decide +kernel

theorem captured : (capture parentPacket).inputs 0 = (1,1) := by decide +kernel

theorem head_schema : plan.headSchema =
    ⟨[⟨0,origin,.actual⟩],[(.source 0,.nominal 0 1)],false⟩ := by
  unfold Plan.headSchema
  rw [query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,rootSite,List.ofFn_succ,origin]

theorem emitted_schema : emittedSchema plan =
    ⟨[⟨1,.lower,.variable 0⟩,⟨1,.upper,.variable 0⟩],false⟩ := by
  change GeneralNominalCenteredHeadMatSchemas.generated _ _ (emittedRequests parentPacket) = _
  unfold emittedRequests GeneralCanonicalChildOrder.canonicalEmit
  unfold GeneralNominalVersionedFrame231.capture GeneralNominalVersionedFrame231.frame
  rw [bindings]
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
    List.mergeSort_singleton]
  rfl

theorem emitted_sites : GeneralNominalVersionedChildren232.emitted plan = [child] := by
  have length : (GeneralNominalVersionedChildren232.emitted plan).length = 1 :=
    GeneralNominalVersionedChildren232.emitted_length _
  have seen : child ∈ GeneralNominalVersionedChildren232.emitted plan := by
    unfold GeneralNominalVersionedChildren232.emitted
    have member : GeneralDeclarationExamples.displayChild ∈
        GeneralCanonicalChildOrder.canonicalRequirements plan.packet.declaration.requirements :=
      (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mp (List.mem_singleton_self _)
    exact List.mem_map.mpr ⟨⟨_,member⟩,List.mem_attach _ _,rfl⟩
  obtain ⟨one,view⟩ := List.length_eq_one_iff.mp length
  rw [view] at seen ⊢
  cases List.mem_singleton.mp seen
  rfl

theorem child_args : ∀ i, child.occurrence.demand.arguments i = (1,1) := by
  intro i
  have iz : i.val = 0 := by have h := i.isLt; change i.val < 1 at h; omega
  have e : i = ⟨0,by decide +kernel⟩ := Fin.ext iz
  subst i
  decide +kernel

theorem child_data : child.occurrence = middle ∧
    ∀ i, child.center i = 1 := by
  constructor
  · have old := GeneralNominalVersionedChildren232.emitted_occurrences plan
    rw [parent_children,emitted_sites] at old
    exact List.singleton_inj.mp old
  · intro i
    have iz : i.val = 0 := by have h := i.isLt; change i.val < 1 at h; omega
    unfold child
    simpa only [iz,GeneralDeclarationExamples.displayChild,List.getElem_cons_zero,
      GeneralNominalVersionedFrame231.childSite,GeneralNominalVersionedFrame231.emittedCenter,
      GeneralDeclarationPatterns.normalize] using center

theorem child_schema : childSchema plan GeneralDeclarationExamples.displayChild
    (display_checked.signature.2.2.2 _ (by simp)) = ⟨[⟨1,.actual,.variable 0⟩],false⟩ := by
  unfold childSchema childRequests
  simp only [GeneralDeclarationExamples.displayChild,List.ofFn_succ,List.ofFn_zero]
  change GeneralNominalCenteredHeadMatSchemas.generated _ _ [⟨.var 0,child.center _,.actual⟩] = _
  rw [child_data.2]
  rfl

theorem var_actual (m : Assignment) : variables plan m .actual 0 = (m 1).1 := by
  unfold variables
  rw [center]
  rfl

theorem var_bounds (m : Assignment) :
    variables plan m .lower 0 = (m 1).1 ∧ variables plan m .upper 0 = (m 1).1 := by
  unfold variables
  rw [captured]
  exact ⟨rfl,rfl⟩

theorem update_support (m : Assignment) (valid : GeneralNominalState.Models snapshot m) :
    Ordinary parentPacket m ∧ ProjectionModels snapshot (GeneralNominalPacketSupport.report parentPacket) m := by
  have fact := GeneralNominalUnaryCaptureFacts.private_models context compiled root display 0
    (listDescriptor 1) rfl 0 rfl (1,1) rfl query m valid
  have raw := (GeneralNominalPacketSupport.private_exact parentPacket m).mp fact.1
  refine ⟨⟨raw.2.1,?_,raw.2.2.2⟩,fact.2⟩
  unfold GeneralNominalVersionedAllocation231.merges
  rw [bindings]
  intro atom present
  cases present

theorem holds (m : Assignment) (valid : GeneralNominalState.Models snapshot m) : Holds plan m := by
  have captured := nominal_argument_bounds snapshot m valid 0 (listDescriptor 1) rfl 0 (1,1) rfl
  have projected : GeneralNominalOriginTerms.Same m origin (.source 1) := by
    refine ⟨captured.1,⟨_,.source 1⟩,?_⟩
    intro a b one two
    cases two
    exact ⟨(captured.2 a one).2,(captured.2 a one).1⟩
  have supported := update_support m valid
  refine ⟨valid,⟨supported.1,supported.2,point_root_holds _ root (fun _ => rfl) m,?_,?_,?_,?_⟩,?_⟩
  · intro name used
    have zero : name = 0 := by
      rcases used with head | ⟨clause,member,used⟩
      · simpa [GeneralDeclarations.Declaration.inputNames,GeneralDeclarationPatterns.variablesArgs,
          GeneralDeclarationPatterns.Pattern.variables,GeneralDeclarationPatterns.normalizeArgs,
          GeneralDeclarationPatterns.normalize,display] using head
      · cases List.mem_singleton.mp member
        simpa [GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables,
          GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
          GeneralDeclarationExamples.displayChild] using used
    subst name
    change GeneralNominalCaptureMerges.Fits m ((capture parentPacket).inputs 0) (m (binder plan 0)).1
    rw [GeneralDepthTwoRootPlan300.captured,center]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · rw [head_schema]
    constructor
    · intro entry member
      cases List.mem_singleton.mp member
      obtain ⟨arguments,fit,equals⟩ := valid.2.1 0 (listDescriptor 1) rfl
      refine ⟨⟨_,.source 0⟩,?_⟩
      intro actual seen
      cases seen
      have length : arguments.length = 1 := by
        change GeneralNominalState.FitsAll snapshot.base m [.type (1,1)] arguments at fit
        cases fit with | cons _ tail => cases tail; rfl
      exact ⟨arguments,length,equals⟩
    · intro entry member
      cases List.mem_singleton.mp member
      simpa only [ite_true,center] using projected
  · rw [emitted_schema]
    intro entry member _
    rcases List.mem_cons.mp member with rfl|rest
    · change Equivalent (m 1).1 (variables plan m .lower 0)
      rw [(var_bounds m).1]
      exact ⟨subtype_refl _,subtype_refl _⟩
    · cases List.mem_singleton.mp rest
      change Equivalent (m 1).1 (variables plan m .upper 0)
      rw [(var_bounds m).2]
      exact ⟨subtype_refl _,subtype_refl _⟩
  · intro clause member signature
    cases List.mem_singleton.mp member
    rw [child_schema]
    refine ⟨?_,?_⟩
    · change child.Holds m
      intro i
      rw [child_args,child_data.2]
      exact ⟨subtype_refl _,subtype_refl _⟩
    · intro entry member
      cases List.mem_singleton.mp member
      change Equivalent (m 1).1 (variables plan m .actual 0)
      rw [var_actual]
      exact ⟨subtype_refl _,subtype_refl _⟩
  · unfold Outputs
    rw [emitted_schema]
    intro entry member
    rcases List.mem_cons.mp member with rfl|rest
    · change Equivalent (m 1).1 (variables plan m .lower 0)
      rw [(var_bounds m).1]
      exact ⟨subtype_refl _,subtype_refl _⟩
    · cases List.mem_singleton.mp rest
      change Equivalent (m 1).1 (variables plan m .upper 0)
      rw [(var_bounds m).2]
      exact ⟨subtype_refl _,subtype_refl _⟩

end Yulang.GeneralDepthTwoRootPlan300
