import Yulang.GeneralLatePeerDirectInstall311

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralLatePeerRoutePlan311
open GeneralGeneratedNestedSource299 (snapshot context listDescriptor)
open GeneralLatePeerSource311 (compiled route route_checked makePeer)
open GeneralLatePeerRoot311 (branch route_args route_center)
open GeneralNominalExamples (interpretation)
open GeneralDeclarationExamples (roles)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalCenters
open GeneralNominalVersionedPlans231
open GeneralNominalVersionedFrame231 (binder capture childSite)
open GeneralNominalRecursiveInspection
open GeneralNominalUnaryCaptureFacts

abbrev middle := branch.occurrence
abbrev middlePacket : GeneralNominalSaturationState.Packet roles :=
  ⟨compiled,context,branch.observed,route,route_checked,[(1,1)]⟩
abbrev plan : Plan roles := ⟨middlePacket,branch,rfl⟩

theorem query : GeneralNominalInspection.queries snapshot interpretation route = [.nominal 0 [.variables [0]]] :=
  by
    simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,
      GeneralDeclarationPatterns.normalize,GeneralNominalInspection.translate,interpretation]

theorem middle_report : GeneralNominalRecursiveCandidates.report context route [(1,1)] =
    captured snapshot 1 0 0 (2,2) :=
  report_exact context route 1 (listDescriptor 2) rfl 0 (2,2) rfl query

abbrev origin : Origin := .nominal (.source 1) 0 0
abbrev child : Site roles := childSite plan makePeer
  (route_checked.signature.2.2.2 _ (by simp))

theorem bindings : middlePacket.bindings = [(0,(2,2))] := by
  change GeneralNominalRecursiveInspection.bindings snapshot
    (GeneralNominalRecursiveCandidates.report context route [(1,1)]) = _
  rw [middle_report]; rfl

theorem center : binder plan 0 = 2 := by decide +kernel

theorem captured : (capture middlePacket).inputs 0 = (2,2) := by decide +kernel

theorem head_schema : plan.headSchema =
    ⟨[⟨0,origin,.actual⟩],[(.source 1,.nominal 0 1)],false⟩ := by
  unfold Plan.headSchema
  rw [query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,List.ofFn_succ,origin,route_center]

theorem emitted_schema : emittedSchema plan =
    ⟨[⟨2,.lower,.variable 0⟩,⟨2,.upper,.variable 0⟩],false⟩ := by
  change GeneralNominalCenteredHeadMatSchemas.generated _ _ (emittedRequests middlePacket) = _
  unfold emittedRequests GeneralCanonicalChildOrder.canonicalEmit
  unfold GeneralNominalVersionedFrame231.capture GeneralNominalVersionedFrame231.frame
  rw [bindings]
  simp only [GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
    List.mergeSort_singleton]
  have noRoot : GeneralNominalMaterialization.rootRequests route middle = [] := by
    simp [GeneralNominalMaterialization.rootRequests]
  rw [show GeneralNominalMaterialization.rootRequests middlePacket.declaration
    middlePacket.site.occurrence = [] from noRoot]
  rfl

theorem emitted_sites : GeneralNominalVersionedChildren232.emitted plan = [child] := by
  have length : (GeneralNominalVersionedChildren232.emitted plan).length = 1 :=
    GeneralNominalVersionedChildren232.emitted_length _
  have seen : child ∈ GeneralNominalVersionedChildren232.emitted plan := by
    unfold GeneralNominalVersionedChildren232.emitted
    have member : makePeer ∈
        GeneralCanonicalChildOrder.canonicalRequirements plan.packet.declaration.requirements :=
      (GeneralCanonicalChildOrder.canonicalRequirements_perm _).mem_iff.mp (List.mem_singleton_self _)
    exact List.mem_map.mpr ⟨⟨_,member⟩,List.mem_attach _ _,rfl⟩
  obtain ⟨one,view⟩ := List.length_eq_one_iff.mp length
  rw [view] at seen ⊢
  cases List.mem_singleton.mp seen
  rfl

theorem child_args : ∀ i, child.occurrence.demand.arguments i = (2,2) := by
  intro i
  have iz : i.val = 0 := by have h := i.isLt; change i.val < 1 at h; omega
  have e : i = ⟨0,by decide +kernel⟩ := Fin.ext iz
  subst i
  decide +kernel

theorem child_data : ∀ i, child.center i = 2 := by
  intro i
  have iz : i.val = 0 := by have h := i.isLt; change i.val < 1 at h; omega
  have e : i = ⟨0,by decide +kernel⟩ := Fin.ext iz
  subst i
  exact center

theorem middle_children : GeneralNominalVersionedFrame231.children middlePacket = [child.occurrence] := by
  rw [← GeneralNominalVersionedChildren232.emitted_occurrences plan,emitted_sites]
  rfl

theorem child_schema : childSchema plan makePeer
    (route_checked.signature.2.2.2 _ (by simp)) = ⟨[⟨2,.actual,.variable 0⟩],false⟩ := by
  unfold childSchema childRequests
  simp only [makePeer,List.ofFn_succ,List.ofFn_zero]
  change GeneralNominalCenteredHeadMatSchemas.generated _ _ [⟨.var 0,child.center _,.actual⟩] = _
  rw [child_data]
  rfl

theorem var_actual (m : Assignment) : variables plan m .actual 0 = (m 2).1 := by
  unfold variables
  rw [center]
  rfl

theorem var_bounds (m : Assignment) :
    variables plan m .lower 0 = (m 2).1 ∧ variables plan m .upper 0 = (m 2).1 := by
  unfold variables
  rw [captured]
  exact ⟨rfl,rfl⟩

theorem update_support (m : Assignment) (valid : GeneralNominalState.Models snapshot m) :
    Ordinary middlePacket m ∧ ProjectionModels snapshot (GeneralNominalPacketSupport.report middlePacket) m := by
  have fact := GeneralNominalUnaryCaptureFacts.private_models context compiled middle route 1
    (listDescriptor 2) rfl 0 rfl (2,2) rfl query m valid
  have raw := (GeneralNominalPacketSupport.private_exact middlePacket m).mp fact.1
  refine ⟨⟨raw.2.1,?_,raw.2.2.2⟩,fact.2⟩
  unfold GeneralNominalVersionedAllocation231.merges
  rw [bindings]
  intro atom present
  cases present

theorem input_holds (m : Assignment) : plan.input.Holds m := by
  intro i
  change GeneralNominalCaptureMerges.Fits m (branch.occurrence.demand.arguments i)
    (m (branch.center i)).1
  rw [route_args,route_center]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem holds (m : Assignment) (valid : GeneralNominalState.Models snapshot m) : Holds plan m := by
  have argument := nominal_argument_bounds snapshot m valid 1 (listDescriptor 2) rfl 0 (2,2) rfl
  have projected : GeneralNominalOriginTerms.Same m origin (.source 2) := by
    refine ⟨argument.1,⟨_,.source 2⟩,?_⟩
    intro a b one two
    cases two
    exact ⟨(argument.2 a one).2,(argument.2 a one).1⟩
  have supported := update_support m valid
  refine ⟨valid,⟨supported.1,supported.2,input_holds m,?_,?_,?_,?_⟩,?_⟩
  · intro name used
    have zero : name = 0 := by
      rcases used with head | ⟨clause,member,used⟩
      · simpa [GeneralDeclarations.Declaration.inputNames,GeneralDeclarationPatterns.variablesArgs,
          GeneralDeclarationPatterns.Pattern.variables,GeneralDeclarationPatterns.normalizeArgs,
          GeneralDeclarationPatterns.normalize,route] using head
      · cases List.mem_singleton.mp member
        simpa [GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables,
          GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
          makePeer] using used
    subst name
    change GeneralNominalCaptureMerges.Fits m ((capture middlePacket).inputs 0) (m (binder plan 0)).1
    rw [GeneralLatePeerRoutePlan311.captured,center]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · rw [head_schema]
    constructor
    · intro entry member
      cases List.mem_singleton.mp member
      obtain ⟨arguments,fit,equals⟩ := valid.2.1 1 (listDescriptor 2) rfl
      refine ⟨⟨_,.source 1⟩,?_⟩
      intro actual seen
      cases seen
      have length : arguments.length = 1 := by
        change GeneralNominalState.FitsAll snapshot.base m [.type (2,2)] arguments at fit
        cases fit with | cons _ tail => cases tail; rfl
      exact ⟨arguments,length,equals⟩
    · intro entry member
      cases List.mem_singleton.mp member
      simpa only [ite_true,center] using projected
  · rw [emitted_schema]
    intro entry member _
    rcases List.mem_cons.mp member with rfl|rest
    · change Equivalent (m 2).1 (variables plan m .lower 0)
      rw [(var_bounds m).1]
      exact ⟨subtype_refl _,subtype_refl _⟩
    · cases List.mem_singleton.mp rest
      change Equivalent (m 2).1 (variables plan m .upper 0)
      rw [(var_bounds m).2]
      exact ⟨subtype_refl _,subtype_refl _⟩
  · intro clause member signature
    cases List.mem_singleton.mp member
    rw [child_schema]
    refine ⟨?_,?_⟩
    · change child.Holds m
      intro i
      rw [child_args,child_data]
      exact ⟨subtype_refl _,subtype_refl _⟩
    · intro entry member
      cases List.mem_singleton.mp member
      change Equivalent (m 2).1 (variables plan m .actual 0)
      rw [var_actual]
      exact ⟨subtype_refl _,subtype_refl _⟩
  · unfold Outputs
    rw [emitted_schema]
    intro entry member
    rcases List.mem_cons.mp member with rfl|rest
    · change Equivalent (m 2).1 (variables plan m .lower 0)
      rw [(var_bounds m).1]
      exact ⟨subtype_refl _,subtype_refl _⟩
    · cases List.mem_singleton.mp rest
      change Equivalent (m 2).1 (variables plan m .upper 0)
      rw [(var_bounds m).2]
      exact ⟨subtype_refl _,subtype_refl _⟩

end Yulang.GeneralLatePeerRoutePlan311
