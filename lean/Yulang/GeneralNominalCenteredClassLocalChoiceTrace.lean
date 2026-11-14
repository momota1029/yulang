import Yulang.GeneralNominalCenteredClassLocalChoiceSource
import Yulang.GeneralNominalCenteredMergeAvailability

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace Yulang.GeneralNominalCenteredClassLocalChoiceTrace
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalRecursiveInspection
open GeneralNominalCenters GeneralNominalCenteredSteps CommonNominalFullCarrier
open GeneralNominalCenteredClassLocalChoiceSource
open GeneralNominalExamples (context state listDescriptor interpretation state_models)

abbrev origin : Origin := .nominal (.source 0) 0 0
noncomputable abbrev before := GeneralNominalCenteredSteps.install start plan []

theorem binder_zero : plan.binder 0 = 1 := by
  unfold Plan.binder GeneralNominalPacketSupport.capture
  change (if 0 ∈ parent.outputNames then _ else _) = _
  simp only [show ¬ 0 ∈ parent.outputNames from by decide +kernel,ite_false]
  rw [GeneralNominalCenteredClassLocalChoiceSource.bindings]
  rfl

theorem head_schema : plan.headSchema =
    ⟨[⟨0,origin,.actual⟩],[(.source 0,.nominal 0 1)],false⟩ := by
  unfold Plan.headSchema
  rw [query]
  simp [GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.Schema.append,plan,rootSite,root,
    root,roles,GeneralDeclarationExamples.bareRole,List.ofFn_succ,origin]

def centerSite (which : Bool) : Site roles := ⟨child which,fun _ => 1⟩

theorem first_child : plan.childSite requested
    (parent_checked.signature.2.2.2 _ (by simp [parent])) = centerSite true := by
  unfold Plan.childSite centerSite
  congr 1
  · unfold GeneralNominalFeedbackSites.clauseChild GeneralNominalFeedbackSites.frame GeneralNominalAllocation.frame
    change GeneralDictionaryEmissionPlans.occurrence _ _ = _
    rw [show plan.packet = packet from rfl,GeneralNominalCenteredClassLocalChoiceSource.bindings]
    simp [GeneralDictionaryEmissionPlans.occurrence,GeneralDeclarationDemands.emit,
      GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,GeneralDeclarationDemands.outputTarget,
      GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences,
      GeneralDeclarationPatterns.normalize,child,packet,root,output,GeneralNominalAllocation.allocation,GeneralNominalAllocation.origin,GeneralNominalDemandMerging.pointSite,
      requested,plain]

  · funext index
    have zero : index.val = 0 := by have bound := index.isLt; change index.val < 1 at bound; omega
    simpa only [zero,requested,List.getElem_cons_zero,
      Plan.emittedCenter,GeneralDeclarationPatterns.normalize] using binder_zero

theorem second_child : plan.childSite plain
    (parent_checked.signature.2.2.2 _ (by simp [parent])) = centerSite false := by
  unfold Plan.childSite centerSite
  congr 1
  · unfold GeneralNominalFeedbackSites.clauseChild GeneralNominalFeedbackSites.frame GeneralNominalAllocation.frame
    change GeneralDictionaryEmissionPlans.occurrence _ _ = _
    rw [show plan.packet = packet from rfl,GeneralNominalCenteredClassLocalChoiceSource.bindings]
    simp [GeneralDictionaryEmissionPlans.occurrence,GeneralDeclarationDemands.emit,
      GeneralDeclarationDemands.childDemand,GeneralDeclarationDemands.inputInterval,GeneralDeclarationDemands.outputTarget,
      GeneralNominalAllocation.capture,GeneralNominalAllocation.occurrences,
      GeneralDeclarationPatterns.normalize,child,packet,root,output,GeneralNominalAllocation.allocation,GeneralNominalAllocation.origin,GeneralNominalDemandMerging.pointSite,
      requested,plain]

  · funext index
    have zero : index.val = 0 := by have bound := index.isLt; change index.val < 1 at bound; omega
    simpa only [zero,plain,List.getElem_cons_zero,
      Plan.emittedCenter,GeneralDeclarationPatterns.normalize] using binder_zero

theorem emitted : plan.emitted = [centerSite true,centerSite false] := by
  change [plan.childSite requested _,plan.childSite plain _] = _
  rw [first_child,second_child]

private theorem fit_length {base : GeneralSourceState.State} {m : GeneralNominalCommonBridge.Assignment}
    {parameters : List (GeneralNominalState.Parameter base.slots)} {values : List CommonNominalFullCarrier.Argument}
    (fit : GeneralNominalState.FitsAll base m parameters values) : parameters.length = values.length := by
  induction fit with
  | nil => rfl
  | cons head rest ih => exact congrArg Nat.succ ih

theorem equations (m : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models (state true) m)
    (out : Equivalent (m output).1 (.base .int)) : plan.Equations m := by
  have seen := nominal_argument_bounds (state true) m valid 0 listDescriptor rfl 0 (1,1) rfl
  have actual : GeneralNominalOriginTerms.Same m origin (.source 1) := by
    refine ⟨seen.1,⟨_,.source 1⟩,?_⟩
    intro a b ha hb
    cases hb
    exact ⟨(seen.2 a ha).2,(seen.2 a ha).1⟩
  refine ⟨point_root_holds _ root (fun _ => rfl) m,?_,?_,?_,?_,?_⟩
  · intro name used
    have zero : name = 0 := by
      rcases used with head | ⟨clause,member,used⟩
      · simpa [packet,parent,GeneralDeclarations.Declaration.inputNames,GeneralDeclarationPatterns.variablesArgs,
          GeneralDeclarationPatterns.Pattern.variables,GeneralDeclarationPatterns.normalizeArgs,
          GeneralDeclarationPatterns.normalize] using head
      · simp only [packet,parent,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl <;>
          simpa [GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables,
            GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
            plain,requested] using used
    subst name
    rw [binder_zero]
    change GeneralNominalCaptureMerges.Fits m ((GeneralNominalPacketSupport.capture packet).inputs 0) _
    unfold GeneralNominalPacketSupport.capture
    rw [GeneralNominalCenteredClassLocalChoiceSource.bindings]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · rw [head_schema]
    constructor
    · intro entry member
      cases List.mem_singleton.mp member
      have nominal := GeneralNominalState.nominal_models (state true) m valid 0 listDescriptor rfl
      obtain ⟨arguments,fit,equal⟩ := nominal
      exact ⟨⟨_,.source 0⟩,by intro value observed; cases observed; exact ⟨arguments,by exact (fit_length fit).symm,equal⟩⟩
    · intro entry member
      cases List.mem_singleton.mp member
      simp only [Plan.SchemaHolds,ite_true]
      rw [binder_zero]
      exact actual
  · rw [show plan.packet = packet from rfl,input_schema]
    exact ⟨(by intro _ impossible; cases impossible),(by intro _ impossible; cases impossible)⟩
  · rw [show plan.packet = packet from rfl,named_schema]
    refine ⟨?_,by intro _ impossible; cases impossible⟩
    intro entry member; cases List.mem_singleton.mp member
    exact ⟨⟨_,.source _⟩,by intro actual seen; cases seen; exact out⟩
  · intro clause member signature
    change clause ∈ parent.requirements at member
    simp only [parent,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals
      constructor
      · first | rw [first_child] | rw [second_child]
        intro index
        exact ⟨subtype_refl _,subtype_refl _⟩
      · change plan.SchemaHolds (GeneralNominalMaterialization.generated _ _
          [⟨.var 0,plan.binder 0,.actual⟩]) m
        simp only [GeneralNominalMaterialization.generated,GeneralNominalMaterialization.schema,
          GeneralNominalMaterialization.Schema.append,GeneralNominalInspection.translate,
          GeneralDeclarationPatterns.normalize,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,
          List.append_nil,Plan.SchemaHolds]
        refine ⟨(by intro _ impossible; cases impossible),?_⟩
        intro entry member
        cases List.mem_singleton.mp member
        exact GeneralNominalOriginTerms.source_self m _


theorem initial_acyclic (observed : Origin) : ¬ Cyclic start observed :=
  GeneralNominalCenteredSteps.initial_acyclic _ _ initial_feedback_acyclic observed

theorem cselected : GeneralNominalCenteredBoundary.Local registry start root (.selected 1 children) := by
  apply GeneralNominalCenteredBoundary.selected_of_old selected initial_acyclic
  exact GeneralNominalCenteredSupport.legacy_decision
    (GeneralNominalSharedPositive.initial_decision _ _ _ _ [] source_decisions)

theorem guard : PacketGuard start plan [] := by
  apply (GeneralNominalCenteredInspection.selected_guard_reduction plan cselected enabled (List.mem_singleton_self _) []).mpr
  exact ⟨GeneralNominalValueSupport.source_packet _ _ raw_guard,
    exampleModel,(point_initial_models _ _ (fun _ => rfl) exampleModel).mpr (state_models true),
    branch_model,equations exampleModel (state_models true)
      (by simp only [GeneralNominalExamples.model,output_nonzero,ite_false]; exact ⟨subtype_refl _,subtype_refl _⟩)⟩

theorem first_step : Step registry root start before :=
  ⟨root,.root,.install plan [] enabled novel guard⟩

theorem initial_source : InitialSource registry root start := GeneralNominalCenteredSteps.initial_source source

theorem before_model : Models before exampleModel :=
  (GeneralNominalCenteredSteps.install_models (plan := plan) (state := start) (support := []) rfl _).mpr
    ⟨(point_initial_models _ _ (fun _ => rfl) exampleModel).mpr (state_models true),branch_model,equations exampleModel (state_models true)
      (by simp only [GeneralNominalExamples.model,output_nonzero,ite_false]; exact ⟨subtype_refl _,subtype_refl _⟩)⟩

noncomputable abbrev rawSite (which : Bool) := GeneralNominalSharedEmission.childSite packet (child which)

theorem raw_sites : before.erased.current.sites =
    [GeneralNominalDemandMerging.pointSite root,rawSite true,rawSite false] := by
  change [GeneralNominalDemandMerging.pointSite root] ++ children.map _ = _
  rw [children_exact]; rfl

theorem center_sites : before.sites = [plan.input,centerSite true,centerSite false] := by
  change [plan.input] ++ plan.emitted = _
  rw [emitted]; rfl

theorem child_generated (which : Bool) : GeneralNominalSaturationState.Generated before.erased.current root (child which) := by
  apply GeneralNominalSaturationState.Generated.child .root
  change (root,child which) ∈ [] ++ children.map (fun c => (root,c))
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨child which,?_,rfl⟩
  rw [children_exact]; cases which <;> simp

theorem child_not_aliased : ¬ GeneralNominalSaturationState.Alias before.erased.current
    (child true).identity (child false).identity := by
  have equal : ∀ a b, GeneralNominalSaturationState.Alias before.erased.current a b → a = b := by
    intro a b related
    induction related with
    | refl => rfl
    | edge member => cases member
    | symm _ ih => exact ih.symm
    | trans _ _ left right => exact left.trans right
  intro related
  have same := (GeneralNominalIdentities.source_identity (state true).seed _ _).mp (equal _ _ related)
  have impossible := congrArg (fun x : GeneralNominalIdentities.Origin => x.2.2.2.1) same
  contradiction

noncomputable abbrev finish := GeneralNominalCenteredSteps.merge before (centerSite true) (centerSite false) []

theorem second_step : Step registry root before finish := by
  apply GeneralNominalCenteredMergeAvailability.same_names_step
  · rw [center_sites]; simp
  · rw [center_sites]; simp
  · exact child_generated true
  · rfl
  · rfl
  · exact child_not_aliased

theorem finish_model : Models finish exampleModel := by
  refine ⟨(GeneralNominalSaturationState.merge_models ..).mpr ⟨before_model.1,?_⟩,before_model.2⟩
  intro atom member
  cases member

theorem ground : GeneralNominalGroundAccessibility.GroundRoots (context true) root [.app 0 [.app 2 []]] := by
  refine ⟨rfl,?_⟩
  intro index
  have zero : index.val = 0 := by have bound := index.isLt; change index.val < 1 at bound; omega
  simp only [zero]
  refine ⟨GeneralNominalGroundExamples.listTerm,⟨?_,rfl,⟨trivial,fun _ => ⟨trivial,fun i => Fin.elim0 i⟩⟩⟩,?_⟩
  · simp [GeneralDeclarationPatterns.normalize,GeneralDeclarationPatterns.normalizeArgs,
      GeneralNominalInspection.translate,GeneralNominalExamples.interpretation,
      GeneralNominalCompoundReadback.quote,GeneralNominalGroundExamples.listTerm,
      GeneralNominalGroundExamples.intTerm,List.ofFn_succ,GeneralNominalOriginTerms.arity,
      GeneralNormalizedObservation.Shape.arity]
  intro m valid
  exact GeneralNominalPeelingExamples.ground m valid

theorem ground_reachable : B4TargetV5.Reachable
    (GeneralNominalCenteredAdministrativeLocal.boundary roles) registry root finish :=
  ⟨start,⟨context true,[.app 0 [.app 2 []]],source,(fun _ => rfl),ground,rfl⟩,
    .tail (.tail .refl first_step) second_step⟩

theorem output_int (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models finish.erased.current m) : Equivalent (m output).1 (.base .int) := by
  have held := valid.2.1 packet (by change packet ∈ [packet]; simp)
  have tests := held.2.2.1
  change ∀ entry ∈ (GeneralNominalPacketSupport.namedSchema packet).tests, _ at tests
  rw [named_schema] at tests
  exact (tests (.source output,.scalar .int) (List.mem_singleton_self _)).2 _ (.source output)

end Yulang.GeneralNominalCenteredClassLocalChoiceTrace
