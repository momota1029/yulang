import Yulang.GeneralNominalCenteredClassLocalChoiceLocal
import Yulang.GeneralNominalCenteredClassLocalProduction

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-! The class keeps one jointly compatible implementation while the frozen
per-occurrence installation guard still sees two candidates. -/
namespace Yulang.GeneralNominalCenteredClassLocalChoiceObstruction
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCenters GeneralNominalCenteredSteps CommonNominalFullCarrier
open GeneralNominalCenteredClassLocalChoiceSource GeneralNominalCenteredClassLocalChoiceTrace
open GeneralNominalCenteredClassLocalChoiceLocal
open GeneralNominalExamples (context state interpretation)

theorem requested_nominal : (.source output,.nominal 0 1) ∈
    (generated registry current (child true) childDeclaration child_checked [((1 : Fin 2),(1 : Fin 2))]).tests := by
  unfold generated GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [canonical_child]
  simp [GeneralNominalMaterialization.rootRequests,
    GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,
    GeneralNominalMaterialization.emissionRequests,GeneralNominalMaterialization.inputRequests,
    List.ofFn_zero,GeneralNominalMaterialization.generated,child,childDeclaration,leaf,roles,
    normalize,normalizeArgs,GeneralNominalInspection.translate,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.Schema.append,
    show current.state.constructors = GeneralDeclarationExamples.constructors from rfl,
    show current.interpretation = interpretation from rfl,interpretation]

theorem no_bad_joint : ¬ GeneralNominalJointCandidates.Joint registry finish.erased.current focus 2 := by
  rintro ⟨_,m,valid,_,all⟩
  have requested := all (rawSite true) ⟨?_,child_alias false true⟩
  · obtain ⟨decl,visible,check,key,role,_,bounds,located,branch⟩ := requested
    simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
    rcases visible with rfl | rfl | rfl
    · cases key
    · have same : bounds = [((1 : Fin 2),(1 : Fin 2))] := Option.some.inj located.symm
      subst bounds
      have seen := (branch.2.2.1 (.source output,.nominal 0 1) requested_nominal).2 _ (.source output)
      obtain ⟨arguments,_,equivalent⟩ := seen
      exact GeneralNominalPeelingOrigins.base_not_nominal .int 0 arguments
        (subtype_trans (output_int m valid).2 equivalent.1)
    · cases key
  · change rawSite true ∈ before.erased.current.sites
    rw [raw_sites]; simp

theorem good_requested_schema : generated registry current (child true) goodDeclaration good_checked
    [((1 : Fin 2),(1 : Fin 2))] = { tests := [(.source output,.scalar .int)] } := by
  unfold generated GeneralNominalMaterialization.requests GeneralCanonicalChildOrder.canonicalEmit
  simp only [canonical_good]
  simp [GeneralNominalMaterialization.rootRequests,
    GeneralDeclarationDemands.emitAll,GeneralDeclarationDemands.emit,
    GeneralNominalMaterialization.emissionRequests,GeneralNominalMaterialization.inputRequests,
    List.ofFn_zero,GeneralNominalMaterialization.generated,child,goodDeclaration,leaf,roles,
    normalize,normalizeArgs,GeneralNominalInspection.translate,GeneralNominalMaterialization.schema,
    GeneralNominalMaterialization.schemas,GeneralNominalMaterialization.Schema.append,
    show current.state.constructors = GeneralDeclarationExamples.constructors from rfl,
    show current.interpretation = interpretation from rfl,interpretation]

theorem good_requested_branch (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models finish.erased.current m) :
    BranchModels registry current (child true) goodDeclaration good_checked [((1 : Fin 2),(1 : Fin 2))] m := by
  refine ⟨?_,?_,?_⟩
  · unfold privateState
    rw [show report current goodDeclaration _ = report current childDeclaration _ from rfl,child_report]
    apply (GeneralNominalState.extend_models ..).mpr
    refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨valid.1,?_,?_⟩,?_⟩
    · simp [GeneralNominalRecursiveInspection.bindings,GeneralNominalAllocation.Compatible]
    · simp [GeneralNominalRecursiveInspection.bindings,GeneralNominalAllocation.merges,goodDeclaration,
        Declaration.inputNames,normalizeArgs,normalize,variablesArgs,Pattern.variables]
    · simp [selfChecks,PresenceNormalForm.All]
      exact subtype_refl _
  · rw [show report current goodDeclaration _ = report current childDeclaration _ from rfl,child_report]
    simp [ProjectionModels]
  · rw [good_requested_schema]
    simp only [GeneralNominalMaterialization.Models,List.not_mem_nil,false_implies,forall_const,and_true]
    refine ⟨?_,by simp⟩
    intro entry member
    cases List.mem_singleton.mp member
    exact ⟨⟨_,.source output⟩,by intro value observed; cases observed; exact output_int m valid⟩

theorem output_member : output ∈ GeneralNominalState.sources current.state := by
  have reserved : output ∈ GeneralNominalAllocation.reserved (state true) registry root.identity := by
    apply List.mem_map.mpr
    exact ⟨(100,1,5,30,0),by decide +kernel,rfl⟩
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ reserved)))

theorem requested_prepared : Prepared registry current (child true) goodDeclaration good_checked := by
  refine ⟨metadata,?_,fresh _,[((1 : Fin 2),(1 : Fin 2))],rfl,?_,?_,exampleModel,good_requested_branch exampleModel finish_model.1⟩
  · constructor
    · intro index; exact good_prepared.2.1.1 index
    · intro entry member
      cases List.mem_singleton.mp member
      exact output_member
  · change Finished (report current childDeclaration _)
    rw [child_report]; exact ⟨rfl,rfl,rfl⟩
  · refine ⟨?_,?_⟩
    · intro entry member
      cases List.mem_singleton.mp member
      exact ⟨⟨40,0,.app 2 []⟩,by simp [goodDeclaration],rfl⟩
    · rw [good_requested_schema]

theorem child_not_root (which : Bool) : (child which).identity ≠ root.identity := by
  have above := GeneralNominalIdentities.source_above_invocation (state true).seed (100,1,6,(if which then 10 else 11),0)
  change 100 < (child which).identity at above
  change (child which).identity ≠ 100
  omega

theorem no_root_alias : ¬ GeneralNominalSaturationState.Alias finish.erased.current focus.identity root.identity := by
  have invariant : ∀ a b, GeneralNominalSaturationState.Alias finish.erased.current a b → (a = root.identity ↔ b = root.identity) := by
    intro a b alias
    induction alias with
    | refl => exact Iff.rfl
    | edge member =>
      cases List.mem_singleton.mp member
      change (child true).identity = root.identity ↔ (child false).identity = root.identity
      exact ⟨fun h => False.elim (child_not_root true h),fun h => False.elim (child_not_root false h)⟩
    | symm _ ih => exact ih.symm
    | trans _ _ one two => exact one.trans two
  intro alias
  exact child_not_root false ((invariant _ _ alias).mpr rfl)

theorem good_joint : GeneralNominalJointCandidates.Joint registry finish.erased.current focus 3 := by
  have branch : GeneralNominalJointCandidates.BranchAt registry finish.erased.current focus 3 exampleModel :=
    ⟨goodDeclaration,by simp,good_checked,rfl,rfl,good_prepared,[((1 : Fin 2),(1 : Fin 2))],rfl,good_branch exampleModel finish_model.1.1⟩
  have requested : GeneralNominalJointCandidates.BranchAt registry finish.erased.current (child true) 3 exampleModel :=
    ⟨goodDeclaration,by simp,good_checked,rfl,rfl,requested_prepared,[((1 : Fin 2),(1 : Fin 2))],rfl,good_requested_branch exampleModel finish_model.1⟩
  refine ⟨?_,exampleModel,finish_model.1,branch,?_⟩
  · intro packet member alias
    cases List.mem_singleton.mp member
    exact False.elim (no_root_alias alias)
  · intro site related
    have member := related.1
    change site ∈ before.erased.current.sites at member
    rw [raw_sites] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact False.elim (no_root_alias related.2)
    · exact requested
    · exact branch

theorem class_selected : GeneralNominalCenteredClassLocalBoundary.Local registry finish focus (.selected 3 goodChildren) := by
  refine .selected class_safe ⟨⟨good_survivor,good_joint⟩,?_⟩
  intro key children candidate
  obtain ⟨_,decl,visible,check,identity,role,_⟩ := candidate.1
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · cases role
  · apply False.elim; apply no_bad_joint
    simpa only [← identity] using candidate.2
  · have same : key = 3 := identity.symm
    subst key
    exact ⟨rfl,survivor_children_functional registry registry_checked current focus 3 children goodChildren candidate.1 good_survivor⟩

theorem not_installable (candidate : Plan roles) (same : candidate.packet.site.occurrence = focus) :
    ¬ GeneralNominalCenteredBoundary.Installable registry finish candidate := by
  intro enabled
  have old := enabled.1.2.1
  rw [same] at old
  have impossible := GeneralNominalLocalBoundary.local_functional raw_ambiguous old
  cases impossible

theorem good_children_nonempty : goodChildren ≠ [] := by
  have count := GeneralCanonicalChildOrder.canonicalEmit_perm focus.identity goodDeclaration good_checked
    (GeneralNominalAllocation.capture current.state registry focus.identity goodDeclaration.id [])
    (GeneralNominalAllocation.allocation current.state registry focus.identity goodDeclaration.id)
  intro empty
  have size := congrArg List.length empty
  change (List.map _ (GeneralCanonicalChildOrder.canonicalEmit _ _ _ _ _)).length = 0 at size
  simp only [List.length_map,GeneralNominalAllocation.frame] at size
  rw [← count.length_eq,GeneralDeclarationDemands.emitAll_length] at size
  cases size

theorem generated_focus : GeneralNominalSaturationState.Generated finish.erased.current root focus := by
  apply GeneralNominalSaturationState.Generated.child .root
  change (root,focus) ∈ [] ++ children.map (fun c => (root,c))
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨focus,?_,rfl⟩
  rw [children_exact]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem reachable_class_selection_blocked :
    (GeneralNominalCenteredClassLocalBoundary.boundary roles).Checked registry ∧
    B4TargetV5.Reachable (GeneralNominalCenteredClassLocalBoundary.boundary roles) registry root finish ∧
    Models finish exampleModel ∧
    GeneralNominalSaturationState.Generated finish.erased.current root focus ∧
    GeneralNominalCenteredClassLocalBoundary.Local registry finish focus (.selected 3 goodChildren) ∧
    goodChildren ≠ [] ∧
    ∀ candidate : Plan roles, candidate.packet.site.occurrence = focus →
      ¬ GeneralNominalCenteredBoundary.Installable registry finish candidate :=
  ⟨⟨rfl,registry_checked⟩,ground_reachable,finish_model,generated_focus,class_selected,good_children_nonempty,not_installable⟩

end Yulang.GeneralNominalCenteredClassLocalChoiceObstruction
