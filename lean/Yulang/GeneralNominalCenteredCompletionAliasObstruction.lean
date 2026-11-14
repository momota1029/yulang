import Yulang.GeneralNominalCenteredCompletionAliasLocal

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

/-! A source-formed, inhabited, merge-closed selection without Joint.
This statement concerns the reachable snapshot; stability is not assumed. -/
namespace Yulang.GeneralNominalCenteredCompletionAliasObstruction
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCenters GeneralNominalCenteredSteps CommonNominalFullCarrier
open GeneralNominalCenteredCompletionAliasSource
open GeneralNominalCenteredCompletionAliasTrace
open GeneralNominalCenteredCompletionAliasLocal
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

theorem requested_branch_incompatible (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models finish.erased.current m) :
    ¬ GeneralNominalJointCandidates.BranchAt registry finish.erased.current (child true) 2 m := by
  rintro ⟨decl,visible,check,key,role,_,bounds,located,branch⟩
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl
  · cases key
  · have same : bounds = [((1 : Fin 2),(1 : Fin 2))] := Option.some.inj located.symm
    subst bounds
    have seen := (branch.2.2.1 (.source output,.nominal 0 1) requested_nominal).2 _ (.source output)
    obtain ⟨arguments,_,equivalent⟩ := seen
    exact GeneralNominalPeelingOrigins.base_not_nominal .int 0 arguments
      (subtype_trans (output_int m valid).2 equivalent.1)

theorem no_joint : ¬ GeneralNominalJointCandidates.Joint registry finish.erased.current focus 2 := by
  rintro ⟨_,m,valid,_,all⟩
  apply requested_branch_incompatible m valid
  apply all (rawSite true)
  refine ⟨?_,child_alias false true⟩
  change rawSite true ∈ before.erased.current.sites
  rw [raw_sites]; simp

theorem no_completion (candidate : Plan roles)
    (frame : GeneralNominalCenteredSelectedCompletion.Frame registry finish focus 2 descendants candidate) :
    ¬ GeneralNominalCenteredSelectedCompletion.Completion registry finish candidate := by
  intro complete
  apply no_joint
  have joint := complete.1
  rw [frame.occurrence_eq,frame.key_eq] at joint
  exact joint

theorem generated_focus : GeneralNominalSaturationState.Generated finish.erased.current root focus := by
  apply GeneralNominalSaturationState.Generated.child .root
  change (root,focus) ∈ [] ++ children.map (fun c => (root,c))
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨focus,?_,rfl⟩
  rw [children_exact]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem reachable_selected_without_joint :
    (GeneralNominalCenteredAdministrativeLocal.boundary roles).Checked registry ∧
    B4TargetV5.Reachable (GeneralNominalCenteredAdministrativeLocal.boundary roles) registry root finish ∧
    Models finish exampleModel ∧
    GeneralNominalSaturationState.Generated finish.erased.current root focus ∧
    GeneralNominalCenteredAdministrativeLocal.Local registry finish focus (.selected 2 descendants) ∧
    descendants ≠ [] ∧
    ¬ GeneralNominalJointCandidates.Joint registry finish.erased.current focus 2 :=
  ⟨⟨rfl,registry_checked⟩,ground_reachable,finish_model,generated_focus,child_selected,descendants_nonempty,no_joint⟩

theorem reachable_frame_without_completion :
    ∃ candidate, GeneralNominalCenteredSelectedCompletion.Frame registry finish focus 2 descendants candidate ∧
      ¬ GeneralNominalCenteredSelectedCompletion.Completion registry finish candidate := by
  obtain ⟨candidate,frame⟩ := GeneralNominalCenteredSelectedCompletion.selected_frame
    ground_reachable generated_focus child_selected
  exact ⟨candidate,frame,no_completion candidate frame⟩

end Yulang.GeneralNominalCenteredCompletionAliasObstruction
