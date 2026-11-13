import Yulang.GeneralDictionaryFiniteObservedExampleNonterminalClosure

/-! Every actual support update is excluded at the reached named-output state. -/
namespace Yulang.GeneralDictionaryFiniteObservedExampleNonterminalStable
open GeneralDictionaryFiniteObservedExampleNonterminal GeneralDictionaryFiniteObservedExampleNonterminalInstallation
open GeneralDictionaryFiniteObservedExampleNonterminalEvidence GeneralDictionaryFiniteObservedExampleNonterminalFinalEvidence
open GeneralDictionaryFiniteObservedExampleNonterminalClosure
open GeneralNominalExamples (intDisplay)
open GeneralDictionaryFiniteObservedExample (model descriptor)
open GeneralDeclarationExamples (roles)
open GeneralNominalSaturationState GeneralDictionaryRecursiveEvidence
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection

private theorem branch_parent (m : GeneralNominalCommonBridge.Assignment) (valid : Models installed.current m) :
    BranchModels registry current root declaration checked [((0 : Fin 2),(0 : Fin 2))] m := by
  obtain ⟨decl,visible,check,key,role,bounds,located,_,_,_,_,branch⟩ := final_parent_instance m valid
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl
  · have found : arguments current root = some [((0 : Fin 2),(0 : Fin 2))] := rfl
    have eq := Option.some.inj (located.symm.trans found)
    subst bounds
    exact branch
  · contradiction

private theorem branch_child (m : GeneralNominalCommonBridge.Assignment) (valid : Models installed.current m) :
    BranchModels registry current child intDisplay GeneralDictionaryFiniteObservedExampleNonterminal.int_display_checked
      [((1 : Fin 2),(1 : Fin 2))] m := by
  obtain ⟨decl,visible,check,key,role,bounds,located,_,_,_,_,branch⟩ := final_child_instance m valid
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl
  · contradiction
  · have found : arguments current child = some [((1 : Fin 2),(1 : Fin 2))] := by change arguments context child = _; exact child_arguments
    have eq := Option.some.inj (located.symm.trans found)
    subst bounds
    exact branch

theorem installs_committed (p : Packet roles)
    (reached : Generated installed.current root p.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry installed.current p) :
    GeneralNominalFeedbackSteps.Committed installed.current p := by
  rcases generated_cases _ reached with same | same
  · have selected := enabled.2.1
    rw [same] at selected
    have agreement := GeneralDictionarySelectedInstanceCoherence.instance_selected registry installed.current root model
      declaration.id p.declaration.id children p.children (final_parent_instance model (models_of_source model source_models)) selected
    have key := agreement.1.symm
    have childrenEq := agreement.2.symm
    constructor
    · intro m valid
      rcases p with ⟨preg,pctx,psite,pdecl,pchecked,pbounds⟩
      have reg := enabled.1.1
      have ctx := enabled.1.2.1
      dsimp only at reg ctx
      subst preg; subst pctx
      have visible := enabled.1.2.2.2.1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
      rcases visible with decl | decl
      · subst pdecl
        have found := enabled.1.2.2.2.2.2.1
        change arguments current psite.occurrence = some pbounds at found
        change psite.occurrence = root at same
        rw [same] at found
        have located : arguments current root = some [((0 : Fin 2),(0 : Fin 2))] := rfl
        have equal := Option.some.inj (found.symm.trans located)
        subst pbounds
        change BranchModels registry current psite.occurrence declaration pchecked [((0 : Fin 2),(0 : Fin 2))] m
        rw [same]
        exact branch_parent m valid
      · subst pdecl; cases key
    · intro c member
      rw [childrenEq,children_exact] at member
      have eq := List.mem_singleton.mp member
      subst c
      rw [same,edges_exact]
      exact List.mem_singleton_self _
  · have selected := enabled.2.1
    rw [same] at selected
    have agreement := GeneralDictionarySelectedInstanceCoherence.instance_selected registry installed.current child model
      intDisplay.id p.declaration.id [] p.children (final_child_instance model (models_of_source model source_models)) selected
    have key := agreement.1.symm
    have childrenEq := agreement.2.symm
    constructor
    · intro m valid
      rcases p with ⟨preg,pctx,psite,pdecl,pchecked,pbounds⟩
      have reg := enabled.1.1
      have ctx := enabled.1.2.1
      dsimp only at reg ctx
      subst preg; subst pctx
      have visible := enabled.1.2.2.2.1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
      rcases visible with decl | decl
      · subst pdecl; cases key
      · subst pdecl
        have found := enabled.1.2.2.2.2.2.1
        change arguments current psite.occurrence = some pbounds at found
        change psite.occurrence = child at same
        rw [same] at found
        have located : arguments current child = some [((1 : Fin 2),(1 : Fin 2))] := by change arguments context child = _; exact child_arguments
        have equal := Option.some.inj (found.symm.trans located)
        subst pbounds
        change BranchModels registry current psite.occurrence intDisplay pchecked [((1 : Fin 2),(1 : Fin 2))] m
        rw [same]
        exact branch_child m valid
    · intro c member
      rw [childrenEq] at member
      cases member

theorem feedback_stable : GeneralNominalFeedbackSteps.Stable registry installed.current root := by
  intro focus generated next update
  cases update with
  | enqueue focus _ absent =>
    rcases generated_cases focus generated with same | same
    · exact absent (GeneralNominalDemandMerging.pointSite root) (by rw [sites_exact]; simp) same.symm
    · exact absent (GeneralNominalFeedbackSites.childSite packet child) (by rw [sites_exact]; simp) same.symm
  | install p enabled novel => exact novel (installs_committed p generated enabled)
  | merge first last one two same novel => exact novel (merges_closed first last one two same)
  | refresh _ next certificate id _ unknown known =>
    by_cases zero : id = 0
    · subst id
      exact unknown ⟨(0 : Fin 2),rfl,Or.inr ⟨descriptor,rfl⟩⟩
    · by_cases one : id = 1
      · subst id
        exact unknown ⟨(1 : Fin 2),rfl,Or.inl (by decide +kernel)⟩
      · exact refresh_large_unknown next certificate id (by omega) known
  | equate _ first last _ _ equal novel =>
    exact novel (fun m valid => equal m (context_complete m valid))

theorem stable : GeneralNominalSupportSteps.Stable registry installed root := by
  intro focus generated next update
  have old := GeneralNominalSupportSteps.at_old update
  exact (GeneralNominalReobservationSteps.stable_of_pointClosed feedback_stable point_closed) focus generated _ old

theorem stable_reachable_named_dictionary :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root installed ∧
    Models installed.current model ∧ GeneralNominalSupportSteps.Stable registry installed root ∧
    root.demand.outputs ≠ [] ∧ children.length = 1 ∧
    ∀ assignment, Models installed.current assignment → Evidence registry current assignment root payload :=
  ⟨installed_reachable,models_of_source model source_models,stable,named_request_present,actual_children_count,final_evidence⟩
end Yulang.GeneralDictionaryFiniteObservedExampleNonterminalStable
