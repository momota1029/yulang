import Yulang.GeneralNominalNonleafFinal194
import Yulang.GeneralDictionarySupportRecursiveClosure
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalNonleafStable194
open GeneralNominalNonleafPlan193 GeneralNominalNonleafInstallation193 GeneralNominalNonleafSafety193 GeneralNominalNonleafAdministrative193
open GeneralNominalExamples (registry displayRoot displayChild model)
open GeneralDeclarationExamples (roles display display_checked)
open GeneralDeclarations GeneralNominalCenters GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel

open GeneralNominalCenteredHeadCandidates
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalSaturationState (Generated Packet)

theorem edges : finish.core.erased.current.edges = [(displayRoot,displayChild)] := by
  change [] ++ plan.packet.children.map _ = _
  rw [children_exact]; rfl

theorem generated_cases (focus : GeneralSourceDictionaries.Occurrence roles)
    (generated : Generated finish.core.erased.current displayRoot focus) : focus = displayRoot ∨ focus = displayChild := by
  induction generated with
  | root => exact Or.inl rfl
  | child prior member ih =>
    rw [edges] at member
    exact Or.inr (congrArg Prod.snd (List.mem_singleton.mp member))
  | alias prior one two same ih =>
    rw [raw_sites] at two
    rcases List.mem_cons.mp two with rfl | rest
    · exact Or.inl rfl
    · cases List.mem_singleton.mp rest; exact Or.inr rfl

theorem raw_source (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models current.state assignment) :
    GeneralNominalState.Models (GeneralNominalExamples.state true) assignment := by
  have old := GeneralDictionarySupportRecursiveClosure.context_complete assignment valid
  exact ((GeneralNominalFeedbackSites.install_models
    GeneralDictionarySupportRecursiveExample.start.current packet
    (GeneralNominalFeedbackSites.emitted packet) rfl assignment).mp old).1.1

theorem context_complete (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models current.state assignment) : Models finish assignment :=
  (final_models_iff assignment).mpr (raw_source assignment valid)

theorem parent_branch (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models current.state assignment) :
    BranchModels registry current displayRoot display display_checked [((0 : Fin 2),(0 : Fin 2))] assignment := by
  have old := GeneralDictionarySupportRecursiveClosure.context_complete assignment valid
  obtain ⟨decl,visible,checked,key,role,bounds,located,_,_,_,_,branch⟩ :=
    GeneralDictionarySupportRecursiveExample.parent_instance assignment old
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · contradiction
  · have found : arguments current displayRoot = some [((0 : Fin 2),(0 : Fin 2))] := rfl
    have equal := Option.some.inj (located.symm.trans found)
    subst bounds
    exact branch
  · contradiction

theorem installs_committed (candidate : Plan roles) (support)
    (reached : Generated finish.core.erased.current displayRoot candidate.packet.site.occurrence)
    (enabled : Installable registry finish candidate support) :
    GeneralNominalFeedbackSteps.Committed finish.core.erased.current candidate.packet := by
  rcases generated_cases _ reached with same | same
  · have localRule := GeneralNominalCenteredHeadWFBoundary.local_iff.mpr
      (GeneralNominalCenteredHeadStepBoundary.installable_selected enabled)
    rw [same] at localRule
    have agreement := GeneralNominalCenteredHeadWFBoundary.local_functional localRule GeneralNominalNonleafFinal194.selected
    have key := (CommonRoleOutermostResolver.Frontier.selected.inj agreement).1
    have children := (CommonRoleOutermostResolver.Frontier.selected.inj agreement).2
    constructor
    · intro assignment valid
      rcases candidate with ⟨⟨preg,pctx,site,decl,check,bounds⟩,input,inputEq⟩
      have reg := enabled.frame.registry_eq
      have ctx := enabled.frame.context_eq
      dsimp only at reg ctx
      subst preg; subst pctx
      have visible := enabled.frame.visible
      simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
      rcases visible with declEq | declEq | declEq
      · subst decl; cases key
      · subst decl
        have found := enabled.frame.located
        change arguments current (inputs site.occurrence) = some bounds at found
        rw [same] at found
        have located : arguments current (inputs displayRoot) = some [((0 : Fin 2),(0 : Fin 2))] := rfl
        have equal := Option.some.inj (found.symm.trans located)
        subst bounds
        change BranchModels registry current site.occurrence display check [((0 : Fin 2),(0 : Fin 2))] assignment
        rw [same]
        exact parent_branch assignment valid.1
      · subst decl; cases key
    · intro child member
      rw [children] at member
      cases List.mem_singleton.mp member
      rw [same,edges]
      exact List.mem_singleton_self _
  · have localRule := GeneralNominalCenteredHeadWFBoundary.local_iff.mpr
      (GeneralNominalCenteredHeadStepBoundary.installable_selected enabled)
    rw [same] at localRule
    have agreement := GeneralNominalCenteredHeadWFBoundary.local_functional localRule GeneralNominalNonleafReuse193.selected
    have key := (CommonRoleOutermostResolver.Frontier.selected.inj agreement).1
    have children := (CommonRoleOutermostResolver.Frontier.selected.inj agreement).2
    constructor
    · intro assignment valid
      rcases candidate with ⟨⟨preg,pctx,site,decl,check,bounds⟩,input,inputEq⟩
      have reg := enabled.frame.registry_eq
      have ctx := enabled.frame.context_eq
      dsimp only at reg ctx
      subst preg; subst pctx
      have visible := enabled.frame.visible
      simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
      rcases visible with declEq | declEq | declEq
      · subst decl
        have found := enabled.frame.located
        change arguments current (inputs site.occurrence) = some bounds at found
        rw [same] at found
        have located : arguments current (inputs displayChild) = some [((1 : Fin 2),(1 : Fin 2))] := rfl
        have equal := Option.some.inj (found.symm.trans located)
        subst bounds
        change BranchModels registry current site.occurrence GeneralNominalExamples.intDisplay check [((1 : Fin 2),(1 : Fin 2))] assignment
        rw [same]
        exact GeneralNominalNonleafReuse193.packet_models assignment valid.1
      · subst decl; cases key
      · subst decl; cases key
    · intro child member
      rw [children] at member
      cases member

theorem no_refresh (next : GeneralNominalCandidates.Context)
    (exactModels : ∀ assignment, Models finish assignment → GeneralNominalState.Models next.state assignment)
    (source : Nat) (unknown : ¬ GeneralNominalState.Known current.state source) :
    ¬ GeneralNominalState.Known next.state source := by
  by_cases zero : source = 0
  · subst source
    exact False.elim (unknown ⟨(0 : Fin 2),rfl,Or.inr ⟨GeneralNominalExamples.listDescriptor,rfl⟩⟩)
  · by_cases one : source = 1
    · subst source
      exact False.elim (unknown ⟨(1 : Fin 2),rfl,Or.inl (by decide +kernel)⟩)
    · exact GeneralDictionaryTerminalRefresh.no_known_distinct next.state model
        (GeneralDictionarySupportRecursiveClosure.varying source) source
        (by change (if source = 0 then CommonNominalFullCarrier.nominal 0 [.inl (.base .int)] else .base .int) = .base .int
            exact ite_eq_right zero)
        (by simp only [GeneralDictionarySupportRecursiveClosure.varying,GeneralDictionaryTerminalRefresh.varying,ite_true])
        (exactModels model final_model)
        (exactModels _ ((final_models_iff _).mpr (GeneralDictionarySupportRecursiveClosure.varying_source source (by omega))))

/-- The actual head-only WF state after the nonleaf installation has no enabled
administrative, refresh, novel installation or merge action at any generated node. -/
theorem stable : Stable registry finish displayRoot := by
  intro focus generated after action
  cases action with
  | administrative focus after action =>
    cases action with
    | enqueue linked absent =>
      rcases generated_cases focus generated with same | same
      · exact absent _ (by rw [raw_sites]; exact List.mem_cons_self ..) same.symm
      · exact absent _ (by rw [raw_sites]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)) same.symm
    | refresh context certificate source member unknown known =>
      exact no_refresh context (fun assignment valid => certificate.exact assignment valid.1.1) source unknown known
    | equate first last one two equal novel =>
      exact novel (fun assignment valid => equal assignment (context_complete assignment valid).1.1)
    | reobserve revision certificate improved =>
      exact GeneralNominalReobservationSteps.pointClosed_no_revision
        (show GeneralNominalReobservationSteps.PointClosed finish.core.erased.current.context.state from
          GeneralDictionarySupportRecursiveClosure.point_closed) revision improved
  | refresh focus context certificate source member unknown known =>
    exact no_refresh context (fun assignment valid => certificate.exact assignment valid.1) source unknown known
  | install candidate support enabled novel =>
    exact novel (installs_committed candidate support generated enabled)
  | merge first last support one two same novel guard =>
    exact novel (center_closed first last one two same)

theorem halted : ∀ after, ¬ Step registry displayRoot finish after := by
  rintro after ⟨focus,generated,action⟩
  exact stable focus generated after action

/-- The concrete source reaches a stable state and its full recursive V6
classification has Evidence for every final assignment. This is one existing
source fixture, not a general EvidenceNode or whole-language theorem. -/
theorem completed :
    (GeneralNominalCenteredHeadWFBoundary.boundary roles).Initial registry displayRoot start ∧
    B4TargetV6.Reachable (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry displayRoot finish ∧
    (GeneralNominalCenteredHeadWFBoundary.boundary roles).Stable registry finish displayRoot ∧
    B4TargetV6.Classify (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry finish displayRoot
      (.selected (.node 1 [.node 3 []])) ∧
    Models finish model ∧
    ∀ assignment, Models finish assignment →
      (GeneralNominalCenteredHeadWFBoundary.boundary roles).Evidence registry finish assignment displayRoot (.node 1 [.node 3 []]) :=
  ⟨initial_source,reachable,stable,GeneralNominalNonleafFinal194.parent_classify,final_model,recursive_evidence⟩
end Yulang.GeneralNominalNonleafStable194
