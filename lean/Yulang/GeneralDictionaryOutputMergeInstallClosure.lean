import Yulang.GeneralDictionaryOutputMergeRefreshClassification

/-! Exact exclusion of further packet installation at every generated focus of
this concrete refreshed state. Semantic Committed is not journal membership:
terminal packets need not be physically added when their full meaning is already
entailed and they emit no children. This is not a proof of full Stable. -/
namespace Yulang.GeneralDictionaryOutputMergeInstallClosure
open GeneralDictionaryOutputMergeSuccess GeneralDictionaryOutputMergeRefresh
open GeneralDictionaryOutputMergeRefreshEvidence GeneralDictionaryOutputMergeRefreshClassification
open GeneralNominalExamples (displayRoot)
open GeneralDeclarationExamples (roles)
open GeneralNominalSaturationState GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection

theorem edges_exact : refreshed.current.edges = [(displayRoot,child 10),(displayRoot,child 11)] := by
  change [] ++ children.map (fun child => (displayRoot,child)) = _
  rw [children_exact]; rfl

theorem generated_cases (focus : GeneralSourceDictionaries.Occurrence roles)
    (given : Generated refreshed.current displayRoot focus) :
    focus = displayRoot ∨ focus = child 10 ∨ focus = child 11 := by
  induction given with
  | root => exact Or.inl rfl
  | child _ member _ =>
    rw [edges_exact] at member
    rcases List.mem_cons.mp member with same | member
    · exact Or.inr (Or.inl (congrArg Prod.snd same))
    · exact Or.inr (Or.inr (congrArg Prod.snd (List.mem_singleton.mp member)))
  | alias _ _ member _ _ =>
    change _ ∈ finish.current.sites at member
    rw [GeneralDictionaryOutputMergeSuccess.sites_exact] at member
    rcases List.mem_cons.mp member with same | member
    · exact Or.inl (congrArg (fun s => s.occurrence) same)
    · rcases List.mem_cons.mp member with same | member
      · exact Or.inr (Or.inl (congrArg (fun s => s.occurrence) same))
      · exact Or.inr (Or.inr (congrArg (fun s => s.occurrence) (List.mem_singleton.mp member)))

theorem root_committed (p : Packet roles) (same : p.site.occurrence = displayRoot)
    (enabled : GeneralNominalFeedbackSteps.Installable registry refreshed.current p) :
    GeneralNominalFeedbackSteps.Committed refreshed.current p := by
  have selected := enabled.2.1
  rw [same] at selected
  have agreement := GeneralNominalFeedbackK2.local_functional selected parent_selected
  have key := (CommonRoleOutermostResolver.Frontier.selected.inj agreement).1
  have children := (CommonRoleOutermostResolver.Frontier.selected.inj agreement).2
  constructor
  · intro m valid
    rcases p with ⟨preg,pctx,psite,pdecl,pchecked,pbounds⟩
    have reg := enabled.1.1
    have ctx := enabled.1.2.1
    dsimp only at reg ctx
    subst preg; subst pctx
    have visible := enabled.1.2.2.2.1
    change pdecl ∈ [declaration,terminal] at visible
    rcases List.mem_cons.mp visible with decl | visible
    · subst pdecl
      have found := enabled.1.2.2.2.2.2.1
      change arguments refreshedContext psite.occurrence = some pbounds at found
      change psite.occurrence = displayRoot at same
      rw [same] at found
      have located : arguments refreshedContext displayRoot = some [((0 : Fin 4),0)] := by decide +kernel
      have equal := Option.some.inj (found.symm.trans located)
      subst pbounds
      change BranchModels registry refreshedContext psite.occurrence declaration pchecked [((0 : Fin 4),0)] m
      rw [same]
      exact GeneralDictionaryOutputMergeRefreshEvidence.parent_branch m valid
    · have decl := List.mem_singleton.mp visible
      subst pdecl
      cases key
  · intro child member
    rw [children] at member
    rw [same,edges_exact]
    rcases List.mem_cons.mp member with same | member
    · rw [same]; exact List.mem_cons_self ..
    · rw [List.mem_singleton.mp member]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem child_committed (p : Packet roles) (n : Nat) (which : n = 10 ∨ n = 11)
    (same : p.site.occurrence = child n)
    (enabled : GeneralNominalFeedbackSteps.Installable registry refreshed.current p) :
    GeneralNominalFeedbackSteps.Committed refreshed.current p := by
  have selected := enabled.2.1
  rw [same] at selected
  have agreement := GeneralNominalFeedbackK2.local_functional selected (child_selected n which)
  have key := (CommonRoleOutermostResolver.Frontier.selected.inj agreement).1
  have children := (CommonRoleOutermostResolver.Frontier.selected.inj agreement).2
  constructor
  · intro m valid
    rcases p with ⟨preg,pctx,psite,pdecl,pchecked,pbounds⟩
    have reg := enabled.1.1
    have ctx := enabled.1.2.1
    dsimp only at reg ctx
    subst preg; subst pctx
    have visible := enabled.1.2.2.2.1
    change pdecl ∈ [declaration,terminal] at visible
    rcases List.mem_cons.mp visible with decl | visible
    · subst pdecl; cases key
    · have decl := List.mem_singleton.mp visible
      subst pdecl
      have found := enabled.1.2.2.2.2.2.1
      change arguments refreshedContext psite.occurrence = some pbounds at found
      change psite.occurrence = child n at same
      rw [same] at found
      have located : arguments refreshedContext (child n) = some [((1 : Fin 4),1)] := by
        change arguments refreshedContext (GeneralDictionaryJointMergeExample.root 0 0) = _
        decide +kernel
      have equal := Option.some.inj (found.symm.trans located)
      subst pbounds
      change BranchModels registry refreshedContext psite.occurrence terminal pchecked [((1 : Fin 4),1)] m
      rw [same]
      exact GeneralDictionaryOutputMergeRefreshEvidence.terminal_branch m valid n which
  · intro child member
    rw [children] at member
    cases member

/-- Every enabled generated packet is already committed semantically, so its
novelty premise for an actual install transition is impossible. -/
theorem installs_committed (p : Packet roles)
    (reached : Generated refreshed.current displayRoot p.site.occurrence)
    (enabled : GeneralNominalFeedbackSteps.Installable registry refreshed.current p) :
    GeneralNominalFeedbackSteps.Committed refreshed.current p := by
  rcases generated_cases _ reached with same | same | same
  · exact root_committed p same enabled
  · exact child_committed p 10 (Or.inl rfl) same enabled
  · exact child_committed p 11 (Or.inr rfl) same enabled
end Yulang.GeneralDictionaryOutputMergeInstallClosure
