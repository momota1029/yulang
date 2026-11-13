import Yulang.GeneralNominalBranchingCaptures

/-! Closed accessibility for branching constructor descent on the unchanged
actual-inspection relation. Output equations and binders are unrestricted. -/
namespace Yulang.GeneralNominalBranchingAccessibility
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalSupport GeneralNominalActualInspectionSteps
open GeneralNominalInvocationAncestry GeneralNominalActualTraceSupport
open GeneralNominalSharedCaptures GeneralNominalRecursiveInspection
open GeneralNominalBranchingReadback GeneralNominalBranchingCaptures

structure Branching (roles : Roles.RoleDecls) (registry : Registry)
    (context : GeneralNominalCandidates.Context) (active : Nat → Prop) : Prop where
  unary : ∀ role, active role → (roles role).arity = 1
  clauses : ∀ declaration ∈ registry.declarations, active declaration.role →
    declaration.requirements ≠ [] → ∃ query,
      GeneralNominalInspection.queries context.state context.interpretation declaration = [query] ∧
      QueryShape query ∧ ∀ clause ∈ declaration.requirements,
        active clause.role ∧ ∃ name, clause.arguments = [.var name]

theorem child_path (branching : Branching roles registry context active)
    (packet : Packet roles) (visible : packet.declaration ∈ registry.declarations)
    (live : active packet.declaration.role)
    (constructors : packet.context.state.constructors = context.state.constructors)
    (interpretation : packet.context.interpretation = context.interpretation)
    (recorded : packet.site.inputs[0]? = some (some origin))
    (generation : GenerationGuard state packet) (member : child ∈ packet.children) :
    active child.demand.role ∧ ∃ next,
      (GeneralNominalSharedEmission.childSite packet child).inputs[0]? = some (some next) ∧ Path origin 1 next := by
  obtain ⟨clause,present,signature,rfl⟩ := GeneralNominalPatersonLineage.emitted_clause packet child member
  have nonempty : packet.declaration.requirements ≠ [] := by
    intro empty; rw [empty] at present; cases present
  obtain ⟨query,queries,shape,clauses⟩ := branching.clauses packet.declaration visible live nonempty
  have currentQuery : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration = [query] := by
    simpa only [GeneralNominalInspection.queries,constructors,interpretation] using queries
  obtain ⟨activeChild,name,arguments⟩ := clauses clause present
  have needed : Needed packet name := ⟨clause,present,by
    simp [arguments,normalizeArgs,normalize,variablesArgs,Pattern.variables]⟩
  obtain ⟨retained,usable⟩ := generation name needed
  let index : Fin (roles clause.role).arity := ⟨0,by rw [branching.unary clause.role activeChild]; omega⟩
  have available : ∃ actual, GeneralNominalSharedEmission.OriginAt packet
      (GeneralNominalFeedbackSites.clauseChild packet clause signature) index.val actual :=
    ⟨retained,clause,present,signature,index,rfl,rfl,name,usable,by simp only [arguments,index,List.getElem_cons_zero,normalize]⟩
  obtain ⟨chosen,kept,evidence⟩ := GeneralNominalSharedEmission.retains packet
    (GeneralNominalFeedbackSites.clauseChild packet clause signature) index available
  obtain ⟨_,_,_,_,_,_,captured,captureUsable,_⟩ := evidence
  exact ⟨activeChild,chosen,kept,usable_path packet currentQuery shape recorded captureUsable⟩

theorem sites_paths (branching : Branching roles registry context active)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (live : active root.demand.role)
    (rootOrigin : (GeneralNominalDemandMerging.pointSite root).inputs[0]? = some (some (.source identity)))
    (steps : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ site ∈ state.current.sites, active site.occurrence.demand.role ∧ ∃ depth origin,
      AtDepth registry context.state.seed root.identity depth site.occurrence.identity ∧
      site.inputs[0]? = some (some origin) ∧ Path (.source identity) depth origin := by
  induction steps with
  | refl =>
    intro site member
    cases List.mem_singleton.mp member
    exact ⟨live,0,_,.root,rootOrigin,.root⟩
  | @tail before after steps step ih =>
    have formed := formed_trace (.initial context source) steps
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action =>
      cases action with
      | enqueue linked absent =>
        obtain ⟨site,member,same⟩ := GeneralNominalSharedSteps.generated_registered (formed_shared formed) generated
        exact False.elim (absent site member same)
      | refresh | equate | reobserve => exact ih
    | merge => exact ih
    | install packet support enabled novel guard =>
      obtain ⟨parentLive,depth,origin,ancestry,retained,path⟩ := ih packet.site enabled.1.2.2.1
      have config := configuration_trace steps
      have seed : packet.context.state.seed = context.state.seed := by rw [enabled.1.2.1]; exact config.1
      have visible : packet.declaration ∈ packet.registry.declarations := by
        simpa only [enabled.1.1] using enabled.1.2.2.2.1
      intro site member
      change site ∈ before.current.sites ++ packet.children.map (GeneralNominalSharedEmission.childSite packet) at member
      rcases List.mem_append.mp member with old | added
      · exact ih site old
      · obtain ⟨child,present,rfl⟩ := List.mem_map.mp added
        obtain ⟨activeChild,next,kept,nextPath⟩ := child_path branching packet enabled.1.2.2.2.1
          (enabled.1.2.2.2.2.1 ▸ parentLive)
          (by rw [enabled.1.2.1]; exact config.2.1)
          (by rw [enabled.1.2.1]; exact config.2.2) retained guard.1.2.2.1 present
        have successor := child_identity packet child present visible
        rw [enabled.1.1,seed] at successor
        exact ⟨activeChild,depth+1,next,.child ancestry successor,kept,path_trans path nextPath⟩

theorem installed_depth_bound (branching : Branching roles registry context active)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (live : active root.demand.role)
    (rootOrigin : (GeneralNominalDemandMerging.pointSite root).inputs[0]? = some (some (.source identity)))
    (tree : Tree) (ground : ∀ model, GeneralNominalState.Models context.state model →
      CommonNominalFullCarrier.Equivalent (model identity).1 tree.value) :
    InstalledDepthBound registry context root tree.mass := by
  intro state steps packet support generated enabled novel guard
  obtain ⟨activeSite,depth,origin,ancestry,retained,path⟩ := sites_paths branching source live rootOrigin steps packet.site enabled.1.2.2.1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,⟨model,valid,_⟩,_⟩ := enabled.1
  have restrict : ∀ before after, B4Target.Steps (Step registry root) before after →
      Models after.current model → Models before.current model := by
    intro before after trace
    induction trace with
    | refl => exact id
    | tail trace step ih => exact fun valid => ih (GeneralNominalSharedSteps.step_models (step_shared step) model valid)
  have original := restrict _ _ steps valid
  let index : Fin (roles packet.site.occurrence.demand.role).arity := ⟨0,by rw [branching.unary _ activeSite]; omega⟩
  obtain ⟨value,seen⟩ := (valid.2.2 packet.site enabled.1.2.2.1 index origin retained).1
  obtain ⟨part,bounded,_⟩ := observed_path path tree (by intro actual observed; cases observed; exact ground model original.1) seen
  exact ⟨depth,by omega,ancestry⟩

theorem accessible (checked : Checked registry) (branching : Branching roles registry context active)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (live : active root.demand.role)
    (rootOrigin : (GeneralNominalDemandMerging.pointSite root).inputs[0]? = some (some (.source identity)))
    (tree : Tree) (ground : ∀ model, GeneralNominalState.Models context.state model →
      CommonNominalFullCarrier.Equivalent (model identity).1 tree.value) :
    Acc (fun next current => Step registry root current next) (initial context root) :=
  GeneralNominalActualBudget.accessible_of_installed_depth_bound checked source
    (installed_depth_bound branching source live rootOrigin tree ground)

end Yulang.GeneralNominalBranchingAccessibility
