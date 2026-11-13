import Yulang.GeneralNominalPeelingOrigins
import Yulang.GeneralNominalPatersonLineage

/-! Accessibility for recursive unary nominal peeling on a finite source
spine. The relation is the unchanged actual-inspection Step; later endpoint
intervals, associated equations, aliases, and observation updates are retained. -/
namespace Yulang.GeneralNominalPeelingAccessibility
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalSupport GeneralNominalActualInspectionSteps
open GeneralNominalInvocationAncestry GeneralNominalActualTraceSupport
open GeneralNominalPeelingOrigins GeneralNominalSharedCaptures
open GeneralNominalRecursiveInspection

structure Peeling (roles : Roles.RoleDecls) (registry : Registry)
    (context : GeneralNominalCandidates.Context) (active : Nat → Prop) (name : Nat) : Prop where
  unary : ∀ role, active role → (roles role).arity = 1
  clauses : ∀ declaration ∈ registry.declarations, active declaration.role →
    declaration.requirements ≠ [] → ∃ binder,
      GeneralNominalInspection.queries context.state context.interpretation declaration =
        [.nominal name [.variables [binder]]] ∧
      ∀ clause ∈ declaration.requirements, active clause.role ∧ clause.arguments = [.var binder]

theorem child_projection (peeling : Peeling roles registry context active name)
    (packet : Packet roles) (visible : packet.declaration ∈ registry.declarations)
    (live : active packet.declaration.role)
    (constructors : packet.context.state.constructors = context.state.constructors)
    (interpretation : packet.context.interpretation = context.interpretation)
    (recorded : packet.site.inputs[0]? = some (some origin))
    (generation : GenerationGuard state packet) (member : child ∈ packet.children) :
    active child.demand.role ∧
      (GeneralNominalSharedEmission.childSite packet child).inputs[0]? =
        some (some (.nominal origin name 0)) := by
  obtain ⟨clause,present,signature,rfl⟩ := GeneralNominalPatersonLineage.emitted_clause packet child member
  have nonempty : packet.declaration.requirements ≠ [] := by
    intro empty; rw [empty] at present; cases present
  obtain ⟨binder,query,clauses⟩ := peeling.clauses packet.declaration visible live nonempty
  have currentQuery : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration =
      [.nominal name [.variables [binder]]] := by
    simpa only [GeneralNominalInspection.queries,constructors,interpretation] using query
  have clauseFacts := clauses clause present
  have needed : Needed packet binder := ⟨clause,present,by
    simp [clauseFacts.2,normalizeArgs,normalize,variablesArgs,Pattern.variables]⟩
  obtain ⟨retained,usable⟩ := generation binder needed
  let index : Fin (roles clause.role).arity := ⟨0,by rw [peeling.unary clause.role clauseFacts.1]; omega⟩
  have available : ∃ actual, GeneralNominalSharedEmission.OriginAt packet
      (GeneralNominalFeedbackSites.clauseChild packet clause signature) index.val actual := by
    refine ⟨retained,clause,present,signature,index,rfl,rfl,binder,usable,?_⟩
    simp only [clauseFacts.2,index,List.getElem_cons_zero,normalize]
  obtain ⟨chosen,kept,evidence⟩ := GeneralNominalSharedEmission.retains packet
    (GeneralNominalFeedbackSites.clauseChild packet clause signature) index available
  obtain ⟨_,_,_,_,_,_,_,captured,_⟩ := evidence
  have equal := usable_origin packet currentQuery recorded captured
  exact ⟨clauseFacts.1,by simpa only [index,equal] using kept⟩

theorem sites_paths (peeling : Peeling roles registry context active name)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (live : active root.demand.role)
    (rootOrigin : (GeneralNominalDemandMerging.pointSite root).inputs[0]? = some (some (.source identity)))
    (steps : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ site ∈ state.current.sites, active site.occurrence.demand.role ∧
      ∃ depth, AtDepth registry context.state.seed root.identity depth site.occurrence.identity ∧
        site.inputs[0]? = some (some (path name (.source identity) depth)) := by
  induction steps with
  | refl =>
    intro site member
    cases List.mem_singleton.mp member
    exact ⟨live,0,.root,rootOrigin⟩
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
      obtain ⟨parentLive,depth,ancestry,retained⟩ := ih packet.site enabled.1.2.2.1
      have config := configuration_trace steps
      have seed : packet.context.state.seed = context.state.seed := by
        rw [enabled.1.2.1]; exact config.1
      have visible : packet.declaration ∈ packet.registry.declarations := by
        simpa only [enabled.1.1] using enabled.1.2.2.2.1
      intro site member
      change site ∈ before.current.sites ++ packet.children.map (GeneralNominalSharedEmission.childSite packet) at member
      rcases List.mem_append.mp member with old | added
      · exact ih site old
      · obtain ⟨child,present,rfl⟩ := List.mem_map.mp added
        have next := child_projection peeling packet enabled.1.2.2.2.1
          (enabled.1.2.2.2.2.1 ▸ parentLive)
          (by rw [enabled.1.2.1]; exact config.2.1)
          (by rw [enabled.1.2.1]; exact config.2.2) retained guard.1.2.2.1 present
        have successor := child_identity packet child present visible
        rw [enabled.1.1,seed] at successor
        exact ⟨next.1,depth+1,.child ancestry successor,next.2⟩

theorem initial_origin {roles : Roles.RoleDecls} {root : Occurrence roles} (unary : (roles root.demand.role).arity = 1)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2) :
    ∃ identity, (GeneralNominalDemandMerging.pointSite root).inputs[0]? = some (some (.source identity)) := by
  let index : Fin (roles root.demand.role).arity := ⟨0,by omega⟩
  refine ⟨(root.demand.arguments index).1,?_⟩
  simp only [GeneralNominalDemandMerging.pointSite,List.getElem?_ofFn]
  split
  · simp only [point,ite_true]
    rfl
  · omega

theorem installed_depth_bound (peeling : Peeling roles registry context active name)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (live : active root.demand.role)
    (rootOrigin : (GeneralNominalDemandMerging.pointSite root).inputs[0]? = some (some (.source identity)))
    (ground : ∀ model, GeneralNominalState.Models context.state model →
      CommonNominalFullCarrier.Equivalent (model identity).1 (tower name base length)) :
    InstalledDepthBound registry context root length := by
  intro state steps packet support generated enabled novel guard
  obtain ⟨activeSite,depth,ancestry,retained⟩ := sites_paths peeling source live rootOrigin steps packet.site enabled.1.2.2.1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,⟨model,valid,_⟩,_⟩ := enabled.1
  have initialValid : GeneralNominalSaturationState.Models (GeneralNominalSupport.initial context root).current model := by
    have descend : ∀ before after, B4Target.Steps (Step registry root) before after →
        Models after.current model → Models before.current model := by
      intro before after path
      induction path with
      | refl => exact id
      | tail path step ih => exact fun valid => ih (GeneralNominalSharedSteps.step_models (step_shared step) model valid)
    exact descend _ _ steps valid
  let index : Fin (roles packet.site.occurrence.demand.role).arity :=
    ⟨0,by rw [peeling.unary _ activeSite]; omega⟩
  obtain ⟨value,seen⟩ := (valid.2.2 packet.site enabled.1.2.2.1 index _ retained).1
  exact ⟨depth,observed_depth (ground model initialValid.1) seen,ancestry⟩

theorem accessible (checked : Checked registry)
    (peeling : Peeling roles registry context active name)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (live : active root.demand.role)
    (rootOrigin : (GeneralNominalDemandMerging.pointSite root).inputs[0]? = some (some (.source identity)))
    (ground : ∀ model, GeneralNominalState.Models context.state model →
      CommonNominalFullCarrier.Equivalent (model identity).1 (tower name base length)) :
    Acc (fun next current => Step registry root current next) (initial context root) :=
  GeneralNominalActualBudget.accessible_of_installed_depth_bound checked source
    (installed_depth_bound peeling source live rootOrigin ground)

end Yulang.GeneralNominalPeelingAccessibility
