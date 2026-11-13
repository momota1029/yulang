import Yulang.GeneralNominalCaptureNames
import Yulang.GeneralNominalPeelingAccessibility

/-! A distinguished input decreases independently of the other arguments.
Other heads and child inputs may be compound, and role arities may differ.
All transitions, outputs and observation updates use the existing relation. -/
namespace Yulang.GeneralNominalSpineAccessibility
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries
open GeneralNominalSaturationState GeneralNominalSupport GeneralNominalActualInspectionSteps
open GeneralNominalInvocationAncestry GeneralNominalActualTraceSupport
open GeneralNominalPeelingOrigins GeneralNominalSharedCaptures
open GeneralNominalRecursiveInspection GeneralNominalCaptureNames

structure Spine (roles : Roles.RoleDecls) (registry : Registry)
    (context : GeneralNominalCandidates.Context) (active : Nat → Prop) (name : Nat) : Prop where
  positive : ∀ role, active role → 0 < (roles role).arity
  clauses : ∀ declaration ∈ registry.declarations, active declaration.role →
    declaration.requirements ≠ [] → ∃ binder rest,
      GeneralNominalInspection.queries context.state context.interpretation declaration =
        .nominal name [.variables [binder]] :: rest ∧
      binder ∉ manyNames rest ∧
      ∀ clause ∈ declaration.requirements,
        active clause.role ∧ clause.arguments[0]? = some (.var binder)

theorem peeling_spine (peeling : GeneralNominalPeelingAccessibility.Peeling roles registry context active name) :
    Spine roles registry context active name := by
  constructor
  · intro role live; rw [peeling.unary role live]; omega
  · intro declaration visible live nonempty
    obtain ⟨binder,query,children⟩ := peeling.clauses declaration visible live nonempty
    refine ⟨binder,[],query,by simp [manyNames],?_⟩
    intro clause member
    obtain ⟨active,arguments⟩ := children clause member
    exact ⟨active,by simp [arguments]⟩

theorem child_projection (spine : Spine roles registry context active name)
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
  obtain ⟨binder,rest,query,separate,clauses⟩ := spine.clauses packet.declaration visible live nonempty
  have currentQuery : GeneralNominalInspection.queries packet.context.state packet.context.interpretation packet.declaration =
      .nominal name [.variables [binder]] :: rest := by
    simpa only [GeneralNominalInspection.queries,constructors,interpretation] using query
  have facts := clauses clause present
  have first : ∃ tail, clause.arguments = .var binder :: tail := by
    cases h : clause.arguments with
    | nil => simp [h] at facts
    | cons head tail =>
      have equal : head = .var binder := Option.some.inj (by simpa [h] using facts.2)
      exact ⟨tail,by rw [equal]⟩
  obtain ⟨tail,arguments⟩ := first
  have needed : Needed packet binder := ⟨clause,present,by
    simp [arguments,normalizeArgs,normalize,variablesArgs,Pattern.variables]⟩
  obtain ⟨retained,usable⟩ := generation binder needed
  let index : Fin (roles clause.role).arity := ⟨0,spine.positive clause.role facts.1⟩
  have available : ∃ actual, GeneralNominalSharedEmission.OriginAt packet
      (GeneralNominalFeedbackSites.clauseChild packet clause signature) index.val actual := by
    refine ⟨retained,clause,present,signature,index,rfl,rfl,binder,usable,?_⟩
    simp only [arguments,index,List.getElem_cons_zero,normalize]
  obtain ⟨chosen,kept,evidence⟩ := GeneralNominalSharedEmission.retains packet
    (GeneralNominalFeedbackSites.clauseChild packet clause signature) index available
  obtain ⟨other,otherMem,otherSignature,position,_,positionEq,captured,captureUsable,pattern⟩ := evidence
  have zero : position.val = 0 := positionEq.symm
  have atZero := (clauses other otherMem).2
  have atPosition : other.arguments[position.val]'(by rw [otherSignature.1]; exact position.isLt) = .var binder := by
    exact (List.getElem?_eq_some_iff.mp (zero ▸ atZero)).2
  rw [atPosition] at pattern
  have equal : binder = captured := by injection pattern
  subst captured
  have originEq := distinguished_capture packet currentQuery separate recorded captureUsable
  exact ⟨facts.1,by simpa only [index,originEq] using kept⟩

theorem sites_paths (spine : Spine roles registry context active name)
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
        have next := child_projection spine packet enabled.1.2.2.2.1
          (enabled.1.2.2.2.2.1 ▸ parentLive)
          (by rw [enabled.1.2.1]; exact config.2.1)
          (by rw [enabled.1.2.1]; exact config.2.2) retained guard.1.2.2.1 present
        have successor := child_identity packet child present visible
        rw [enabled.1.1,seed] at successor
        exact ⟨next.1,depth+1,.child ancestry successor,next.2⟩

theorem installed_depth_bound (spine : Spine roles registry context active name)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (live : active root.demand.role)
    (rootOrigin : (GeneralNominalDemandMerging.pointSite root).inputs[0]? = some (some (.source identity)))
    (ground : ∀ model, GeneralNominalState.Models context.state model →
      CommonNominalFullCarrier.Equivalent (model identity).1 (tower name base length)) :
    InstalledDepthBound registry context root length := by
  intro state steps packet support generated enabled novel guard
  obtain ⟨activeSite,depth,ancestry,retained⟩ := sites_paths spine source live rootOrigin steps packet.site enabled.1.2.2.1
  obtain ⟨_,_,_,_,_,_,_,_,_,_,⟨model,valid,_⟩,_⟩ := enabled.1
  have descend : ∀ before after, B4Target.Steps (Step registry root) before after →
      Models after.current model → Models before.current model := by
    intro before after trace
    induction trace with
    | refl => exact id
    | tail trace step ih => exact fun valid => ih (GeneralNominalSharedSteps.step_models (step_shared step) model valid)
  have initialValid := descend _ _ steps valid
  let index : Fin (roles packet.site.occurrence.demand.role).arity := ⟨0,spine.positive _ activeSite⟩
  obtain ⟨value,seen⟩ := (valid.2.2 packet.site enabled.1.2.2.1 index _ retained).1
  exact ⟨depth,observed_depth (ground model initialValid.1) seen,ancestry⟩

theorem accessible (checked : Checked registry)
    (spine : Spine roles registry context active name)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (live : active root.demand.role)
    (rootOrigin : (GeneralNominalDemandMerging.pointSite root).inputs[0]? = some (some (.source identity)))
    (ground : ∀ model, GeneralNominalState.Models context.state model →
      CommonNominalFullCarrier.Equivalent (model identity).1 (tower name base length)) :
    Acc (fun next current => Step registry root current next) (initial context root) :=
  GeneralNominalActualBudget.accessible_of_installed_depth_bound checked source
    (installed_depth_bound spine source live rootOrigin ground)

end Yulang.GeneralNominalSpineAccessibility
