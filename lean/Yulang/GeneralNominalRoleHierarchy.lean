import Yulang.GeneralNominalActualBudget

/-! Unconditional termination for the syntactically stratified reachable role
fragment. Heads, captures, output binders, materialization, and observations
remain unrestricted. Unreachable recursive declarations may remain visible. -/
namespace Yulang.GeneralNominalRoleHierarchy
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualInspectionSteps
open GeneralNominalInvocationAncestry GeneralNominalActualTraceSupport

structure Hierarchy (registry : Registry) (active : Nat → Prop) (rank : Nat → Nat) : Prop where
  children : ∀ declaration ∈ registry.declarations, active declaration.role →
    ∀ clause ∈ declaration.requirements, active clause.role ∧ rank clause.role < rank declaration.role

theorem child_role (packet : Packet roles) (child : Occurrence roles) (member : child ∈ packet.children) :
    ∃ clause ∈ packet.declaration.requirements, child.demand.role = clause.role := by
  unfold Packet.children GeneralNominalAllocation.children GeneralDictionaryEmissionPlans.children at member
  obtain ⟨emission,present,rfl⟩ := List.mem_map.mp member
  have old := (GeneralCanonicalChildOrder.canonicalEmit_perm packet.site.occurrence.identity
    packet.declaration packet.checked _ _).mem_iff.mpr present
  unfold GeneralDeclarationDemands.emitAll at old
  obtain ⟨clause,_,same⟩ := List.mem_map.mp old
  cases same
  exact ⟨clause.val,clause.property,rfl⟩

theorem child_rank (hierarchy : Hierarchy registry active rank)
    (packet : Packet roles) (visible : packet.declaration ∈ registry.declarations)
    (sameRole : packet.declaration.role = packet.site.occurrence.demand.role)
    (live : active packet.site.occurrence.demand.role)
    (child : Occurrence roles) (member : child ∈ packet.children) :
    active child.demand.role ∧ rank child.demand.role < rank packet.site.occurrence.demand.role := by
  obtain ⟨clause,present,role⟩ := child_role packet child member
  have smaller := hierarchy.children packet.declaration visible (sameRole ▸ live) clause present
  simpa only [role,sameRole] using smaller

theorem sites_ranked (hierarchy : Hierarchy registry active rank)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (live : active root.demand.role)
    (path : B4Target.Steps (Step registry root) (initial context root) state) :
    ∀ site ∈ state.current.sites, active site.occurrence.demand.role ∧
      ∃ depth, AtDepth registry context.state.seed root.identity depth site.occurrence.identity ∧
        depth + rank site.occurrence.demand.role ≤ rank root.demand.role := by
  induction path with
  | refl =>
    intro site member
    cases List.mem_singleton.mp member
    exact ⟨live,0,.root,by simp [GeneralNominalDemandMerging.pointSite]⟩
  | @tail before after path step ih =>
    have formed := formed_trace (.initial context source) path
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
      obtain ⟨parentLive,depth,ancestry,bounded⟩ := ih packet.site enabled.1.2.2.1
      have seed : packet.context.state.seed = context.state.seed := by
        rw [enabled.1.2.1]; exact seed_trace path
      have visible : packet.declaration ∈ packet.registry.declarations := by
        simpa only [enabled.1.1] using enabled.1.2.2.2.1
      intro site member
      change site ∈ before.current.sites ++ packet.children.map (GeneralNominalSharedEmission.childSite packet) at member
      rcases List.mem_append.mp member with old | added
      · exact ih site old
      · obtain ⟨child,present,rfl⟩ := List.mem_map.mp added
        have smaller := child_rank hierarchy packet enabled.1.2.2.2.1
          enabled.1.2.2.2.2.1 parentLive child present
        have successor := child_identity packet child present visible
        rw [enabled.1.1,seed] at successor
        refine ⟨smaller.1,depth+1,?_,?_⟩
        · simpa only [GeneralNominalSharedEmission.childSite] using AtDepth.child ancestry successor
        · change depth+1 + rank child.demand.role ≤ rank root.demand.role
          omega

theorem installed_depth_bound (hierarchy : Hierarchy registry active rank)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (live : active root.demand.role) : InstalledDepthBound registry context root (rank root.demand.role) := by
  intro state path packet support generated enabled novel guard
  obtain ⟨_,depth,ancestry,bounded⟩ := sites_ranked hierarchy source live path packet.site enabled.1.2.2.1
  exact ⟨depth,by omega,ancestry⟩

theorem accessible (checked : Checked registry) (hierarchy : Hierarchy registry active rank)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (live : active root.demand.role) :
    Acc (fun next current => Step registry root current next) (initial context root) :=
  GeneralNominalActualBudget.accessible_of_installed_depth_bound checked source
    (installed_depth_bound hierarchy source live)

end Yulang.GeneralNominalRoleHierarchy
