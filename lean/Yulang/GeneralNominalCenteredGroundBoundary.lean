import Yulang.GeneralNominalCenteredAccessibility

/-! Ground point sources retain the full centered transition relation and
local diagnostics. Accessibility now supplies actual terminal executions. -/
namespace Yulang.GeneralNominalCenteredGroundBoundary
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralNominalCenteredBoundary (vocabulary boundary frontiers)
open B4TargetV5

variable {roles : Roles.RoleDecls}

def groundBoundary (roles : Roles.RoleDecls) : SourceBoundary (vocabulary roles) :=
  { boundary roles with Initial := fun registry root state => ∃ context labels,
      GeneralNominalSourceFormation.InitialSource registry context root ∧
      (∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2) ∧
      GeneralNominalGroundAccessibility.GroundRoots context root labels ∧ state = initial context root }

theorem old_reachable (reachable : Reachable (groundBoundary roles) registry root state) :
    Reachable (boundary roles) registry root state := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  exact ⟨_,initial_source source,path⟩

theorem progress (registry : Registry) (checked : (groundBoundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles) (reachable : Reachable (groundBoundary roles) registry root state) :
    Acc (fun next current => (groundBoundary roles).Step registry root current next) state := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  have accessible := GeneralNominalCenteredAccessibility.ground_point_root_accessible checked.2 source point ground
  induction path with
  | refl => exact accessible
  | tail path step ih => exact ih.inv step

theorem closure (registry : Registry) (checked : (groundBoundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles) (reachable : Reachable (groundBoundary roles) registry root state)
    (halted : ∀ after, ¬ (groundBoundary roles).Step registry root state after) :
    (groundBoundary roles).Stable registry state root ∧
      ∀ child, (groundBoundary roles).Generated registry state root child → (groundBoundary roles).Stable registry state child :=
  GeneralNominalCenteredBoundary.closure registry checked state root (old_reachable reachable) halted

theorem stepModels (registry : Registry) (checked : (groundBoundary roles).Checked registry)
    (root : Occurrence roles) (before after : State roles) (reachable : Reachable (groundBoundary roles) registry root before)
    (step : (groundBoundary roles).Step registry root before after) :
    ∀ model, (groundBoundary roles).Models after model → (groundBoundary roles).Models before model :=
  GeneralNominalCenteredBoundary.stepModels registry checked root before after (old_reachable reachable) step

theorem localIdentity (registry : Registry) (state : State roles) (root : Occurrence roles)
    (_reachable : Reachable (groundBoundary roles) registry root state) :
    (frontiers roles registry state).Local = B4TargetV3.Local (groundBoundary roles).toSourceBoundary registry state := rfl

theorem frontierLocal (registry : Registry) (checked : (groundBoundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles) (reachable : Reachable (groundBoundary roles) registry root state)
    (demand : Occurrence roles) (frontier : CommonRoleOutermostResolver.Frontier (Occurrence roles)) :
    (frontiers roles registry state).frontier demand = frontier ↔
      B4TargetV3.Local (groundBoundary roles).toSourceBoundary registry state demand frontier :=
  GeneralNominalCenteredBoundary.frontierLocal registry checked state root (old_reachable reachable) demand frontier

theorem dictionaryRefl (dictionary : CommonRoleOutermostResolver.Dictionary) :
    (groundBoundary roles).DictionaryEquivalent dictionary dictionary :=
  GeneralNominalCenteredBoundary.dictionaryRefl dictionary

theorem initialReorders (registry other : Registry) (_checked : (groundBoundary roles).Checked registry)
    (_checkedOther : (groundBoundary roles).Checked other) (order : (groundBoundary roles).Reorders registry other)
    (state : State roles) (root : Occurrence roles) (given : (groundBoundary roles).Initial registry root state) :
    (groundBoundary roles).Initial other root state := by
  obtain ⟨context,labels,formed,point,ground,same⟩ := given
  exact ⟨context,labels,GeneralDictionaryInitialSource.source_reorders registry other order context root formed,
    point,ground,same⟩

theorem terminal (registry : Registry) (checked : (groundBoundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles) (reachable : Reachable (groundBoundary roles) registry root state) :
    ∃ final, B4Target.Steps (Step registry root) state final ∧
      (∀ next, ¬ Step registry root final next) ∧ Stable registry final root ∧
      (∀ child, GeneralNominalSaturationState.Generated final.erased.current root child → Stable registry final child) ∧
      ∀ model, Models final model → Models state model := by
  obtain ⟨final,path,halted⟩ := terminal_of_accessible (progress registry checked state root reachable)
  have stable := closure registry checked final root (reachable_steps (groundBoundary roles) reachable path) halted
  refine ⟨final,path,halted,stable.1,stable.2,?_⟩
  exact B4SkeletonV5.steps_models (groundBoundary roles) registry root (stepModels registry checked root) reachable path

noncomputable def finalState (registry : Registry) (checked : (groundBoundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles) (reachable : Reachable (groundBoundary roles) registry root state) : State roles :=
  Classical.choose (terminal registry checked state root reachable)

theorem execution (registry : Registry) (checked : (groundBoundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles) (reachable : Reachable (groundBoundary roles) registry root state) :
    B4Target.Steps (Step registry root) state (finalState registry checked state root reachable) :=
  (Classical.choose_spec (terminal registry checked state root reachable)).1

theorem halted (registry : Registry) (checked : (groundBoundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles) (reachable : Reachable (groundBoundary roles) registry root state)
    (next : State roles) : ¬ Step registry root (finalState registry checked state root reachable) next :=
  (Classical.choose_spec (terminal registry checked state root reachable)).2.1 next

end Yulang.GeneralNominalCenteredGroundBoundary
