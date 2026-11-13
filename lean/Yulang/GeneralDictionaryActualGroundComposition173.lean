import Yulang.GeneralDictionaryActualGroundExecutor173

/-! A conditional ground V5 composition. Ten structural/driver fields are
proved for the ground initial-source restriction. The three named residual
properties below cover the four remaining fields; none is discharged here. -/
namespace Yulang.GeneralDictionaryActualGroundComposition173
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualBoundary
open GeneralDictionaryActualV5173 GeneralDictionaryActualGroundExecutor173
open GeneralDictionaryActualStable173 (SelectedPackets)
open CommonRoleOutermostResolver
open B4TargetV5
variable {roles : Roles.RoleDecls}

theorem initial_reorders (registry other : Registry)
    (order : (groundBoundary roles).Reorders registry other) (state : Tracked roles) (root : Occurrence roles)
    (given : (groundBoundary roles).Initial registry root state) :
    (groundBoundary roles).Initial other root state := by
  obtain ⟨context,labels,source,point,ground,same⟩ := given
  exact ⟨context,labels,GeneralDictionaryInitialSource.source_reorders registry other order context root source,
    point,ground,same⟩

/-- These residuals are not proved. In particular ground saturation termination
is NOT where-tree accessibility or canonical registry-order independence. -/
structure Remaining (roles : Roles.RoleDecls) : Prop where
  packets : SelectedPackets roles
  whereAccessible : ∀ registry, (groundBoundary roles).Checked registry → ∀ state root,
    Reachable (groundBoundary roles) registry root state →
      Acc (Child (B4TargetV3.Local (groundBoundary roles).toSourceBoundary registry state)) root
  canonicalLocalOrder : ∀ registry other, (groundBoundary roles).Checked registry →
    (groundBoundary roles).Checked other → (groundBoundary roles).Reorders registry other → ∀ state root,
    Reachable (groundBoundary roles) registry root state → Reachable (groundBoundary roles) other root state →
    ∀ focus frontier,
      B4TargetV3.Local (groundBoundary roles).toSourceBoundary registry
        ((executor roles).run registry state root).1 focus frontier ↔
      B4TargetV3.Local (groundBoundary roles).toSourceBoundary other
        ((executor roles).run other state root).1 focus frontier

theorem bridges (roles : Roles.RoleDecls) (rest : Remaining roles) :
    B4SkeletonV5.B4Bridges (groundBoundary roles) (executor roles) (frontiers roles) where
  progress := ground_progress
  execution := execution roles
  halted := halted roles
  closure := fun registry checked state root reachable =>
    closure registry checked state root (ground_reachable reachable)
  stepModels := fun registry checked root before after reachable =>
    stepModels registry checked root before after (ground_reachable reachable)
  frontierLocal := fun registry checked state root reachable =>
    frontierLocal registry checked state root (ground_reachable reachable)
  localIdentity := fun registry state root reachable =>
    localIdentity registry state root (ground_reachable reachable)
  whereAccessible := rest.whereAccessible
  treeExecution := treeExecution roles
  canonicalLocalOrder := rest.canonicalLocalOrder
  dictionaryRefl := dictionaryRefl
  evidenceNode := ground_evidenceNode rest.packets
  generatedChildren := ground_generatedChildren rest.packets
  initialReorders := fun registry other _ _ order state root given =>
    initial_reorders registry other order state root given

/-- Conditional only: the three explicit residuals remain to be established. -/
theorem statement (roles : Roles.RoleDecls) (rest : Remaining roles) :
    B4TargetV5.Statement (groundBoundary roles) (executor roles) :=
  B4SkeletonV5.b4_of_bridges _ _ _ (bridges roles rest)

end Yulang.GeneralDictionaryActualGroundComposition173
