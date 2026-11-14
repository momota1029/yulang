import Yulang.GeneralNominalCenteredGroundBoundary
import Yulang.GeneralNominalCenteredWhere

/-! A total mathematical executor and ten of the fourteen V5 fields for the
ground centered boundary. The four remaining laws are explicit parameters of
the composition theorem, rather than premises hidden in the executor. -/
namespace Yulang.GeneralNominalCenteredGroundComposition
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralNominalCenteredBoundary (vocabulary frontiers)
open GeneralNominalCenteredGroundBoundary (groundBoundary)
open B4TargetV5 CommonRoleOutermostResolver

variable {roles : Roles.RoleDecls}

noncomputable def terminalState (registry : Registry) (state : State roles) (root : Occurrence roles) : State roles := by
  classical
  exact if eligible : (groundBoundary roles).Checked registry ∧ Reachable (groundBoundary roles) registry root state then
    GeneralNominalCenteredGroundBoundary.finalState registry eligible.1 state root eligible.2 else state

theorem terminalState_exact (registry : Registry) (checked : (groundBoundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles) (reachable : Reachable (groundBoundary roles) registry root state) :
    terminalState registry state root =
      GeneralNominalCenteredGroundBoundary.finalState registry checked state root reachable := by
  classical
  simp [terminalState,checked,reachable]

noncomputable def diagnostic (registry : Registry) (state : State roles) (root : Occurrence roles) : Tree := by
  classical
  exact if supported : FrontierExact (frontiers roles registry state) ∧
      Acc (Child (frontiers roles registry state).Local) root then
    resolve (frontiers roles registry state) supported.1 root supported.2 else .pending

theorem diagnostic_exact (registry : Registry) (state : State roles) (root : Occurrence roles)
    (exact : FrontierExact (frontiers roles registry state))
    (accessible : Acc (Child (frontiers roles registry state).Local) root) :
    diagnostic registry state root = resolve (frontiers roles registry state) exact root accessible := by
  classical
  simp [diagnostic,exact,accessible]

noncomputable def executor (roles : Roles.RoleDecls) : B4TargetV3.Executor (vocabulary roles) where
  run registry state root :=
    let final := terminalState registry state root
    (final,diagnostic registry final root)

theorem execution (registry : Registry) (checked : (groundBoundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles) (reachable : Reachable (groundBoundary roles) registry root state) :
    B4Target.Steps ((groundBoundary roles).Step registry root) state ((executor roles).run registry state root).1 := by
  change B4Target.Steps _ _ (terminalState registry state root)
  rw [terminalState_exact registry checked state root reachable]
  exact GeneralNominalCenteredGroundBoundary.execution registry checked state root reachable

theorem halted (registry : Registry) (checked : (groundBoundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles) (reachable : Reachable (groundBoundary roles) registry root state)
    (next : State roles) : ¬ (groundBoundary roles).Step registry root ((executor roles).run registry state root).1 next := by
  change ¬ Step registry root (terminalState registry state root) next
  rw [terminalState_exact registry checked state root reachable]
  exact GeneralNominalCenteredGroundBoundary.halted registry checked state root reachable next

theorem treeExecution (registry : Registry) (_checked : (groundBoundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles) (_reachable : Reachable (groundBoundary roles) registry root state)
    (exact : FrontierExact (frontiers roles registry ((executor roles).run registry state root).1))
    (accessible : Acc (Child (frontiers roles registry ((executor roles).run registry state root).1).Local) root) :
    ((executor roles).run registry state root).2 =
      resolve (frontiers roles registry ((executor roles).run registry state root).1) exact root accessible :=
  diagnostic_exact registry _ root exact accessible

structure Remaining (roles : Roles.RoleDecls) : Prop where
  whereAccessible : ∀ r, (groundBoundary roles).Checked r → ∀ s root,
    Reachable (groundBoundary roles) r root s →
    Acc (Child (B4TargetV3.Local (groundBoundary roles).toSourceBoundary r s)) root
  canonicalLocalOrder : ∀ r r', (groundBoundary roles).Checked r → (groundBoundary roles).Checked r' →
    (groundBoundary roles).Reorders r r' → ∀ s root,
    Reachable (groundBoundary roles) r root s → Reachable (groundBoundary roles) r' root s → ∀ d f,
    B4TargetV3.Local (groundBoundary roles).toSourceBoundary r ((executor roles).run r s root).1 d f ↔
      B4TargetV3.Local (groundBoundary roles).toSourceBoundary r' ((executor roles).run r' s root).1 d f
  evidenceNode : B4SkeletonV5.EvidenceNode (groundBoundary roles)
  generatedChildren : B4SkeletonV5.GeneratedChildren (groundBoundary roles)

theorem bridges (remaining : Remaining roles) :
    B4SkeletonV5.B4Bridges (groundBoundary roles) (executor roles) (frontiers roles) where
  progress := GeneralNominalCenteredGroundBoundary.progress
  execution := execution
  halted := halted
  closure := GeneralNominalCenteredGroundBoundary.closure
  stepModels := GeneralNominalCenteredGroundBoundary.stepModels
  frontierLocal := GeneralNominalCenteredGroundBoundary.frontierLocal
  localIdentity := GeneralNominalCenteredGroundBoundary.localIdentity
  whereAccessible := remaining.whereAccessible
  treeExecution := treeExecution
  canonicalLocalOrder := remaining.canonicalLocalOrder
  dictionaryRefl := GeneralNominalCenteredGroundBoundary.dictionaryRefl
  evidenceNode := remaining.evidenceNode
  generatedChildren := remaining.generatedChildren
  initialReorders := GeneralNominalCenteredGroundBoundary.initialReorders

theorem composition (remaining : Remaining roles) :
    B4TargetV5.Statement (groundBoundary roles) (executor roles) :=
  B4SkeletonV5.b4_of_bridges _ _ _ (bridges remaining)

end Yulang.GeneralNominalCenteredGroundComposition
