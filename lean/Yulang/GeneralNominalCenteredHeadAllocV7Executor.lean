import Yulang.GeneralNominalCenteredHeadAllocV7Canonical

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCenteredHeadAllocV7Executor
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalCenteredHeadMatStepJournal (State)
open GeneralNominalCenteredHeadAllocV7Boundary
open GeneralNominalCenteredHeadAllocEncoding (registry registry_reorders)
variable {roles : Roles.RoleDecls}

noncomputable def frontiers (roles : Roles.RoleDecls) (value : Registry) :=
  GeneralNominalCenteredHeadAllocV7KernelExecutor.frontiers roles (registry value)

noncomputable def executor (roles : Roles.RoleDecls) : B4TargetV3.Executor (GeneralNominalCenteredHeadMatStepLocal.vocabulary roles) where
  run value state root := (GeneralNominalCenteredHeadAllocV7KernelExecutor.executor roles).run (registry value) state root

theorem progress (value : Registry) (checked : (boundary roles).Checked value) (state : State roles)
    (root : Occurrence roles) (reachable : B4TargetV7.Reachable (boundary roles) value root state) :
    Acc (fun next current => Step value root current next) state :=
  GeneralNominalCenteredHeadAllocV7Canonical.progress (registry value) (checked_compiled checked) state root
    (reachable_compiled reachable)

theorem execution (value : Registry) (checked : (boundary roles).Checked value) (state : State roles)
    (root : Occurrence roles) (reachable : B4TargetV7.Reachable (boundary roles) value root state) :
    B4Target.Steps (Step value root) state ((executor roles).run value state root).1 :=
  GeneralNominalCenteredHeadAllocV7KernelExecutor.execution (registry value) (checked_compiled checked) state root
    (reachable_compiled reachable)

theorem halted (value : Registry) (checked : (boundary roles).Checked value) (state : State roles)
    (root : Occurrence roles) (reachable : B4TargetV7.Reachable (boundary roles) value root state) :
    ∀ next, ¬ Step value root ((executor roles).run value state root).1 next :=
  GeneralNominalCenteredHeadAllocV7Canonical.halted (registry value) (checked_compiled checked) state root
    (reachable_compiled reachable)

def CanonicalExitLifting (roles : Roles.RoleDecls) : Prop :=
  ∀ value, (boundary roles).Checked value → ∀ state root,
    B4TargetV7.Reachable (boundary roles) value root state → state.core.erased.current.packets = [] →
      ∃ final, GeneralNominalCenteredHeadAllocV7KernelExecutor.LiftedExit (registry value) state root final

theorem canonical_exit_lifting (roles : Roles.RoleDecls) : CanonicalExitLifting roles := by
  intro value checked state root reachable empty
  exact GeneralNominalCenteredHeadAllocV7Canonical.canonical_exit_lifting roles
    (registry value) (checked_compiled checked) state root (reachable_compiled reachable) empty

theorem frontierLocal (checked : (boundary roles).Checked value) (state : State roles) (root : Occurrence roles) (frontier) :
    (frontiers roles value state).frontier root = frontier ↔ Local value state root frontier :=
  (GeneralNominalCenteredHeadAllocV7KernelExecutor.frontierLocal (checked_compiled checked) state root frontier).trans local_iff.symm

theorem localIdentity (value : Registry) (state : State roles) : (frontiers roles value state).Local = Local value state :=
  local_eq.symm

theorem treeExecution (value : Registry) (state : State roles) (root : Occurrence roles)
    (exact : FrontierExact (frontiers roles value ((executor roles).run value state root).1))
    (accessible : Acc (Child (frontiers roles value ((executor roles).run value state root).1).Local) root) :
    ((executor roles).run value state root).2 =
      resolve (frontiers roles value ((executor roles).run value state root).1) exact root accessible :=
  GeneralNominalCenteredHeadAllocV7KernelExecutor.treeExecution (registry value) state root exact accessible

def CanonicalLocalOrder (roles : Roles.RoleDecls) : Prop :=
  ∀ first last, (boundary roles).Checked first → (boundary roles).Checked last → (boundary roles).Reorders first last →
    ∀ state root, B4TargetV7.Reachable (boundary roles) first root state → B4TargetV7.Reachable (boundary roles) last root state →
    ∀ demand frontier, Local first ((executor roles).run first state root).1 demand frontier ↔
      Local last ((executor roles).run last state root).1 demand frontier

theorem canonicalLocalOrder (roles : Roles.RoleDecls) : CanonicalLocalOrder roles := by
  intro first last checked checkedLast order state root one two demand frontier
  exact local_iff.trans ((GeneralNominalCenteredHeadAllocV7Canonical.canonicalLocalOrder roles
    (registry first) (registry last) (checked_compiled checked) (checked_compiled checkedLast)
    (registry_reorders order) state root (reachable_compiled one) (reachable_compiled two) demand frontier).trans local_iff.symm)

theorem exact : B4TargetV7.Exact (boundary roles) (executor roles) := by
  intro value checked state root tree initial
  change Registry at value
  change State roles at state
  change Occurrence roles at root
  change _ ↔ Resolves (Local value ((executor roles).run value state root).1) root tree
  rw [local_eq]
  exact GeneralNominalCenteredHeadAllocV7Canonical.exact (registry value) (checked_compiled checked) state root tree
    (initial_compiled initial)

theorem saturationTotal : B4TargetV7.SaturationTotal (boundary roles) (executor roles) := by
  intro value checked state root initial
  exact GeneralNominalCenteredHeadAllocV7Canonical.saturationTotal
    (registry value) (checked_compiled checked) state root (initial_compiled initial)

theorem orderIndependent : B4TargetV7.OrderIndependent (boundary roles) (executor roles) := by
  intro value other checked checkedOther order state root initial
  exact GeneralNominalCenteredHeadAllocV7Canonical.orderIndependent
    (registry value) (registry other) (checked_compiled checked) (checked_compiled checkedOther)
    (registry_reorders order) state root (initial_compiled initial)

end Yulang.GeneralNominalCenteredHeadAllocV7Executor
