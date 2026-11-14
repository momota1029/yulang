import Yulang.GeneralNominalCenteredHeadWFBoundary

set_option backward.isDefEq.respectTransparency false

/-! Restriction of the existing head-step results to well-formed sources.
The executor is literally the existing canonical-registry executor. -/
namespace Yulang.GeneralNominalCenteredHeadWFTransfer
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalCenteredHeadStepEffects (State)
open GeneralNominalCenteredHeadWFBoundary
variable {roles : Roles.RoleDecls}

noncomputable abbrev executor := GeneralNominalCenteredHeadStepCanonicalExecutor.executor
noncomputable abbrev frontiers := GeneralNominalCenteredHeadStepCanonicalExecutor.frontiers

theorem progress (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state) :
    Acc (fun next current => (boundary roles).Step registry root current next) state :=
  GeneralNominalCenteredHeadStepAccessibility.progress registry checked state root (reachable_old reachable)

theorem stepModels (registry : Registry) (checked : (boundary roles).Checked registry)
    (root : Occurrence roles) (before after : State roles)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root before)
    (step : (boundary roles).Step registry root before after) :
    ∀ model, (boundary roles).Models after model → (boundary roles).Models before model :=
  GeneralNominalCenteredHeadStepBoundary.boundary_stepModels registry checked root before after (reachable_old reachable) step

theorem closure (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (halted : ∀ after, ¬ (boundary roles).Step registry root state after) :
    (boundary roles).Stable registry state root ∧
      ∀ child, (boundary roles).Generated registry state root child → (boundary roles).Stable registry state child :=
  GeneralNominalCenteredHeadStepBoundary.boundary_closure registry checked state root (reachable_old reachable) halted

theorem execution (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state) :
    B4Target.Steps ((boundary roles).Step registry root) state ((executor roles).run registry state root).1 :=
  GeneralNominalCenteredHeadStepCanonicalExecutor.execution registry checked state root (reachable_old reachable)

theorem halted (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state) :
    ∀ after, ¬ (boundary roles).Step registry root ((executor roles).run registry state root).1 after :=
  GeneralNominalCenteredHeadStepCanonicalExecutor.halted registry checked state root (reachable_old reachable)

theorem frontierLocal (checked : (boundary roles).Checked registry) (state : State roles)
    (root : Occurrence roles) (frontier) :
    (frontiers roles registry state).frontier root = frontier ↔ Local registry state root frontier :=
  (GeneralNominalCenteredHeadStepCanonicalExecutor.frontierLocal checked state root frontier).trans local_iff.symm

theorem localIdentity (registry : Registry) (state : State roles) :
    (frontiers roles registry state).Local = Local registry state := (local_eq registry state).symm

theorem whereAccessible (registry : Registry) (state : State roles) (root : Occurrence roles) :
    Acc (Child (Local registry state)) root := by
  rw [local_eq]
  exact GeneralNominalCenteredHeadStepWhere.whereAccessible registry state root

theorem treeExecution (registry : Registry) (state : State roles) (root : Occurrence roles)
    (exact : FrontierExact (frontiers roles registry ((executor roles).run registry state root).1))
    (accessible : Acc (Child (frontiers roles registry ((executor roles).run registry state root).1).Local) root) :
    ((executor roles).run registry state root).2 =
      resolve (frontiers roles registry ((executor roles).run registry state root).1) exact root accessible :=
  GeneralNominalCenteredHeadStepCanonicalExecutor.treeExecution registry state root exact accessible

theorem dictionaryRefl (dictionary : Dictionary) : (boundary roles).DictionaryEquivalent dictionary dictionary :=
  GeneralNominalCenteredAdministrativeComposition.dictionaryRefl (roles := roles) dictionary

theorem initialReorders (order : (boundary roles).Reorders first last)
    (initial : (boundary roles).Initial first root state) : (boundary roles).Initial last root state :=
  initial_reorders order initial

def CanonicalLocalOrder (roles : Roles.RoleDecls) : Prop :=
  ∀ first last, (boundary roles).Checked first → (boundary roles).Checked last → (boundary roles).Reorders first last →
    ∀ state root, B4TargetV6.Reachable (boundary roles) first root state → B4TargetV6.Reachable (boundary roles) last root state →
    ∀ demand frontier, Local first ((executor roles).run first state root).1 demand frontier ↔
      Local last ((executor roles).run last state root).1 demand frontier

theorem canonicalLocalOrder : CanonicalLocalOrder roles := by
  intro first last checked checkedLast order state root reached reachedLast demand frontier
  exact local_iff.trans ((GeneralNominalCenteredHeadStepCanonicalExecutor.canonicalLocalOrder
    first last checked checkedLast order state root (reachable_old reached) (reachable_old reachedLast) demand frontier).trans local_iff.symm)

theorem exact : B4TargetV6.Exact (boundary roles) (executor roles) := by
  intro registry checked state root tree initial
  have prior := GeneralNominalCenteredHeadStepCanonicalExecutor.exact registry checked state root tree initial.1
  constructor
  · intro equal
    exact B4Skeleton.resolves_transport (fun _ _ localRule => local_iff.mpr localRule) (prior.mp equal)
  · intro resolved
    exact prior.mpr (B4Skeleton.resolves_transport (fun _ _ localRule => local_iff.mp localRule) resolved)

theorem saturationTotal : B4TargetV6.SaturationTotal (boundary roles) (executor roles) := by
  intro registry checked state root initial
  exact GeneralNominalCenteredHeadStepCanonicalExecutor.saturationTotal registry checked state root initial.1

theorem orderIndependent : B4TargetV6.OrderIndependent (boundary roles) (executor roles) := by
  intro registry other checked checkedOther order state root initial
  exact GeneralNominalCenteredHeadStepCanonicalExecutor.orderIndependent registry other checked checkedOther order state root initial.1

end Yulang.GeneralNominalCenteredHeadWFTransfer
