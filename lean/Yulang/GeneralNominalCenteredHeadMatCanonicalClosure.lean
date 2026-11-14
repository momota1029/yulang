import Yulang.GeneralNominalCenteredHeadMatPermutationSimulation
import Yulang.GeneralNominalCenteredHeadMatHeadReadback
import Yulang.GeneralNominalCenteredHeadMatStepComposition

namespace Yulang.GeneralNominalCenteredHeadMatCanonicalClosure
open GeneralDeclarations GeneralSourceDictionaries GeneralRegistryReordering
open GeneralNominalCenteredHeadMatStepJournal (State)
open GeneralNominalCenteredHeadMatStepKernel (Step)
open GeneralNominalCenteredHeadMatStepBoundary (boundary Local)
open GeneralNominalCenteredHeadMatStepExecutor
open GeneralNominalCenteredHeadMatPermutationSimulation
open GeneralCanonicalRegistry (canonical)
variable {roles : Roles.RoleDecls} {state : State roles}

theorem packet_free_reachable (order : Reorders first last)
    (reachable : B4TargetV6.Reachable (boundary roles) first root state)
    (empty : state.core.erased.current.packets = []) : B4TargetV6.Reachable (boundary roles) last root state := by
  obtain ⟨start,initial,path⟩ := reachable
  exact ⟨start,GeneralNominalCenteredHeadMatStepBoundary.initialReorders order initial,
    packet_free_steps path empty last⟩

theorem canonical_checked (checked : (boundary roles).Checked registry) : (boundary roles).Checked (canonical registry) :=
  ⟨(GeneralCanonicalRegistry.roles registry).trans checked.1,GeneralCanonicalRegistry.canonical_checked checked.2⟩

theorem canonical_exit_lifting (roles : Roles.RoleDecls) : CanonicalExitLifting roles := by
  intro registry checked state root reachable empty
  have order := GeneralCanonicalRegistry.reorders_canonical registry
  have canonicalReachable := packet_free_reachable order reachable empty
  have canonicalExit := terminal_exit (GeneralNominalCenteredHeadMatHeadReadback.progress roles
    (canonical registry) (canonical_checked checked) state root canonicalReachable)
  obtain ⟨start,⟨context,labels,source,point,ground,coverage,rfl⟩,path⟩ := reachable
  have paired := packet_free_self path empty
  obtain ⟨final,trace,related⟩ := steps_backward order checked.1 paired canonicalExit.1
  exact ⟨final,⟨trace,halt_reflects order checked.1 related canonicalExit.2⟩,
    observations related (canonical registry) (canonical_checked checked).1⟩

theorem halted (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state) :
    ∀ next, ¬ Step registry root ((executor roles).run registry state root).1 next :=
  GeneralNominalCenteredHeadMatStepExecutor.halted (GeneralNominalCenteredHeadMatHeadReadback.progress roles)
    registry checked state root reachable

theorem saturationTotal (roles : Roles.RoleDecls) : B4TargetV6.SaturationTotal (boundary roles) (executor roles) :=
  GeneralNominalCenteredHeadMatStepComposition.saturationTotal (GeneralNominalCenteredHeadMatHeadReadback.progress roles)

theorem canonicalLocalOrder (roles : Roles.RoleDecls) : GeneralNominalCenteredHeadMatStepComposition.CanonicalLocalOrder roles :=
  GeneralNominalCenteredHeadMatStepComposition.canonicalLocalOrder (canonical_exit_lifting roles)

theorem orderIndependent (roles : Roles.RoleDecls) : B4TargetV6.OrderIndependent (boundary roles) (executor roles) :=
  GeneralNominalCenteredHeadMatStepComposition.orderIndependent (canonical_exit_lifting roles)

end Yulang.GeneralNominalCenteredHeadMatCanonicalClosure
