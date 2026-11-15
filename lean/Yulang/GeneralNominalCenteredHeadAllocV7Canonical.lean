import Yulang.GeneralNominalCenteredHeadAllocV7KernelExecutor

namespace Yulang.GeneralNominalCenteredHeadAllocV7Canonical
open GeneralDeclarations GeneralSourceDictionaries GeneralRegistryReordering
open GeneralNominalCenteredHeadMatStepJournal (State)
open GeneralNominalCenteredHeadMatStepKernel (Step)
open GeneralNominalCenteredHeadAllocV7KernelExecutor
open GeneralNominalCenteredHeadMatPermutationSimulation
open GeneralCanonicalRegistry (canonical)
variable {roles : Roles.RoleDecls} {state : State roles}

theorem progress : Progress roles := GeneralNominalCenteredHeadMatHeadReadback.progress roles

theorem canonical_exit_lifting (roles : Roles.RoleDecls) : CanonicalExitLifting roles := by
  intro registry checked state root reachable empty
  have order := GeneralCanonicalRegistry.reorders_canonical registry
  have canonicalReachable := GeneralNominalCenteredHeadMatCanonicalClosure.packet_free_reachable order reachable empty
  have canonicalExit := terminal_exit (progress (canonical registry)
    (GeneralNominalCenteredHeadMatCanonicalClosure.canonical_checked checked) state root canonicalReachable)
  obtain ⟨start,⟨context,labels,source,point,ground,coverage,rfl⟩,path⟩ := reachable
  have paired := packet_free_self path empty
  obtain ⟨final,trace,related⟩ := steps_backward order checked.1 paired canonicalExit.1
  refine ⟨final,⟨trace,halt_reflects order checked.1 related canonicalExit.2⟩,?_⟩
  obtain ⟨relation,pair,_,_⟩ := related
  exact GeneralNominalCenteredHeadAllocV7Boundary.kernel_related pair (canonical registry)
    (GeneralNominalCenteredHeadMatCanonicalClosure.canonical_checked checked).1

theorem final_lifted (checked : (boundary roles).Checked registry)
    (reachable : B4TargetV7.Reachable (boundary roles) registry root state)
    (empty : state.core.erased.current.packets = []) : LiftedExit registry state root (finalState registry state root) := by
  classical
  have available := canonical_exit_lifting roles registry checked state root reachable empty
  unfold finalState
  rw [dite_eq_left ⟨empty,available⟩]
  exact Classical.choose_spec available

def CanonicalLocalOrder (roles : Roles.RoleDecls) : Prop :=
  ∀ first last, (boundary roles).Checked first → (boundary roles).Checked last → (boundary roles).Reorders first last →
    ∀ state root, B4TargetV7.Reachable (boundary roles) first root state → B4TargetV7.Reachable (boundary roles) last root state →
    ∀ demand frontier, Local first ((executor roles).run first state root).1 demand frontier ↔
      Local last ((executor roles).run last state root).1 demand frontier

theorem canonicalLocalOrder (roles : Roles.RoleDecls) : CanonicalLocalOrder roles := by
  intro first last checked checkedLast order state root reached reachedLast demand frontier
  classical
  by_cases same : first = last
  · subst last; exact Iff.rfl
  have empty := GeneralNominalCenteredHeadMatStepComposition.distinct_shared_packet_free same reached reachedLast
  have left := (final_lifted checked reached empty).2 demand frontier
  have right := (final_lifted checkedLast reachedLast empty).2 demand frontier
  have equal := GeneralCanonicalRegistry.canonical_eq order
  rw [equal] at left
  apply (GeneralNominalCenteredHeadAllocV7Boundary.kernel_order (GeneralCanonicalRegistry.reorders_canonical first) _ demand frontier).trans
  change Local (canonical first) (finalState first state root) demand frontier ↔ _
  rw [equal]
  exact left.trans (right.symm.trans
    (GeneralNominalCenteredHeadAllocV7Boundary.kernel_order (GeneralCanonicalRegistry.reorders_canonical last) _ demand frontier).symm)

theorem halted (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (reachable : B4TargetV7.Reachable (boundary roles) registry root state) :
    ∀ next, ¬ Step registry root ((executor roles).run registry state root).1 next :=
  GeneralNominalCenteredHeadAllocV7KernelExecutor.halted progress registry checked state root reachable

theorem exact : B4TargetV7.Exact (boundary roles) (executor roles) := by
  intro registry checked state root tree _initial
  exact GeneralNominalCenteredHeadAllocV7KernelExecutor.exact registry checked state root tree

theorem saturationTotal : B4TargetV7.SaturationTotal (boundary roles) (executor roles) := by
  intro registry checked state root initial
  have reachable : B4TargetV7.Reachable (boundary roles) registry root state := ⟨state,initial,.refl⟩
  have trace := execution registry checked state root reachable
  have stable := GeneralNominalCenteredHeadMatStepKernel.closure (halted registry checked state root reachable)
  exact ⟨progress registry checked state root reachable,trace,stable.1,stable.2,
    GeneralNominalCenteredHeadMatStepKernel.steps_models trace⟩

theorem orderIndependent : B4TargetV7.OrderIndependent (boundary roles) (executor roles) := by
  intro registry other checked checkedOther order state root initial
  have initialOther := GeneralNominalCenteredHeadMatStepBoundary.initialReorders order initial
  have resolved := (exact registry checked state root _ initial).mp rfl
  have transported := B4Skeleton.resolves_transport
    (fun demand frontier given => (canonicalLocalOrder roles registry other checked checkedOther order state root
      ⟨state,initial,.refl⟩ ⟨state,initialOther,.refl⟩ demand frontier).mp given) resolved
  have equal := (exact other checkedOther state root _ initialOther).mpr transported
  rw [equal]
  exact B4TargetV3.same_diagnostic_refl (B4TargetV7.base (boundary roles)) (fun _ => rfl) _

end Yulang.GeneralNominalCenteredHeadAllocV7Canonical
