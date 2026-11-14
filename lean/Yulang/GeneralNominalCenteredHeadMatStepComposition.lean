import Yulang.GeneralNominalCenteredHeadMatStepOrder
import Yulang.GeneralNominalCenteredHeadMatStepCompletion

namespace Yulang.GeneralNominalCenteredHeadMatStepComposition
open GeneralDeclarations GeneralSourceDictionaries GeneralRegistryReordering
open GeneralNominalCenteredHeadMatStepJournal (State)
open GeneralNominalCenteredHeadMatStepKernel (Step)
open GeneralNominalCenteredHeadMatStepBoundary
open GeneralNominalCenteredHeadMatStepExecutor
open GeneralCanonicalRegistry (canonical)
variable {roles : Roles.RoleDecls} {state : State roles}

theorem registry_built (built : GeneralNominalCenteredHeadMatStepHistory.Built registry context root state) :
    ∀ packet ∈ state.core.erased.current.packets, packet.registry = registry := by
  induction built with
  | initial => intro packet member; cases member
  | install prior effect snapshot registryEq ih =>
      intro packet member
      rcases List.mem_cons.mp member with rfl | member
      · exact effect.frame.registry_eq.trans registryEq
      · exact ih packet member
  | merge _ _ _ _ ih => exact ih
  | context _ _ _ _ ih => exact ih

theorem registry_reachable (reachable : B4TargetV6.Reachable (boundary roles) registry root state) :
    ∀ packet ∈ state.core.erased.current.packets, packet.registry = registry := by
  obtain ⟨first,⟨context,labels,source,point,ground,coverage,rfl⟩,path⟩ := reachable
  exact registry_built (GeneralNominalCenteredHeadMatStepTrace.built_trace path)

theorem distinct_shared_packet_free (different : first ≠ last)
    (one : B4TargetV6.Reachable (boundary roles) first root state)
    (two : B4TargetV6.Reachable (boundary roles) last root state) : state.core.erased.current.packets = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro packet member
  exact different ((registry_reachable one packet member).symm.trans (registry_reachable two packet member))

theorem final_lifted (lifting : CanonicalExitLifting roles) (checked : (boundary roles).Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (empty : state.core.erased.current.packets = []) : LiftedExit registry state root (finalState registry state root) := by
  classical
  have available := lifting registry checked state root reachable empty
  unfold finalState
  rw [dite_eq_left ⟨empty,available⟩]
  exact Classical.choose_spec available

def CanonicalLocalOrder (roles : Roles.RoleDecls) : Prop :=
  ∀ first last, (boundary roles).Checked first → (boundary roles).Checked last → (boundary roles).Reorders first last →
    ∀ state root, B4TargetV6.Reachable (boundary roles) first root state → B4TargetV6.Reachable (boundary roles) last root state →
    ∀ demand frontier, Local first ((executor roles).run first state root).1 demand frontier ↔
      Local last ((executor roles).run last state root).1 demand frontier

theorem canonicalLocalOrder (lifting : CanonicalExitLifting roles) : CanonicalLocalOrder roles := by
  intro first last checked checkedLast order state root reached reachedLast demand frontier
  classical
  by_cases same : first = last
  · subst last; exact Iff.rfl
  have empty := distinct_shared_packet_free same reached reachedLast
  have left := (final_lifted lifting checked reached empty).2 demand frontier
  have right := (final_lifted lifting checkedLast reachedLast empty).2 demand frontier
  have equal := GeneralCanonicalRegistry.canonical_eq order
  rw [equal] at left
  apply (GeneralNominalCenteredHeadMatStepOrder.local_iff (GeneralCanonicalRegistry.reorders_canonical first) _ demand frontier).trans
  change Local (canonical first) (finalState first state root) demand frontier ↔ _
  rw [equal]
  exact left.trans (right.symm.trans
    (GeneralNominalCenteredHeadMatStepOrder.local_iff (GeneralCanonicalRegistry.reorders_canonical last) _ demand frontier).symm)

theorem exact : B4TargetV6.Exact (boundary roles) (executor roles) := by
  intro registry checked state root tree _initial
  exact GeneralNominalCenteredHeadMatStepExecutor.exact registry checked state root tree

theorem saturationTotal (progress : Progress roles) : B4TargetV6.SaturationTotal (boundary roles) (executor roles) := by
  intro registry checked state root initial
  have reachable : B4TargetV6.Reachable (boundary roles) registry root state := ⟨state,initial,.refl⟩
  have trace := execution registry checked state root reachable
  have stable := GeneralNominalCenteredHeadMatStepKernel.closure (halted progress registry checked state root reachable)
  exact ⟨progress registry checked state root reachable,trace,stable.1,stable.2,
    GeneralNominalCenteredHeadMatStepKernel.steps_models trace⟩

theorem orderIndependent (lifting : CanonicalExitLifting roles) : B4TargetV6.OrderIndependent (boundary roles) (executor roles) := by
  intro registry other checked checkedOther order state root initial
  have initialOther := initialReorders order initial
  have resolved := (exact registry checked state root _ initial).mp rfl
  have transported := B4Skeleton.resolves_transport
    (fun demand frontier given => (canonicalLocalOrder lifting registry other checked checkedOther order state root
      ⟨state,initial,.refl⟩ ⟨state,initialOther,.refl⟩ demand frontier).mp given) resolved
  have equal := (exact other checkedOther state root _ initialOther).mpr transported
  rw [equal]
  exact B4TargetV3.same_diagnostic_refl (boundary roles).toV5.toSourceBoundary
    (dictionaryRefl (roles := roles)) _

end Yulang.GeneralNominalCenteredHeadMatStepComposition
