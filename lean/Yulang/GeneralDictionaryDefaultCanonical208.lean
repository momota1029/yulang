import Yulang.GeneralDictionaryDefaultExecutor208
import Yulang.GeneralDictionaryDefaultSimulation208

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryDefaultCanonical208
open GeneralDeclarations GeneralSourceDictionaries GeneralRegistryReordering
open GeneralNominalCenteredHeadMatStepJournal (State)
open GeneralDictionaryDefaultBoundary208
open GeneralDictionaryDefaultExecutor208
open GeneralDictionaryDefaultSimulation208
open GeneralNominalCenteredHeadAllocEncoding (registry registry_reorders)
open GeneralCanonicalRegistry (canonical)
variable {roles : Roles.RoleDecls} {state : State roles}

theorem local_order (order : Reorders first last) (state : State roles) (focus frontier) :
    Local first state focus frontier ↔ Local last state focus frontier :=
  local_iff.trans (GeneralNominalCenteredHeadAllocV7Boundary.local_iff.trans
    ((GeneralNominalCenteredHeadAllocV7Boundary.kernel_order (registry_reorders order) state focus frontier).trans
      (GeneralNominalCenteredHeadAllocV7Boundary.local_iff.symm.trans local_iff.symm)))

theorem local_related {first last : State roles} (same : GeneralNominalCenteredHeadMatPermutationLedger.Related relation first last)
    (value : Registry) (roleEq : value.roles = roles) (focus frontier) :
    Local value first focus frontier ↔ Local value last focus frontier :=
  local_iff.trans (GeneralNominalCenteredHeadAllocV7Boundary.local_iff.trans
    ((GeneralNominalCenteredHeadAllocV7Boundary.kernel_related same (registry value) roleEq focus frontier).trans
      (GeneralNominalCenteredHeadAllocV7Boundary.local_iff.symm.trans local_iff.symm)))

theorem packet_free_reachable (order : Reorders first last)
    (reachable : B4TargetV7.Reachable (boundary roles) first root state)
    (empty : state.core.erased.current.packets = []) : B4TargetV7.Reachable (boundary roles) last root state := by
  obtain ⟨start,initial,path⟩ := reachable
  exact ⟨start,initialReorders order initial,packet_free_steps path empty (registry last)⟩

theorem canonical_checked (checked : (boundary roles).Checked value) : (boundary roles).Checked (canonical value) :=
  ⟨(GeneralCanonicalRegistry.roles value).trans checked.1,GeneralCanonicalRegistry.canonical_checked checked.2⟩

theorem canonical_exit_lifting (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (empty : state.core.erased.current.packets = []) : ∃ final, LiftedExit value state root final := by
  have order := GeneralCanonicalRegistry.reorders_canonical value
  have canonicalReachable := packet_free_reachable order reachable empty
  have canonicalExit := terminal_exit (progress (canonical value)
    (canonical_checked checked) state root canonicalReachable)
  obtain ⟨start,⟨context,labels,source,point,ground,coverage,rfl⟩,path⟩ := reachable
  have paired := packet_free_self path empty
  obtain ⟨final,trace,related⟩ := steps_backward (registry_reorders order) checked.1 paired canonicalExit.1
  refine ⟨final,⟨trace,halt_reflects (registry_reorders order) checked.1 related canonicalExit.2⟩,?_⟩
  obtain ⟨relation,pair,_,_⟩ := related
  exact local_related pair (canonical value) (canonical_checked checked).1

theorem final_lifted (checked : (boundary roles).Checked value)
    (reachable : B4TargetV7.Reachable (boundary roles) value root state)
    (empty : state.core.erased.current.packets = []) : LiftedExit value state root (finalState value state root) := by
  classical
  have available := canonical_exit_lifting checked reachable empty
  unfold finalState
  rw [dite_eq_left ⟨empty,available⟩]
  exact Classical.choose_spec available

theorem registry_reachable (reachable : B4TargetV7.Reachable (boundary roles) value root state) :
    ∀ packet ∈ state.core.erased.current.packets, packet.registry = registry value := by
  obtain ⟨start,⟨context,labels,source,point,ground,coverage,rfl⟩,path⟩ := reachable
  exact GeneralNominalCenteredHeadMatStepComposition.registry_built (GeneralDictionaryDefaultTrace208.built_trace path)

theorem distinct_shared_packet_free (different : registry first ≠ registry last)
    (one : B4TargetV7.Reachable (boundary roles) first root state)
    (two : B4TargetV7.Reachable (boundary roles) last root state) : state.core.erased.current.packets = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro packet member
  exact different ((registry_reachable one packet member).symm.trans (registry_reachable two packet member))

def CanonicalLocalOrder (roles : Roles.RoleDecls) : Prop :=
  ∀ first last, (boundary roles).Checked first → (boundary roles).Checked last → (boundary roles).Reorders first last →
    ∀ state root, B4TargetV7.Reachable (boundary roles) first root state → B4TargetV7.Reachable (boundary roles) last root state →
    ∀ demand frontier, Local first ((executor roles).run first state root).1 demand frontier ↔
      Local last ((executor roles).run last state root).1 demand frontier

theorem choice_eq {α : Sort u} {p q : α → Prop} (same : p = q)
    (one : ∃ x, p x) (two : ∃ x, q x) : Classical.choose one = Classical.choose two := by
  cases same
  rfl

theorem canonicalLocalOrder (roles : Roles.RoleDecls) : CanonicalLocalOrder roles := by
  intro first last checked checkedLast order state root reached reachedLast demand frontier
  classical
  have equal := GeneralCanonicalRegistry.canonical_eq order
  by_cases same : registry first = registry last
  · have exits : Exit first state root = Exit last state root := by
      funext final
      simp only [Exit,Step,same]
    have terminals : terminalState first state root = terminalState last state root := by
      unfold terminalState
      rw [exits]
    have lifteds : LiftedExit first state root = LiftedExit last state root := by
      funext final
      simp only [LiftedExit,exits,equal]
    have finals : finalState first state root = finalState last state root := by
      unfold finalState
      by_cases available : state.core.erased.current.packets = [] ∧ ∃ final, LiftedExit first state root final
      · have other : state.core.erased.current.packets = [] ∧ ∃ final, LiftedExit last state root final := by
          simpa only [lifteds] using available
        rw [dite_eq_left available,dite_eq_left other]
        exact choice_eq lifteds _ _
      · have other : ¬ (state.core.erased.current.packets = [] ∧ ∃ final, LiftedExit last state root final) := by
          simpa only [lifteds] using available
        rw [dite_eq_right available,dite_eq_right other]
        exact terminals
    change Local first (finalState first state root) demand frontier ↔ Local last (finalState last state root) demand frontier
    rw [finals]
    exact local_order order _ _ _
  · have empty := distinct_shared_packet_free same reached reachedLast
    have left := (final_lifted checked reached empty).2 demand frontier
    have right := (final_lifted checkedLast reachedLast empty).2 demand frontier
    rw [equal] at left
    apply (local_order (GeneralCanonicalRegistry.reorders_canonical first) _ demand frontier).trans
    change Local (canonical first) (finalState first state root) demand frontier ↔ _
    rw [equal]
    exact left.trans (right.symm.trans
      (local_order (GeneralCanonicalRegistry.reorders_canonical last) _ demand frontier).symm)

end Yulang.GeneralDictionaryDefaultCanonical208
