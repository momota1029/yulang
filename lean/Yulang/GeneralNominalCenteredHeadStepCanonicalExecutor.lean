import Yulang.GeneralNominalCenteredHeadStepRegistry
import Yulang.GeneralNominalCenteredHeadStepAccessibility
import Yulang.GeneralNominalCenteredHeadStepWhere

set_option backward.isDefEq.respectTransparency false

/-! A canonical-registry executor for the V6 local relation. Its executions
and halting certificates use the original registry and the successor Step.
No final-state confluence or effect-coverage premise is required. -/
namespace Yulang.GeneralNominalCenteredHeadStepCanonicalExecutor
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadStepBoundary (boundary vocabulary Local local_total local_functional)
open GeneralCanonicalRegistry (canonical)
open CommonRoleOutermostResolver
variable {roles : Roles.RoleDecls}
variable {state : State roles} {root : Occurrence roles}

def Exit (registry : Registry) (state : State roles) (root : Occurrence roles) (final : State roles) : Prop :=
  B4Target.Steps (Step registry root) state final ∧ ∀ next, ¬ Step registry root final next

theorem exit_exists (checked : (boundary roles).Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state) : ∃ final, Exit registry state root final := by
  obtain ⟨final,path,halted,_⟩ := GeneralNominalCenteredHeadStepAccessibility.terminal registry checked state root reachable
  exact ⟨final,path,halted⟩

noncomputable def terminalState (registry : Registry) (state : State roles) (root : Occurrence roles) : State roles := by
  classical
  exact if eligible : (boundary roles).Checked registry ∧ B4TargetV6.Reachable (boundary roles) registry root state
    then Classical.choose (exit_exists eligible.1 eligible.2) else state

theorem terminal_exit (checked : (boundary roles).Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state) : Exit registry state root (terminalState registry state root) := by
  classical
  unfold terminalState
  rw [dite_eq_left ⟨checked,reachable⟩]
  exact Classical.choose_spec (exit_exists checked reachable)

def LiftedExit (registry : Registry) (state : State roles) (root : Occurrence roles) (final : State roles) : Prop :=
  Exit registry state root final ∧ ∀ demand frontier,
    Local (canonical registry) final demand frontier ↔ Local (canonical registry) (terminalState (canonical registry) state root) demand frontier

theorem canonical_checked (checked : (boundary roles).Checked registry) : (boundary roles).Checked (canonical registry) :=
  ⟨(GeneralCanonicalRegistry.roles registry).trans checked.1,GeneralCanonicalRegistry.canonical_checked checked.2⟩

theorem canonical_exit_lifting (checked : (boundary roles).Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (empty : state.core.erased.current.packets = []) : ∃ final, LiftedExit registry state root final := by
  have order := GeneralCanonicalRegistry.reorders_canonical registry
  have canonicalReachable := GeneralNominalCenteredHeadStepRegistry.packet_free_reachable order reachable empty
  have canonicalExit := terminal_exit (canonical_checked checked) canonicalReachable
  have initial := GeneralNominalCenteredHeadStepRegistry.packet_free_self (canonical registry) reachable empty
  obtain ⟨final,path,related⟩ := GeneralNominalCenteredHeadStepSimulation.steps_backward order checked.1 initial canonicalExit.1
  exact ⟨final,⟨path,GeneralNominalCenteredHeadStepSimulation.halt_reflects order checked.1 related canonicalExit.2⟩,
    GeneralNominalCenteredHeadStepSimulation.observations (canonical_checked checked).1 related⟩

noncomputable def finalState (registry : Registry) (state : State roles) (root : Occurrence roles) : State roles := by
  classical
  exact if lifted : state.core.erased.current.packets = [] ∧ ∃ final, LiftedExit registry state root final
    then Classical.choose lifted.2 else terminalState registry state root

theorem final_exit (checked : (boundary roles).Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state) : Exit registry state root (finalState registry state root) := by
  classical
  unfold finalState
  split
  · rename_i lifted
    exact (Classical.choose_spec lifted.2).1
  · exact terminal_exit checked reachable

theorem final_lifted (checked : (boundary roles).Checked registry)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state)
    (empty : state.core.erased.current.packets = []) : LiftedExit registry state root (finalState registry state root) := by
  classical
  have available := canonical_exit_lifting checked reachable empty
  unfold finalState
  rw [dite_eq_left ⟨empty,available⟩]
  exact Classical.choose_spec available

noncomputable def frontiers (roles : Roles.RoleDecls) (registry : Registry) (state : State roles) : Protocol (Occurrence roles) := by
  classical
  exact { frontier := fun root => if checked : Checked registry then Classical.choose (local_total registry checked state root) else .pending
          Local := Local registry state }

theorem frontierLocal (checked : (boundary roles).Checked registry) (state : State roles) (root : Occurrence roles) (frontier) :
    (frontiers roles registry state).frontier root = frontier ↔ Local registry state root frontier := by
  classical
  have valid := Classical.choose_spec (local_total registry checked.2 state root)
  change (if checked : Checked registry then Classical.choose (local_total registry checked state root) else .pending) = frontier ↔ _
  rw [dite_eq_left checked.2]
  exact ⟨fun same => same ▸ valid,fun chosen => local_functional valid chosen⟩

theorem localIdentity (registry : Registry) (state : State roles) : (frontiers roles registry state).Local = Local registry state := rfl

noncomputable def diagnostic (registry : Registry) (state : State roles) (root : Occurrence roles) : Tree := by
  classical
  exact if exact : FrontierExact (frontiers roles registry state) then
    resolve (frontiers roles registry state) exact root
      (GeneralNominalCenteredHeadStepWhere.whereAccessible registry state root) else .pending

theorem diagnostic_exact (registry : Registry) (state : State roles) (root : Occurrence roles)
    (exact : FrontierExact (frontiers roles registry state))
    (accessible : Acc (Child (frontiers roles registry state).Local) root) :
    diagnostic registry state root = resolve (frontiers roles registry state) exact root accessible := by
  classical
  simp [diagnostic,exact]

noncomputable def executor (roles : Roles.RoleDecls) : B4TargetV3.Executor (vocabulary roles) where
  run registry state root := let final := finalState registry state root; (final,diagnostic registry final root)

theorem execution (registry : Registry) (checked : (boundary roles).Checked registry) (state : State roles) (root : Occurrence roles)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state) :
    B4Target.Steps (Step registry root) state ((executor roles).run registry state root).1 := (final_exit checked reachable).1

theorem halted (registry : Registry) (checked : (boundary roles).Checked registry) (state : State roles) (root : Occurrence roles)
    (reachable : B4TargetV6.Reachable (boundary roles) registry root state) :
    ∀ next, ¬ Step registry root ((executor roles).run registry state root).1 next := (final_exit checked reachable).2

theorem treeExecution (registry : Registry) (state : State roles) (root : Occurrence roles)
    (exact : FrontierExact (frontiers roles registry ((executor roles).run registry state root).1))
    (accessible : Acc (Child (frontiers roles registry ((executor roles).run registry state root).1).Local) root) :
    ((executor roles).run registry state root).2 =
      resolve (frontiers roles registry ((executor roles).run registry state root).1) exact root accessible :=
  diagnostic_exact registry _ root exact accessible

/-- The V5 field's full shared-reachable-input quantifiers, with V6 Local. -/
def CanonicalLocalOrder (roles : Roles.RoleDecls) : Prop :=
  ∀ first last, (boundary roles).Checked first → (boundary roles).Checked last → (boundary roles).Reorders first last →
    ∀ state root, B4TargetV6.Reachable (boundary roles) first root state → B4TargetV6.Reachable (boundary roles) last root state →
    ∀ demand frontier, Local first ((executor roles).run first state root).1 demand frontier ↔
      Local last ((executor roles).run last state root).1 demand frontier

theorem canonicalLocalOrder : CanonicalLocalOrder roles := by
  intro first last checked checkedLast order state root reached reachedLast demand frontier
  classical
  by_cases same : first = last
  · subst last; exact Iff.rfl
  have empty := GeneralNominalCenteredHeadStepRegistry.distinct_shared_packet_free same reached reachedLast
  have left := (final_lifted checked reached empty).2 demand frontier
  have right := (final_lifted checkedLast reachedLast empty).2 demand frontier
  have equal := GeneralCanonicalRegistry.canonical_eq order
  rw [equal] at left
  apply (GeneralNominalCenteredHeadStepOrder.local_iff (GeneralCanonicalRegistry.reorders_canonical first) _ demand frontier).trans
  change Local (canonical first) (finalState first state root) demand frontier ↔ _
  rw [equal]
  exact left.trans (right.symm.trans
    (GeneralNominalCenteredHeadStepOrder.local_iff (GeneralCanonicalRegistry.reorders_canonical last) _ demand frontier).symm)

theorem exact : B4TargetV6.Exact (boundary roles) (executor roles) := by
  intro registry checked state root tree _initial
  have front : FrontierExact (frontiers roles registry ((executor roles).run registry state root).1) :=
    fun demand frontier => frontierLocal checked _ demand frontier
  have accessible := GeneralNominalCenteredHeadStepWhere.whereAccessible registry ((executor roles).run registry state root).1 root
  rw [treeExecution registry state root front accessible]
  exact resolve_tree_exact_of_frontier_exact (frontiers roles registry _) front root accessible tree

theorem saturationTotal : B4TargetV6.SaturationTotal (boundary roles) (executor roles) := by
  intro registry checked state root initial
  have reachable : B4TargetV6.Reachable (boundary roles) registry root state := ⟨state,initial,.refl⟩
  have trace := execution registry checked state root reachable
  have stable := GeneralNominalCenteredHeadStepKernel.closure (halted registry checked state root reachable)
  exact ⟨GeneralNominalCenteredHeadStepAccessibility.progress registry checked state root reachable,
    trace,stable.1,stable.2,steps_models trace⟩

theorem orderIndependent : B4TargetV6.OrderIndependent (boundary roles) (executor roles) := by
  intro registry other checked checkedOther order state root initial
  have initialOther := GeneralNominalCenteredHeadStepRegistry.initial_reorders order initial
  have resolved := (exact registry checked state root _ initial).mp rfl
  have transported := B4Skeleton.resolves_transport
    (fun demand frontier given => (canonicalLocalOrder registry other checked checkedOther order state root
      ⟨state,initial,.refl⟩ ⟨state,initialOther,.refl⟩ demand frontier).mp given) resolved
  have equal := (exact other checkedOther state root _ initialOther).mpr transported
  rw [equal]
  exact B4TargetV3.same_diagnostic_refl (boundary roles).toV5.toSourceBoundary
    (GeneralNominalCenteredAdministrativeComposition.dictionaryRefl (roles := roles)) _

end Yulang.GeneralNominalCenteredHeadStepCanonicalExecutor
