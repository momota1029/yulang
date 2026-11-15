import Yulang.GeneralDictionaryDefaultBoundary208
import Yulang.GeneralDictionaryDefaultCover208

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryDefaultExecutor208
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalCenteredHeadMatStepJournal (State)
open GeneralDictionaryDefaultBoundary208
open GeneralCanonicalRegistry (canonical)
variable {roles : Roles.RoleDecls}

def Exit (registry : Registry) (state : State roles) (root : Occurrence roles) (final : State roles) : Prop :=
  B4Target.Steps (Step registry root) state final ∧ ∀ next, ¬ Step registry root final next

noncomputable def terminalState (registry : Registry) (state : State roles) (root : Occurrence roles) : State roles := by
  classical
  exact if available : ∃ final, Exit registry state root final then Classical.choose available else state

theorem terminal_execution (registry : Registry) (state : State roles) (root : Occurrence roles) :
    B4Target.Steps (Step registry root) state (terminalState registry state root) := by
  classical
  unfold terminalState
  split
  · rename_i available
    exact (Classical.choose_spec available).1
  · exact .refl

theorem terminal_exit (accessible : Acc (fun next current => Step registry root current next) state) :
    Exit registry state root (terminalState registry state root) := by
  classical
  have available : ∃ final, Exit registry state root final := GeneralNominalActualBoundary.terminal_of_accessible accessible
  unfold terminalState
  rw [dite_eq_left available]
  exact Classical.choose_spec available

def LiftedExit (registry : Registry) (state : State roles) (root : Occurrence roles) (final : State roles) : Prop :=
  Exit registry state root final ∧ ∀ demand frontier,
    Local (canonical registry) final demand frontier ↔
      Local (canonical registry) (terminalState (canonical registry) state root) demand frontier

noncomputable def finalState (registry : Registry) (state : State roles) (root : Occurrence roles) : State roles := by
  classical
  exact if lifted : state.core.erased.current.packets = [] ∧ ∃ final, LiftedExit registry state root final then
    Classical.choose lifted.2 else terminalState registry state root

theorem final_execution (registry : Registry) (state : State roles) (root : Occurrence roles) :
    B4Target.Steps (Step registry root) state (finalState registry state root) := by
  classical
  unfold finalState
  split
  · rename_i available
    exact (Classical.choose_spec available.2).1.1
  · exact terminal_execution registry state root

theorem final_exit (accessible : Acc (fun next current => Step registry root current next) state) :
    Exit registry state root (finalState registry state root) := by
  classical
  unfold finalState
  split
  · rename_i available
    exact (Classical.choose_spec available.2).1
  · exact terminal_exit accessible

noncomputable def frontiers (roles : Roles.RoleDecls) (registry : Registry) (state : State roles) :=
  GeneralNominalCenteredHeadAllocV7Executor.frontiers roles registry state

theorem frontierLocal (checked : (boundary roles).Checked registry) (state : State roles) (root : Occurrence roles) (frontier) :
    (frontiers roles registry state).frontier root = frontier ↔ Local registry state root frontier :=
  (GeneralNominalCenteredHeadAllocV7Executor.frontierLocal checked state root frontier).trans local_iff.symm

theorem localIdentity (registry : Registry) (state : State roles) : (frontiers roles registry state).Local = Local registry state :=
  (GeneralNominalCenteredHeadAllocV7Executor.localIdentity registry state).trans local_eq.symm

noncomputable def diagnostic (registry : Registry) (state : State roles) (root : Occurrence roles) : Tree := by
  classical
  exact if exact : FrontierExact (frontiers roles registry state) then
    resolve (frontiers roles registry state) exact root
      (by rw [localIdentity]; exact whereAccessible registry state root) else .pending

noncomputable def executor (roles : Roles.RoleDecls) : B4TargetV3.Executor (GeneralNominalCenteredHeadMatStepLocal.vocabulary roles) where
  run registry state root := let final := finalState registry state root; (final,diagnostic registry final root)

theorem execution (registry : Registry) (_checked : (boundary roles).Checked registry) (state : State roles) (root : Occurrence roles)
    (_reachable : B4TargetV7.Reachable (boundary roles) registry root state) :
    B4Target.Steps (Step registry root) state ((executor roles).run registry state root).1 := final_execution registry state root

theorem halted_of_accessible (accessible : Acc (fun next current => Step registry root current next) state) :
    ∀ next, ¬ Step registry root ((executor roles).run registry state root).1 next := (final_exit accessible).2

theorem treeExecution (registry : Registry) (state : State roles) (root : Occurrence roles)
    (exact : FrontierExact (frontiers roles registry ((executor roles).run registry state root).1))
    (accessible : Acc (Child (frontiers roles registry ((executor roles).run registry state root).1).Local) root) :
    ((executor roles).run registry state root).2 =
      resolve (frontiers roles registry ((executor roles).run registry state root).1) exact root accessible := by
  classical
  change FrontierExact (frontiers roles registry (finalState registry state root)) at exact
  simp [executor,diagnostic,exact]

theorem progress (registry : Registry) (checked : (boundary roles).Checked registry) (state : State roles)
    (root : Occurrence roles) (reachable : B4TargetV7.Reachable (boundary roles) registry root state) :
    Acc (fun next current => Step registry root current next) state := by
  obtain ⟨start,initial,path⟩ := reachable
  have compiled := GeneralNominalCenteredHeadAllocBoundary.initial_compiled initial
  obtain ⟨context,labels,source,point,ground,coverage,rfl⟩ := compiled
  have accessible := GeneralDictionaryDefaultCover208.ground_accessible
    (GeneralNominalCenteredHeadAllocBoundary.checked_compiled checked).2 source point ground coverage
  induction path with
  | refl => exact accessible
  | tail path step ih => exact ih.inv step

theorem halted (registry : Registry) (checked : (boundary roles).Checked registry) (state : State roles)
    (root : Occurrence roles) (reachable : B4TargetV7.Reachable (boundary roles) registry root state) :
    ∀ next, ¬ Step registry root ((executor roles).run registry state root).1 next :=
  halted_of_accessible (progress registry checked state root reachable)

theorem exact (registry : Registry) (checked : (boundary roles).Checked registry) (state : State roles)
    (root : Occurrence roles) (tree : Tree) :
    ((executor roles).run registry state root).2 = tree ↔
      Resolves (Local registry ((executor roles).run registry state root).1) root tree := by
  have front : FrontierExact (frontiers roles registry ((executor roles).run registry state root).1) :=
    fun demand frontier => (frontierLocal checked _ demand frontier).trans (by rw [localIdentity])
  have accessible : Acc (Child (frontiers roles registry ((executor roles).run registry state root).1).Local) root := by
    rw [localIdentity]
    exact whereAccessible registry _ root
  rw [treeExecution registry state root front accessible,← localIdentity]
  exact resolve_tree_exact_of_frontier_exact (frontiers roles registry _) front root accessible tree

end Yulang.GeneralDictionaryDefaultExecutor208
