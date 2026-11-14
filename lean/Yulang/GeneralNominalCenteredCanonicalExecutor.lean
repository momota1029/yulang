import Yulang.GeneralNominalCenteredRegistryPassive
import Yulang.GeneralNominalCenteredFixedChoice

/-! A total canonical-registry executor with original-registry exits.
Eleven bridges hold independently of exit lifting. The order bridge follows
from the named canonical exit-lifting obligation. -/
namespace Yulang.GeneralNominalCenteredCanonicalExecutor
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralNominalCenteredAdministrativeLocal
open GeneralNominalCenteredGroundComposition (terminalState)
open GeneralCanonicalRegistry (canonical)
open GeneralNominalCenteredFixedChoice (Exit)
open CommonRoleOutermostResolver

variable {roles : Roles.RoleDecls}

theorem canonical_checked (checked : (boundary roles).Checked registry) :
    (boundary roles).Checked (canonical registry) :=
  ⟨(GeneralCanonicalRegistry.roles registry).trans checked.1,
    GeneralCanonicalRegistry.canonical_checked checked.2⟩

def LiftedExit (registry : Registry) (state : State roles) (root : Occurrence roles)
    (final : State roles) : Prop :=
  Exit registry state root final ∧ ∀ demand frontier,
    Local (canonical registry) final demand frontier ↔
      Local (canonical registry) (terminalState (canonical registry) state root) demand frontier

/-- An original execution realizing the one chosen canonical observation.
This is an existence obligation, not confluence of arbitrary exits. -/
def CanonicalExitLifting (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (boundary roles).Checked registry → ∀ state root,
    B4TargetV5.Reachable (boundary roles) registry root state →
    state.erased.current.packets = [] → ∃ final, LiftedExit registry state root final

theorem lifted_exit_of_canonical (checked : (boundary roles).Checked registry)
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (fixed : canonical registry = registry) :
    LiftedExit registry state root (terminalState registry state root) := by
  refine ⟨⟨GeneralNominalCenteredAdministrativeComposition.execution registry checked state root reachable,
    GeneralNominalCenteredAdministrativeComposition.halted registry checked state root reachable⟩,?_⟩
  rw [fixed]
  exact fun _ _ => Iff.rfl

noncomputable def finalState (registry : Registry) (state : State roles) (root : Occurrence roles) : State roles := by
  classical
  exact if lifted : state.erased.current.packets = [] ∧ ∃ final, LiftedExit registry state root final
    then Classical.choose lifted.2 else terminalState registry state root

theorem final_exit (checked : (boundary roles).Checked registry)
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state) :
    Exit registry state root (finalState registry state root) := by
  classical
  unfold finalState
  split
  · rename_i lifted
    exact (Classical.choose_spec lifted.2).1
  · exact ⟨GeneralNominalCenteredAdministrativeComposition.execution registry checked state root reachable,
      GeneralNominalCenteredAdministrativeComposition.halted registry checked state root reachable⟩

theorem final_nonempty (nonempty : state.erased.current.packets ≠ []) :
    finalState registry state root = terminalState registry state root := by
  classical
  simp only [finalState,nonempty,false_and,dite_eq_right,not_false_eq_true]

theorem final_lifted (empty : state.erased.current.packets = [])
    (lifted : ∃ final, LiftedExit registry state root final) :
    LiftedExit registry state root (finalState registry state root) := by
  classical
  unfold finalState
  rw [dite_eq_left ⟨empty,lifted⟩]
  exact Classical.choose_spec lifted

noncomputable def executor (roles : Roles.RoleDecls) :
    B4TargetV3.Executor (GeneralNominalCenteredBoundary.vocabulary roles) where
  run registry state root :=
    let final := finalState registry state root
    (final,GeneralNominalCenteredAdministrativeComposition.diagnostic registry final root)

theorem execution (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state) :
    B4Target.Steps ((boundary roles).Step registry root) state ((executor roles).run registry state root).1 :=
  (final_exit checked reachable).1

theorem halted (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state) (next : State roles) :
    ¬ (boundary roles).Step registry root ((executor roles).run registry state root).1 next :=
  (final_exit checked reachable).2 next

theorem treeExecution (registry : Registry) (_checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (_reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (exact : FrontierExact (frontiers roles registry ((executor roles).run registry state root).1))
    (accessible : Acc (Child (frontiers roles registry ((executor roles).run registry state root).1).Local) root) :
    ((executor roles).run registry state root).2 =
      resolve (frontiers roles registry ((executor roles).run registry state root).1) exact root accessible :=
  GeneralNominalCenteredAdministrativeComposition.diagnostic_exact registry _ root exact accessible

def CanonicalLocalOrder (roles : Roles.RoleDecls) : Prop :=
  ∀ first last, (boundary roles).Checked first → (boundary roles).Checked last →
    (boundary roles).Reorders first last → ∀ state root,
    B4TargetV5.Reachable (boundary roles) first root state →
    B4TargetV5.Reachable (boundary roles) last root state → ∀ demand frontier,
    B4TargetV3.Local (boundary roles).toSourceBoundary first ((executor roles).run first state root).1 demand frontier ↔
      B4TargetV3.Local (boundary roles).toSourceBoundary last ((executor roles).run last state root).1 demand frontier

theorem canonicalLocalOrder (lifting : CanonicalExitLifting roles) : CanonicalLocalOrder roles := by
  intro first last checked checkedLast order state root reached reachedLast demand frontier
  classical
  by_cases same : first = last
  · subst last; exact Iff.rfl
  have empty := GeneralNominalCenteredRegistryJournal.distinct_shared_packet_free same reached reachedLast
  have left := (final_lifted empty (lifting first checked state root reached empty)).2 demand frontier
  have right := (final_lifted empty (lifting last checkedLast state root reachedLast empty)).2 demand frontier
  have equal := GeneralCanonicalRegistry.canonical_eq order
  rw [equal] at left
  apply (local_correspondence first _ demand frontier).trans
  apply (GeneralNominalCenteredAdministrativeOrder.local_iff
    (GeneralCanonicalRegistry.reorders_canonical first) checked.1 _ demand frontier).trans
  change Local (canonical first) (finalState first state root) demand frontier ↔ _
  rw [equal]
  exact left.trans (right.symm.trans
    ((GeneralNominalCenteredAdministrativeOrder.local_iff
      (GeneralCanonicalRegistry.reorders_canonical last) checkedLast.1 _ demand frontier).symm.trans
      (local_correspondence last _ demand frontier).symm))

theorem final_models (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state) :
    ∀ model, Models ((executor roles).run registry state root).1 model → Models state model :=
  B4SkeletonV5.steps_models (boundary roles) registry root
    (GeneralNominalCenteredAdministrativeComposition.stepModels registry checked root)
    reachable (execution registry checked state root reachable)

theorem final_stable (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles)
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state) :
    Stable registry ((executor roles).run registry state root).1 root ∧
      ∀ child, GeneralNominalSaturationState.Generated ((executor roles).run registry state root).1.erased.current root child →
        Stable registry ((executor roles).run registry state root).1 child :=
  GeneralNominalCenteredAdministrativeComposition.closure registry checked _ root
    (B4TargetV5.reachable_steps (boundary roles) reachable (execution registry checked state root reachable))
    (halted registry checked state root reachable)

structure Remaining (roles : Roles.RoleDecls) : Prop where
  canonicalExitLifting : CanonicalExitLifting roles
  evidenceNode : B4SkeletonV5.EvidenceNode (boundary roles)
  generatedChildren : B4SkeletonV5.GeneratedChildren (boundary roles)

theorem bridges (remaining : Remaining roles) :
    B4SkeletonV5.B4Bridges (boundary roles) (executor roles) (frontiers roles) where
  progress := GeneralNominalCenteredAdministrativeComposition.progress
  execution := execution
  halted := halted
  closure := GeneralNominalCenteredAdministrativeComposition.closure
  stepModels := GeneralNominalCenteredAdministrativeComposition.stepModels
  frontierLocal := frontierLocal
  localIdentity := localIdentity
  whereAccessible := GeneralNominalCenteredAdministrativeWhere.whereAccessible
  treeExecution := treeExecution
  canonicalLocalOrder := canonicalLocalOrder remaining.canonicalExitLifting
  dictionaryRefl := GeneralNominalCenteredAdministrativeComposition.dictionaryRefl
  evidenceNode := remaining.evidenceNode
  generatedChildren := remaining.generatedChildren
  initialReorders := GeneralNominalCenteredAdministrativeComposition.initialReorders

theorem composition (remaining : Remaining roles) : B4TargetV5.Statement (boundary roles) (executor roles) :=
  B4SkeletonV5.b4_of_bridges _ _ _ (bridges remaining)

end Yulang.GeneralNominalCenteredCanonicalExecutor
