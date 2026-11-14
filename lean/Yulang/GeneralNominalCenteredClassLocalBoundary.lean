import Yulang.GeneralNominalCenteredPermutationSimulation
import Yulang.GeneralNominalCenteredCompletionAliasObstruction

set_option backward.isDefEq.respectTransparency false

/-! Class-wide applicability refines Survivor. Existing pending, cycle,
ambiguity and zero-candidate rules, and the transition kernel, are retained. -/
namespace Yulang.GeneralNominalCenteredClassLocalBoundary
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralNominalCenteredBoundary (vocabulary)
open CommonRoleOutermostResolver
variable {roles : Roles.RoleDecls}

def fields (roles : Roles.RoleDecls) : GeneralNominalLocalBoundary.Fields (vocabulary roles) :=
  { GeneralNominalCenteredAdministrativeLocal.fields roles with
    Survivor := fun registry state root key children =>
      GeneralNominalRecursiveCandidates.Survivor registry state.erased.current.context root key children ∧
        GeneralNominalJointCandidates.Joint registry state.erased.current root key }

abbrev Local (registry : Registry) (state : State roles) := GeneralNominalLocalBoundary.Local (fields roles) registry state

def boundary (roles : Roles.RoleDecls) : B4TargetV5.SourceBoundary (vocabulary roles) where
  toSourceBoundary := GeneralNominalLocalBoundary.complete (fields roles) (GeneralNominalCenteredBoundary.remaining roles)
  Initial := (GeneralNominalCenteredAdministrativeLocal.boundary roles).Initial

theorem reachable_iff : B4TargetV5.Reachable (boundary roles) registry root state ↔
    B4TargetV5.Reachable (GeneralNominalCenteredAdministrativeLocal.boundary roles) registry root state := Iff.rfl

theorem local_correspondence (registry : Registry) (state : State roles) (root : Occurrence roles) (frontier) :
    B4TargetV3.Local (boundary roles).toSourceBoundary registry state root frontier ↔ Local registry state root frontier :=
  (GeneralNominalLocalBoundary.local_extension (GeneralNominalCenteredBoundary.remaining roles) frontier).symm

theorem local_functional (one : Local registry state root first) (two : Local registry state root last) : first = last :=
  GeneralNominalLocalBoundary.local_functional one two

theorem local_total (registry : Registry) (checked : Checked registry) (state : State roles) (root : Occurrence roles) :
    ∃ frontier, Local registry state root frontier :=
  GeneralNominalLocalBoundary.local_total (fun key first last one two =>
    GeneralNominalRecursiveCandidates.survivor_children_functional registry checked
      state.erased.current.context root key first last one.1 two.1)

theorem selected_survivor (selected : Local registry state root (.selected key children)) :
    GeneralNominalRecursiveCandidates.Survivor registry state.erased.current.context root key children := by
  cases selected with | selected _ unique => exact unique.1.1

theorem selected_joint (selected : Local registry state root (.selected key children)) :
    GeneralNominalJointCandidates.Joint registry state.erased.current root key := by
  cases selected with | selected _ unique => exact unique.1.2

theorem selected_ready (selected : Local registry state root (.selected key children)) :
    GeneralNominalCenteredAdministrativeLocal.AdministrativeReady state root := by
  apply Classical.byContradiction
  intro missing
  cases selected with | selected safe _ => exact safe.2.2.2 (Or.inr missing)

/-- Filtering preserves a chosen raw branch, but does not itself establish
uniqueness among raw candidates. This is the exact old-selection requirement. -/
def RawUnique (registry : Registry) (state : State roles) (root : Occurrence roles) (key : Nat) : Prop :=
  ∀ other children, GeneralNominalRecursiveCandidates.Survivor registry state.erased.current.context root other children → other = key

theorem selected_old_iff (checked : Checked registry)
    (selected : Local registry state root (.selected key children)) :
    GeneralNominalCenteredAdministrativeLocal.Local registry state root (.selected key children) ↔ RawUnique registry state root key := by
  constructor
  · intro old other cs survivor
    cases old with | selected _ unique => exact (unique.2 other cs survivor).1
  · intro unique
    cases selected with
    | selected safe witness =>
      refine .selected safe ⟨witness.1.1,?_⟩
      intro other cs survivor
      have keyEq := unique other cs survivor
      subst other
      exact ⟨rfl,GeneralNominalRecursiveCandidates.survivor_children_functional registry checked
        state.erased.current.context root key cs children survivor witness.1.1⟩

noncomputable def frontiers (roles : Roles.RoleDecls) : B4SkeletonV5.Frontiers (vocabulary roles) := by
  classical
  exact fun registry state =>
    { frontier := fun root => if checked : Checked registry then Classical.choose (local_total registry checked state root) else .pending
      Local := B4TargetV3.Local (boundary roles).toSourceBoundary registry state }

theorem frontierLocal (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : State roles) (root : Occurrence roles) (_reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (demand : Occurrence roles) (frontier) :
    (frontiers roles registry state).frontier demand = frontier ↔
      B4TargetV3.Local (boundary roles).toSourceBoundary registry state demand frontier := by
  classical
  have valid := Classical.choose_spec (local_total registry checked.2 state demand)
  change (if checked : Checked registry then Classical.choose (local_total registry checked state demand) else .pending) = frontier ↔ _
  rw [dite_eq_left checked.2]
  exact ⟨fun same => (local_correspondence registry state demand frontier).mpr (same ▸ valid),
    fun given => local_functional valid ((local_correspondence registry state demand frontier).mp given)⟩

theorem localIdentity (registry : Registry) (state : State roles) (root : Occurrence roles)
    (_reachable : B4TargetV5.Reachable (boundary roles) registry root state) :
    (frontiers roles registry state).Local = B4TargetV3.Local (boundary roles).toSourceBoundary registry state := rfl

open GeneralNominalCenteredCompletionAliasSource GeneralNominalCenteredCompletionAliasTrace
open GeneralNominalCenteredCompletionAliasLocal

theorem alias_fixture_rejected : Local registry finish focus .rejected := by
  have selected := child_selected
  cases selected with
  | selected safe unique =>
    refine .rejected ⟨safe.1,Or.inr (Or.inr ⟨safe.2.2.2,?_⟩)⟩
    intro key children candidate
    have identity := (unique.2 key children candidate.1).1
    exact GeneralNominalCenteredCompletionAliasObstruction.no_joint (identity ▸ candidate.2)

end Yulang.GeneralNominalCenteredClassLocalBoundary
