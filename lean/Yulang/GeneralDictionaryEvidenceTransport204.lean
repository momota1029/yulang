import Yulang.GeneralNominalCenteredHeadAllocV7Composition

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryEvidenceTransport204
open GeneralDeclarations GeneralSourceDictionaries CommonRoleOutermostResolver
open GeneralNominalCenteredHeadMatStepJournal (State)
open GeneralNominalCenteredHeadAllocV7Executor (executor frontiers)

abbrev EvidenceFamily (roles : Roles.RoleDecls) :=
  Registry → State roles → GeneralNominalCommonBridge.Assignment → Occurrence roles → Dictionary → Prop

def boundary (roles : Roles.RoleDecls) (evidence : EvidenceFamily roles) :
    B4TargetV7.SourceBoundary (GeneralNominalCenteredHeadMatStepLocal.vocabulary roles) :=
  { GeneralNominalCenteredHeadAllocV7Boundary.boundary roles with Evidence := evidence }

variable {roles : Roles.RoleDecls} (evidence : EvidenceFamily roles)

theorem ordinary_iff : B4TargetV6.Local (boundary roles evidence).toV6 r s d f ↔
    B4TargetV6.Local (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles).toV6 r s d f := by
  constructor <;> intro h <;> cases h with
  | pending h => exact .pending h
  | inspectionPending a b c d => exact .inspectionPending a b c d
  | rejected h => exact .rejected h
  | ambiguous a b c d => exact .ambiguous a b c d
  | selected a b c => exact .selected a b c

theorem local_iff : B4TargetV7.Local (boundary roles evidence) r s d f ↔
    GeneralNominalCenteredHeadAllocV7Boundary.Local r s d f :=
  B4TargetV7.local_transport (fun _ => ordinary_iff evidence) Iff.rfl Iff.rfl _

theorem local_eq : B4TargetV7.Local (boundary roles evidence) r s =
    GeneralNominalCenteredHeadAllocV7Boundary.Local r s := by
  funext d f
  exact propext (local_iff evidence)

theorem reachable_iff : B4TargetV7.Reachable (boundary roles evidence) r d s ↔
    B4TargetV7.Reachable (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles) r d s := Iff.rfl

theorem generated_iff : B4SkeletonV7.GeneratedChildren (boundary roles evidence) ↔
    GeneralNominalCenteredHeadAllocV7Composition.GeneratedChildren roles := by
  unfold B4SkeletonV7.GeneratedChildren GeneralNominalCenteredHeadAllocV7Composition.GeneratedChildren
  simp only [local_iff]
  rfl

/-- The twelve operational fields transfer without any evidence hypothesis.
Only the exact node and child-production laws remain inputs. -/
theorem bridges (node : B4SkeletonV7.EvidenceNode (boundary roles evidence))
    (generated : B4SkeletonV7.GeneratedChildren (boundary roles evidence)) :
    B4SkeletonV7.B4Bridges (boundary roles evidence) (executor roles) (frontiers roles) where
  progress := GeneralNominalCenteredHeadAllocV7Executor.progress
  execution := GeneralNominalCenteredHeadAllocV7Executor.execution
  halted := GeneralNominalCenteredHeadAllocV7Executor.halted
  closure := GeneralNominalCenteredHeadAllocV7Boundary.closure
  stepModels := GeneralNominalCenteredHeadAllocV7Boundary.stepModels
  frontierLocal := by
    intro r checked s root reachable d f
    exact (GeneralNominalCenteredHeadAllocV7Executor.frontierLocal checked s d f).trans (local_iff evidence).symm
  localIdentity := by
    intro r s root reachable
    exact (GeneralNominalCenteredHeadAllocV7Executor.localIdentity r s).trans (local_eq evidence).symm
  whereAccessible := by
    intro r checked s root reachable
    rw [local_eq]
    exact GeneralNominalCenteredHeadAllocV7Boundary.whereAccessible r s root
  treeExecution := fun r _ s root _ => GeneralNominalCenteredHeadAllocV7Executor.treeExecution r s root
  canonicalLocalOrder := by
    intro r r' checked checked' order s root reachable reachable' d f
    exact (local_iff evidence).trans ((GeneralNominalCenteredHeadAllocV7Executor.canonicalLocalOrder roles
      r r' checked checked' order s root reachable reachable' d f).trans (local_iff evidence).symm)
  dictionaryRefl := GeneralNominalCenteredHeadAllocV7Boundary.dictionaryRefl (roles := roles)
  evidenceNode := node
  generatedChildren := generated
  initialReorders := fun _ _ _ _ order _ _ initial => GeneralNominalCenteredHeadAllocV7Boundary.initialReorders order initial

/-- Conditional only on the two genuinely remaining fields, not on any new
operational or order obligation. This is not an unconditional I36 completion. -/
theorem composition (node : B4SkeletonV7.EvidenceNode (boundary roles evidence))
    (generated : B4SkeletonV7.GeneratedChildren (boundary roles evidence)) :
    B4TargetV7.Statement (boundary roles evidence) (executor roles) :=
  B4SkeletonV7.b4_of_bridges _ _ _ (bridges evidence node generated)

end Yulang.GeneralDictionaryEvidenceTransport204
