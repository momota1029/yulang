import Yulang.GeneralDictionaryEvidenceTransport204
import Yulang.GeneralDictionaryDefaultEvidence204

namespace Yulang.GeneralDictionaryDefaultBoundary204
open GeneralNominalCenteredHeadAllocV7Executor (executor frontiers)

/-- I36 successor: only Evidence changes; the compiled registry and actual
centered source state are passed to the provenance-aware judgment. -/
def evidence (roles : Roles.RoleDecls) : GeneralDictionaryEvidenceTransport204.EvidenceFamily roles :=
  fun value state => GeneralDictionaryDefaultEvidence204.Evidence
    (GeneralNominalCenteredHeadAllocEncoding.registry value) state.core

def boundary (roles : Roles.RoleDecls) :=
  GeneralDictionaryEvidenceTransport204.boundary roles (evidence roles)

theorem local_iff : B4TargetV7.Local (boundary roles) r s d f ↔
    GeneralNominalCenteredHeadAllocV7Boundary.Local r s d f :=
  GeneralDictionaryEvidenceTransport204.local_iff (evidence roles)

theorem reachable_iff : B4TargetV7.Reachable (boundary roles) r d s ↔
    B4TargetV7.Reachable (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles) r d s := Iff.rfl

theorem generated_iff : B4SkeletonV7.GeneratedChildren (boundary roles) ↔
    GeneralNominalCenteredHeadAllocV7Composition.GeneratedChildren roles :=
  GeneralDictionaryEvidenceTransport204.generated_iff (evidence roles)

/-- The twelve structural laws are unchanged. Selected-node source evidence and
fresh child production remain explicit open fields, not implicit axioms. -/
theorem bridges (node : B4SkeletonV7.EvidenceNode (boundary roles))
    (generated : B4SkeletonV7.GeneratedChildren (boundary roles)) :
    B4SkeletonV7.B4Bridges (boundary roles) (executor roles) (frontiers roles) :=
  GeneralDictionaryEvidenceTransport204.bridges (evidence roles) node generated

theorem composition (node : B4SkeletonV7.EvidenceNode (boundary roles))
    (generated : B4SkeletonV7.GeneratedChildren (boundary roles)) :
    B4TargetV7.Statement (boundary roles) (executor roles) :=
  GeneralDictionaryEvidenceTransport204.composition (evidence roles) node generated

end Yulang.GeneralDictionaryDefaultBoundary204
