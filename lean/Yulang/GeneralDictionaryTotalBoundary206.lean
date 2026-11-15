import Yulang.GeneralDictionaryEvidenceTransport204
import Yulang.GeneralDictionaryTotalEvidence206

namespace Yulang.GeneralDictionaryTotalBoundary206
open GeneralNominalCenteredHeadAllocV7Executor (executor frontiers)

def evidence (roles : Roles.RoleDecls) : GeneralDictionaryEvidenceTransport204.EvidenceFamily roles :=
  fun value state => GeneralDictionaryTotalEvidence206.Evidence
    (GeneralNominalCenteredHeadAllocEncoding.registry value) state.core

def boundary (roles : Roles.RoleDecls) :=
  GeneralDictionaryEvidenceTransport204.boundary roles (evidence roles)

theorem local_iff : B4TargetV7.Local (boundary roles) r s d f ↔
    GeneralNominalCenteredHeadAllocV7Boundary.Local r s d f :=
  GeneralDictionaryEvidenceTransport204.local_iff (evidence roles)

theorem reachable_iff : B4TargetV7.Reachable (boundary roles) r d s ↔
    B4TargetV7.Reachable (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles) r d s := Iff.rfl

theorem bridges (node : B4SkeletonV7.EvidenceNode (boundary roles))
    (generated : B4SkeletonV7.GeneratedChildren (boundary roles)) :
    B4SkeletonV7.B4Bridges (boundary roles) (executor roles) (frontiers roles) :=
  GeneralDictionaryEvidenceTransport204.bridges (evidence roles) node generated

theorem composition (node : B4SkeletonV7.EvidenceNode (boundary roles))
    (generated : B4SkeletonV7.GeneratedChildren (boundary roles)) :
    B4TargetV7.Statement (boundary roles) (executor roles) :=
  GeneralDictionaryEvidenceTransport204.composition (evidence roles) node generated
end Yulang.GeneralDictionaryTotalBoundary206
