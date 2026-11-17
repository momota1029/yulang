import Yulang.GeneralNominalVersionedMixedEmbedding234
set_option backward.isDefEq.respectTransparency false
/-! Pointwise evidence transport. No old reachability hypothesis is needed for
an already established EvidenceAt at this exact state. This is not transport of
EvidenceNode: newly reachable mixed-cache states need not be old-reachable. -/
namespace Yulang.GeneralNominalVersionedMixedEvidenceTransport234
variable {roles : Roles.RoleDecls}

theorem models_iff :
    (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Models state model ↔
    (GeneralNominalVersionedSourceBoundary232.boundary roles).Models state model := Iff.rfl

theorem evidence_iff :
    (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Evidence registry state model demand dictionary ↔
    (GeneralNominalVersionedSourceBoundary232.boundary roles).Evidence registry state model demand dictionary := Iff.rfl

theorem stable_old
    (stable : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Stable registry state demand) :
    (GeneralNominalVersionedSourceBoundary232.boundary roles).Stable registry state demand :=
  GeneralNominalVersionedMixedKernel234.stable_old stable

theorem evidenceAt
    (given : B4SkeletonV8.EvidenceAt (GeneralNominalVersionedSourceBoundary232.boundary roles) registry state root) :
    B4SkeletonV8.EvidenceAt (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry state root := by
  intro model valid demand key children dictionaries generated stable childStable selected evidence
  exact given model valid demand key children dictionaries generated (stable_old stable)
    (fun child member => stable_old (childStable child member))
    (GeneralNominalVersionedMixedEmbedding234.local_iff.mp selected) evidence

end Yulang.GeneralNominalVersionedMixedEvidenceTransport234
