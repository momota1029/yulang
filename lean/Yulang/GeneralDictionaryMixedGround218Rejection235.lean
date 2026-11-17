import Yulang.GeneralDictionaryMixedGround218Safety235
/-! Actual source-initial mixed-kernel parent installation produces a generated
leaf with a coherent head-only candidate but impossible actual-center sharing.
The rejection below is at that reachable installed state; no Stable or global
termination assertion is made. -/
namespace Yulang.GeneralDictionaryMixedGround218Rejection235
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryMixedGround218Leaf235
open GeneralDictionaryMixedGround218Install234 (installed)

theorem conflict : GeneralNominalVersionedDiagnostic232.SharingConflict registry installed oldChild :=
  ⟨1,[],GeneralDictionaryMixedGround218Fresh235.unique,
    GeneralDictionaryMixedGround218Safety235.safe,GeneralDictionaryMixedGround218LeafFrame235.at_key⟩

theorem rejected : GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry installed oldChild .rejected := by
  apply B4TargetV8.Local.sharingRejected conflict
  exact B4TargetV8.unique_not_priorityAmbiguity
    (show B4TargetV8.Unique (GeneralNominalVersionedMixedSourceBoundary234.boundary roles)
      sourceRegistry installed oldChild 1 [] from GeneralDictionaryMixedGround218Fresh235.unique)

theorem generated : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Generated
    sourceRegistry installed root oldChild := by
  rw [← GeneralDictionaryMixedGround218LeafFrame235.child_eq]
  exact GeneralDictionaryMixedGround218Install234.generated_child

theorem source_regression :
    B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry root installed ∧
    (∃ model, (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Models installed model) ∧
    (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Generated sourceRegistry installed root oldChild ∧
    GeneralNominalVersionedMixedSourceBoundary234.Local sourceRegistry installed oldChild .rejected :=
  ⟨GeneralDictionaryMixedGround218Install234.reachable,
    ⟨_,GeneralDictionaryMixedGround218Install234.installed_model⟩,generated,rejected⟩
end Yulang.GeneralDictionaryMixedGround218Rejection235
