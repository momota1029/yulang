import Yulang.GeneralDictionaryVersionedJoin204Local233
import Yulang.GeneralNominalVersionedMixedStableTransfer234
import Yulang.GeneralNominalVersionedMixedEvidenceTransport234
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryMixedJoin204234
open GeneralDictionaryDefaultEvidence204JoinSource
open GeneralDictionaryVersionedJoin204233
open GeneralNominalVersionedJournal232

theorem initial : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root current :=
  GeneralDictionaryVersionedJoin204233.initial

theorem reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root current :=
  ⟨current,initial,.refl⟩

theorem headless : GeneralNominalVersionedMixedTerminalStable234.HeadlessUnknown current :=
  GeneralNominalVersionedMixedStableTransfer234.headless_of_known current_model
    (fun identity member => GeneralNominalCenteredTerminalForkSource.all_known _ identity member)

theorem stable : GeneralNominalVersionedMixedKernel234.Stable registry current root :=
  GeneralNominalVersionedMixedStableTransfer234.stable GeneralDictionaryVersionedJoin204Local233.stable
    (GeneralNominalCenteredHeadMatStepObservations.initial_cache context root)
    (GeneralNominalCenteredTerminalForkSource.point_closed false) headless

theorem selected : GeneralNominalVersionedMixedSourceBoundary234.Local registry current root (.selected 37 []) :=
  GeneralNominalVersionedMixedEmbedding234.local_iff.mpr GeneralDictionaryVersionedJoin204Local233.selected

theorem evidenceAt : B4SkeletonV8.EvidenceAt (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry current root :=
  GeneralNominalVersionedMixedEvidenceTransport234.evidenceAt GeneralDictionaryVersionedJoin204Local233.evidenceAt

theorem regression :
    (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry ∧
    (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root current ∧
    Models current model ∧ GeneralNominalVersionedMixedKernel234.Stable registry current root ∧
    GeneralNominalVersionedMixedSourceBoundary234.Local registry current root (.selected 37 []) ∧
    B4SkeletonV8.EvidenceAt (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry current root :=
  ⟨⟨rfl,checked⟩,initial,current_model,stable,selected,evidenceAt⟩

end Yulang.GeneralDictionaryMixedJoin204234
