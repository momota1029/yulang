import Yulang.GeneralDictionaryVersionedDefault202Local233
import Yulang.GeneralNominalVersionedMixedStableTransfer234
import Yulang.GeneralNominalVersionedMixedEvidenceTransport234
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryMixedDefault202234
open GeneralDictionaryAllocDefaultSource202
open GeneralDictionaryVersionedDefault202233
open GeneralNominalVersionedJournal232

theorem initial : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root current :=
  GeneralDictionaryVersionedDefault202233.initial

theorem reachable : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry root current :=
  ⟨current,initial,.refl⟩

theorem headless : GeneralNominalVersionedMixedTerminalStable234.HeadlessUnknown current :=
  GeneralNominalVersionedMixedStableTransfer234.headless_of_known current_model
    (fun identity member => GeneralNominalCenteredTerminalForkSource.all_known _ identity member)

theorem stable : GeneralNominalVersionedMixedKernel234.Stable registry current root :=
  GeneralNominalVersionedMixedStableTransfer234.stable GeneralDictionaryVersionedDefault202Local233.stable
    (GeneralNominalCenteredHeadMatStepObservations.initial_cache context root)
    (GeneralNominalCenteredTerminalForkSource.point_closed false) headless

theorem selected : GeneralNominalVersionedMixedSourceBoundary234.Local registry current root (.selected 37 []) :=
  GeneralNominalVersionedMixedEmbedding234.local_iff.mpr GeneralDictionaryVersionedDefault202Local233.selected

theorem evidenceAt : B4SkeletonV8.EvidenceAt (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry current root :=
  GeneralNominalVersionedMixedEvidenceTransport234.evidenceAt GeneralDictionaryVersionedDefault202Local233.evidenceAt

theorem regression :
    (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked registry ∧
    (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Initial registry root current ∧
    Models current model ∧ GeneralNominalVersionedMixedKernel234.Stable registry current root ∧
    GeneralNominalVersionedMixedSourceBoundary234.Local registry current root (.selected 37 []) ∧
    B4SkeletonV8.EvidenceAt (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) registry current root :=
  ⟨⟨rfl,checked⟩,initial,current_model,stable,selected,evidenceAt⟩

end Yulang.GeneralDictionaryMixedDefault202234
