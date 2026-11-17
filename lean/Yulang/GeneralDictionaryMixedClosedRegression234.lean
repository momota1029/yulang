import Yulang.GeneralDictionaryMixedClosedSelected234
import Yulang.GeneralDictionaryVersionedRegression233
set_option backward.isDefEq.respectTransparency false
/-! Genuine source-initial mixed-cache saturation of the I44 example. Unlike
cycle233, the three width aggregates are learned by the operational kernel.
This is a nonempty four-step regression, not general termination/EvidenceNode. -/
namespace Yulang.GeneralDictionaryMixedClosedRegression234
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryMixedClosedStep234 (next)
open GeneralNominalVersionedJournal232
open GeneralDictionaryVersionedBothModel233 (extended)

abbrev boundary := GeneralNominalVersionedMixedSourceBoundary234.boundary roles

theorem checked : boundary.Checked sourceRegistry := GeneralDictionaryOptionalInitial229.boundary_checked

theorem source_unchanged : next.core.erased.source =
    GeneralDictionaryVersionedInitialFrame233.before.core.erased.source := rfl

theorem all_models_evidence {model : GeneralNominalCommonBridge.Assignment} (valid : Models next model) :
    boundary.Evidence sourceRegistry next model root (.node declaration.id []) :=
  GeneralDictionaryMixedClosedEvidence234.evidence valid

theorem generated_only (generated : boundary.Generated sourceRegistry next root demand) : demand = root :=
  GeneralNominalVersionedMixedTerminalStable234.generated_only
    GeneralDictionaryMixedClosedFrame234.raw_sites GeneralDictionaryMixedClosedStable234.edges_empty generated

theorem evidenceAt : B4SkeletonV8.EvidenceAt boundary sourceRegistry next root := by
  intro model valid demand key children dictionaries reached _stable _childStable chosen childEvidence
  have same : demand = root := by
    rcases reached with same | reached
    · exact same
    · exact generated_only reached
  subst demand
  have classified := B4TargetV8.local_functional chosen GeneralDictionaryMixedClosedSelected234.source_selected
  cases classified
  cases childEvidence
  exact all_models_evidence valid

theorem generated_stable (generated : boundary.Generated sourceRegistry next root demand) :
    boundary.Stable sourceRegistry next demand := by
  rw [generated_only generated]
  exact GeneralDictionaryMixedClosedStable234.source_stable

theorem positive_regression :
    boundary.Checked sourceRegistry ∧
    B4TargetV8.Reachable boundary sourceRegistry root next ∧
    boundary.Stable sourceRegistry next root ∧
    B4TargetV8.Local boundary sourceRegistry next root (.selected declaration.id []) ∧
    B4SkeletonV8.EvidenceAt boundary sourceRegistry next root ∧
    ∃ model, boundary.Models next model ∧
      boundary.Evidence sourceRegistry next model root (.node declaration.id []) :=
  ⟨checked,GeneralDictionaryMixedClosedStep234.source_reachable,
    GeneralDictionaryMixedClosedStable234.source_stable,
    GeneralDictionaryMixedClosedSelected234.source_selected,evidenceAt,
    extended,GeneralDictionaryMixedClosedStable234.valid,
    all_models_evidence GeneralDictionaryMixedClosedStable234.valid⟩

end Yulang.GeneralDictionaryMixedClosedRegression234
