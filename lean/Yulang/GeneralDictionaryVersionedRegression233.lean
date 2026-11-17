import Yulang.GeneralDictionaryVersionedSecondStable233
import Yulang.GeneralDictionaryVersionedPointEvidenceAt233
set_option backward.isDefEq.respectTransparency false
/-! Nonvacuous I44 regression on the actual source initialization: three genuine
new-kernel steps, a full stable selected endpoint, historical and new aggregate
equations together, and current evidence in every endpoint model. The kernel
still uses inherited legacy trusted caches; global solver completeness and
termination are separate obligations. -/
namespace Yulang.GeneralDictionaryVersionedRegression233
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryVersionedSecondInstall233
open GeneralNominalVersionedJournal232
open GeneralDictionaryVersionedBothModel233 (extended)

abbrev boundary := GeneralNominalVersionedSourceBoundary232.boundary roles

theorem checked : boundary.Checked sourceRegistry := GeneralDictionaryOptionalInitial229.boundary_checked

theorem source_unchanged : installed.core.erased.source =
    GeneralDictionaryVersionedInitialFrame233.before.core.erased.source := rfl

theorem two_version_values :
    (extended (GeneralDictionaryVersionedNames231.oldVersionName 0)).1 = GeneralDictionaryOptionalOutput229.value ∧
    (extended (GeneralDictionaryVersionedNames231.freshName 0)).1 = CommonNominalFullCarrier.emptyRecord :=
  ⟨GeneralDictionaryVersionedBothModel233.fresh_value 0,GeneralDictionaryVersionedBothModel233.next_value 0⟩

theorem versions_distinct : GeneralDictionaryVersionedNames231.oldVersionName 0 ≠
    GeneralDictionaryVersionedNames231.freshName 0 := GeneralDictionaryVersionedNames231.version_changed 0

theorem all_models_evidence {model : GeneralNominalCommonBridge.Assignment} (valid : Models installed model) :
    boundary.Evidence sourceRegistry installed model root (.node declaration.id []) := evidence valid

theorem evidenceAt : B4SkeletonV8.EvidenceAt boundary sourceRegistry installed root :=
  GeneralDictionaryVersionedSecondSelected233.evidenceAt

/-- Every generated descendant in this terminal example is the stable root. -/
theorem generated_stable (generated : boundary.Generated sourceRegistry installed root demand) :
    boundary.Stable sourceRegistry installed demand := by
  have same := GeneralDictionaryVersionedSecondStable233.generated_only generated
  subst demand
  exact GeneralDictionaryVersionedSecondStable233.source_stable

/-- The selected EvidenceAt is not vacuous: its reachable/stable/selected and
model premises are all simultaneously inhabited in the successor boundary. -/
theorem positive_regression :
    boundary.Checked sourceRegistry ∧
    B4TargetV8.Reachable boundary sourceRegistry root installed ∧
    boundary.Stable sourceRegistry installed root ∧
    B4TargetV8.Local boundary sourceRegistry installed root (.selected declaration.id []) ∧
    B4SkeletonV8.EvidenceAt boundary sourceRegistry installed root ∧
    ∃ model, boundary.Models installed model ∧
      boundary.Evidence sourceRegistry installed model root (.node declaration.id []) :=
  ⟨checked,GeneralDictionaryVersionedSecondStep233.reachable,
    GeneralDictionaryVersionedSecondStable233.source_stable,
    GeneralDictionaryVersionedSecondSelected233.source_selected,evidenceAt,
    extended,installed_model,all_models_evidence installed_model⟩

end Yulang.GeneralDictionaryVersionedRegression233
