import Yulang.GeneralNominalCenteredHeadAllocV7Cycle199Fixture

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCenteredHeadAllocV7Cycle199Regression
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalCenteredHeadAllocV7Cycle199Source
open GeneralNominalCenteredHeadAllocV7Cycle199Local
open GeneralNominalCenteredHeadAllocV7Cycle199Fixture
open GeneralNominalCenteredHeadAllocV7Boundary (boundary Local)

theorem encoded_registry_eq : GeneralNominalCenteredHeadAllocEncoding.registry registry = registry := rfl

theorem reachable : B4TargetV7.Reachable (boundary roles) registry root start :=
  ⟨start,initial_source,.refl⟩

theorem conflict : (boundary roles).OutputConflict registry start root 37 := output_conflict

theorem no_merged_conflict : ¬ (boundary roles).MergedOutputConflict registry start root := by
  rintro ⟨⟨a,b,member,_,_⟩,_⟩
  cases member

theorem rejected_v7 : Local registry start root .rejected :=
  .ordinary no_merged_conflict (GeneralNominalCenteredHeadAllocBoundary.local_iff.mpr rejected)

theorem no_selected (key children) : ¬ Local registry start root (.selected key children) := by
  intro chosen
  have equal := B4TargetV7.local_functional chosen rejected_v7
  cases equal

/-- This is the entire selected-only evidence obligation at the cycle-199
snapshot. Its selection premise is false even though the journal is inhabited. -/
theorem evidenceAt : B4SkeletonV7.EvidenceAt (boundary roles) registry start root := by
  apply B4SkeletonV7.evidenceAt_of_no_selection
  intro demand key children reached
  have same : demand = root := by
    rcases reached with same | generated
    · exact same
    · exact generated_only_root demand generated
  subst demand
  exact no_selected key children

/-- The port preserves the source, stability and positive model of the original
counterexample, while the corrected evidence obligation holds at that state. -/
theorem terminal_regression :
    (boundary roles).Checked registry ∧ (boundary roles).Initial registry root start ∧
    (boundary roles).Models start model ∧ (boundary roles).Stable registry start root ∧
    Local registry start root .rejected ∧ B4SkeletonV7.EvidenceAt (boundary roles) registry start root :=
  ⟨⟨rfl,checked⟩,initial_source,inhabited,stable,rejected_v7,evidenceAt⟩

end Yulang.GeneralNominalCenteredHeadAllocV7Cycle199Regression
