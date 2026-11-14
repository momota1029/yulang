import Yulang.GeneralNominalForestProducer192
import Yulang.GeneralNominalInitialLeafNonvacuity189
import Yulang.GeneralNominalForestRegression191

/-! Both previously committed and genuinely novel source cases are covered.
Neither fixture has a nonempty child list. -/
namespace Yulang.GeneralNominalReusableRegression192
open GeneralNominalInitialLeafFixture189 GeneralNominalInitialLeafLocal189
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalReusableForest192

theorem stable_build : Build registry root start [root] [.node 3 []] start := by
  obtain ⟨support,enabled⟩ := GeneralNominalHeadLeafPlan189.initial_selected_installable
    checked initial_source selected plan frame rfl rfl
  apply Build.reuse plan support enabled .root
    (GeneralNominalInitialLeafNonvacuity189.candidate_committed plan frame)
  · rw [GeneralNominalHeadLeafPlan189.children_empty plan rfl]; exact .nil _
  · exact .nil _

theorem stable_old_impossible (after : State roles) :
    ¬ GeneralNominalInstalledForest191.Build registry root start [root] [.node 3 []] after :=
  GeneralNominalForestProducer192.stable_no_installed GeneralNominalInitialLeafNonvacuity189.stable

/-- Nonempty final models exclude vacuous dictionary soundness. This source
already has every required equation, so reusing it takes zero kernel steps. -/
theorem stable_source_sound :
    (boundary roles).Checked registry ∧ (boundary roles).Initial registry root start ∧
    (boundary roles).Stable registry start root ∧ Models start model ∧
    ∀ assignment, Models start assignment →
      (boundary roles).Evidence registry start assignment root (.node 3 []) := by
  exact ⟨⟨rfl,checked⟩,initial_source,GeneralNominalInitialLeafNonvacuity189.stable,
    inhabited,(tree_sound root (.node 3 []) stable_build).2.2⟩

/-- The novel repeated-variable source retains its real installation path
when embedded into the new certificate relation. -/
theorem repeated_exists_build : ∃ after,
    Build GeneralNominalRepeatedFixture190.registry GeneralNominalRepeatedFixture190.root
      GeneralNominalRepeatedFixture190.start [GeneralNominalRepeatedFixture190.root] [.node 3 []] after := by
  obtain ⟨after,certificate⟩ := GeneralNominalForestRegression191.exists_build
  exact ⟨after,GeneralNominalForestProducer192.of_installed certificate⟩

end Yulang.GeneralNominalReusableRegression192
