import Yulang.GeneralNominalInstalledForest191
import Yulang.GeneralNominalRepeatedLocal190

/-! A genuinely enabled, novel repeated-head installation instantiates the
forest certificate. This baseline is a leaf, not a nonempty-child regression. -/
namespace Yulang.GeneralNominalForestRegression191
open GeneralNominalRepeatedFixture190
open GeneralNominalRepeatedLocal190
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadWFBoundary (boundary)
open GeneralNominalInstalledForest191

/-- Every real enabled support for the existing repeated-head fixture produces
an explicit one-node forest. The novelty proof is the existing bad-model witness. -/
theorem build {support : List (GeneralSourceDictionaries.Occurrence roles)}
    (enabled : Installable registry start plan support) :
    Build registry root start [root] [.node 3 []] (install start plan support enabled) := by
  apply Build.cons plan support enabled .root not_committed
  · rw [GeneralNominalHeadLeafPlan189.children_empty plan rfl]
    exact .nil _
  · exact .nil _

theorem exists_build : ∃ after,
    Build registry root start [root] [.node 3 []] after := by
  obtain ⟨support,enabled⟩ := installable
  exact ⟨install start plan support enabled,build enabled⟩

/-- Checked source reachability and an inhabited actual execution coexist;
all final models, rather than a selected witness, have the same dictionary. -/
theorem source_tree_sound :
    (boundary roles).Checked registry ∧
    (boundary roles).Initial registry root start ∧
    ∃ after, B4Target.Steps ((boundary roles).Step registry root) start after ∧
      (∃ model, Models after model) ∧
      ∀ model, Models after model →
        (boundary roles).Evidence registry after model root (.node 3 []) := by
  obtain ⟨after,certificate⟩ := exists_build
  exact ⟨⟨rfl,checked⟩,initial_source,after,tree_sound root (.node 3 []) certificate⟩

end Yulang.GeneralNominalForestRegression191
