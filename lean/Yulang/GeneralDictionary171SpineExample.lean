import Yulang.GeneralDictionary171SpineAccessible
import Yulang.GeneralDictionary170NamedSpineStable

/-! The same actual initial nominal/named-output source which lacked the old
local certificate now has structural coverage and a uniform dictionary. -/
namespace Yulang.GeneralDictionary171SpineExample
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralDictionary171SpineCoverage GeneralDictionary171SpineAccessible
open GeneralDictionary170NamedSpineExample
open GeneralDeclarationExamples (roles)

def domain (occurrence : Occurrence roles) : Prop := occurrence = root

def coverage : Coverage registry start domain where
  node := fun occurrence equal => by
    change occurrence = root at equal
    subst occurrence
    exact .namedSpine root declaration (by simp) checked shape
  closed := by
    intro occurrence equal child member
    change occurrence = root at equal
    subst occurrence
    cases member

theorem actual_tree : GeneralDictionary171SpineTree.Tree registry start root (.node declaration.id []) :=
  .namedSpine root declaration (by simp) checked shape

theorem actual_accessible : Acc (Child coverage) ⟨root,rfl⟩ :=
  coverage_accessible coverage ⟨root,rfl⟩

theorem actual_uniform_dictionary :
    ∃ payload, GeneralDictionary171SpineTree.Tree registry start root payload ∧
      ∀ assignment, Models start.current assignment →
        GeneralDictionaryRecursiveEvidence.Evidence registry start.current.context assignment root payload :=
  covered_dictionary coverage ⟨root,rfl⟩ (.initial context initial_source)

theorem actual_no_old_coverage :
    ¬ Nonempty (GeneralDictionary170NamedCoverage.Coverage registry start domain) := by
  intro ⟨old⟩
  exact no_current_local_node ⟨old.node root rfl⟩

/-- This repairs the known local expressivity hole; it does not derive coverage
from an arbitrary reachable stable state or close V5.evidenceNode. -/
theorem stable_strict_coverage :
    GeneralNominalSharedSteps.SourceFormed registry root start ∧
    GeneralNominalSharedSteps.Stable registry start root ∧
    Nonempty (Coverage registry start domain) ∧
    ¬ Nonempty (GeneralDictionary170NamedCoverage.Coverage registry start domain) ∧
    Models start.current GeneralDictionaryFiniteObservedExample.model ∧
    GeneralDictionary171SpineTree.Tree registry start root (.node declaration.id []) ∧
    (∀ assignment, Models start.current assignment →
      GeneralDictionaryRecursiveEvidence.Evidence registry start.current.context assignment root (.node declaration.id [])) :=
  ⟨.initial context initial_source,GeneralDictionary170NamedSpineStable.shared_stable,
    ⟨coverage⟩,actual_no_old_coverage,
    GeneralDictionary170NamedSpineStable.initial_models _ GeneralDictionaryFiniteObservedExample.state_models,
    actual_tree, fun assignment valid => GeneralDictionary171SpineTree.current_evidence
      (.initial context initial_source) actual_tree assignment valid⟩
end Yulang.GeneralDictionary171SpineExample
