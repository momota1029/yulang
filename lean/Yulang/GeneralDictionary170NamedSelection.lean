import Yulang.GeneralDictionary169NamedTree
import Yulang.GeneralDictionary169Selected

/-! Exact-current selection coherence for named-output structural certificates.
A concrete current model is retained: universal evidence alone can be vacuous.
No coverage-existence, alias transport, or global V5 result is asserted. -/
namespace Yulang.GeneralDictionary170NamedSelection
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionaryRecursiveEvidence GeneralNominalRecursiveCandidates
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
open GeneralDictionary169NamedTree (NamedTree)
variable {roles : Roles.RoleDecls}

/-- Actual leaf observations and one source model determine the selected key
and literal ordered child list, without assuming a dictionary. -/
theorem leaf_selected {registry : Registry} {state : State roles} {focus : Occurrence roles}
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : GeneralDictionary169NamedLeaf.LeafShape registry state.context focus declaration checked)
    (metadata : Metadata registry state.context)
    (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models state.context.state model)
    (selected : GeneralNominalFeedbackK2.Local registry state focus (.selected key children)) :
    declaration.id = key ∧ [] = children :=
  GeneralDictionarySelectedInstanceCoherence.instance_selected registry state focus model
    declaration.id key [] children
    (GeneralDictionary169NamedLeaf.instance_of_shape state.context registry focus declaration
      visible checked shape metadata model valid) selected

/-- Interpreting a structural tree in an actual current model exposes exactly
its selected ordered children, not merely the same child count. -/
theorem tree_selected {registry : Registry} {state : Tracked roles} {root focus : Occurrence roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (tree : NamedTree registry state focus (.node key payloads))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (selected : GeneralNominalFeedbackK2.Local registry state.current focus (.selected chosen children)) :
    key = chosen ∧ All₂ (Evidence registry state.current.context model) children payloads := by
  obtain ⟨actual,instanceRule,descendants⟩ := evidence_node_elim _ _ _ _ _ _
    (GeneralDictionary169NamedTree.current_evidence formed tree model valid)
  obtain ⟨sameKey,sameChildren⟩ := GeneralDictionarySelectedInstanceCoherence.instance_selected
    registry state.current focus model key chosen actual children instanceRule selected
  exact ⟨sameKey,sameChildren ▸ descendants⟩

/-- Any semantic dictionary at a terminal selected occurrence has the exact
terminal payload. This is a representation uniqueness fact, not existence. -/
theorem terminal_payload {registry : Registry} {state : State roles} {focus : Occurrence roles}
    (model : GeneralNominalCommonBridge.Assignment)
    (evidence : Evidence registry state.context model focus payload)
    (selected : GeneralNominalFeedbackK2.Local registry state focus (.selected key [])) :
    payload = .node key [] := by
  cases payload with
  | node own payloads =>
    obtain ⟨children,instanceRule,descendants⟩ := evidence_node_elim _ _ _ _ _ _ evidence
    obtain ⟨sameKey,sameChildren⟩ := GeneralDictionarySelectedInstanceCoherence.instance_selected
      registry state focus model own key children [] instanceRule selected
    subst own
    subst children
    cases descendants
    rfl

/-- The observed named leaf forces every structural dictionary at that exact
selected occurrence to have its terminal payload. One actual model is explicit. -/
theorem leaf_tree_unique {registry : Registry} {state : Tracked roles} {root focus : Occurrence roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (shape : GeneralDictionary169NamedLeaf.LeafShape registry state.current.context focus declaration checked)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (selected : GeneralNominalFeedbackK2.Local registry state.current focus (.selected key children))
    (tree : NamedTree registry state focus payload) : payload = .node declaration.id [] := by
  obtain ⟨sameKey,sameChildren⟩ := leaf_selected declaration visible checked shape
    (GeneralDictionarySharedMetadata.formed_metadata formed) model valid.1 selected
  subst key
  subst children
  exact terminal_payload model (GeneralDictionary169NamedTree.current_evidence formed tree model valid) selected

open GeneralDictionaryFiniteObservedExample in
/-- The inhabited ternary-output fixture has exactly one structural dictionary
payload. Its current source model and Shared formation are exhibited, not
inferred from a universal semantic implication. -/
theorem actual_unique :
    Models start.current model ∧ NamedTree registry start root (.node declaration.id []) ∧
    (∀ payload, NamedTree registry start root payload → payload = .node declaration.id []) := by
  have valid : Models start.current model := (initial_models ..).mpr state_models
  refine ⟨valid,GeneralDictionary169NamedTree.actual_tree,?_⟩
  intro payload tree
  exact leaf_tree_unique GeneralDictionary169SharedStable.actual_formed declaration (by simp)
    checked GeneralDictionary169NamedLeaf.actual_shape model valid
    GeneralDictionaryFiniteObservedExampleClassify.selected tree

end Yulang.GeneralDictionary170NamedSelection
