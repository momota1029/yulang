import Yulang.GeneralDictionaryVariableIntervalLeaf
import Yulang.GeneralDictionaryNonterminalNonpointEvidence

/-! Declarative current leaf plans construct finite child Evidence rather than
assuming it. Location and endpoint order remain explicit obligations; there is
no candidate-selection, Stable, or execution conclusion. -/
namespace Yulang.GeneralDictionaryVariableLeafPlans
open GeneralDeclarations GeneralNominalRecursiveCandidates
open GeneralDictionaryRecursiveEvidence
open CommonRoleOutermostResolver (All₂)

/-- A checked bare-variable terminal declaration with computed-query and
location witnesses in one specified current context and assignment. -/
structure LeafPlan (registry : Registry) (context : Context)
    (model : GeneralNominalCommonBridge.Assignment)
    (root : GeneralSourceDictionaries.Occurrence roles) (key : Nat) where
  declaration : Declaration
  visible : declaration ∈ registry.declarations
  checked : DeclarationChecked registry.constructors roles declaration
  identity : declaration.id = key
  role : declaration.role = root.demand.role
  name : Nat
  pair : GeneralNominalInspection.Bounds context.state
  query : GeneralNominalInspection.queries context.state context.interpretation declaration = [.variables [name]]
  inputs : declaration.inputNames = [name]
  terminal : declaration.requirements = []
  outputs : root.demand.outputs = []
  located : arguments context root = some [pair]
  ordered : CommonNominalFullCarrier.Subtype
    (model (context.state.base.source pair.1)).1 (model (context.state.base.source pair.2)).1

theorem instance_of_plan (registry : Registry) (context : Context)
    (model : GeneralNominalCommonBridge.Assignment)
    (metadata : Metadata registry context) (valid : GeneralNominalState.Models context.state model)
    (root : GeneralSourceDictionaries.Occurrence roles) (key : Nat)
    (plan : LeafPlan registry context model root key) :
    Instance registry context model root key [] := by
  rw [← plan.identity]
  exact GeneralDictionaryVariableIntervalLeaf.instance_of_interval context registry root plan.declaration
    plan.visible plan.checked plan.name plan.pair plan.query plan.inputs plan.terminal plan.outputs
    plan.role plan.located metadata model valid plan.ordered

theorem evidence_of_plan (registry : Registry) (context : Context)
    (model : GeneralNominalCommonBridge.Assignment)
    (metadata : Metadata registry context) (valid : GeneralNominalState.Models context.state model)
    (root : GeneralSourceDictionaries.Occurrence roles) (key : Nat)
    (plan : LeafPlan registry context model root key) :
    Evidence registry context model root (.node key []) :=
  (evidence_leaf_iff registry context model root key).mpr
    (instance_of_plan registry context model metadata valid root key plan)

/-- All actual children have plans, preserving their order and multiplicity.
Each plan supplies syntax, location and endpoint order, not Evidence. -/
theorem children_evidence (registry : Registry) (context : Context)
    (model : GeneralNominalCommonBridge.Assignment)
    (metadata : Metadata registry context) (valid : GeneralNominalState.Models context.state model)
    (children : List (GeneralSourceDictionaries.Occurrence roles)) (keys : List Nat)
    (plans : All₂ (fun child key => Nonempty (LeafPlan registry context model child key)) children keys) :
    All₂ (Evidence registry context model) children (keys.map fun key => .node key []) := by
  induction plans with
  | nil => exact .nil
  | cons first rest ih =>
    obtain ⟨plan⟩ := first
    exact .cons (evidence_of_plan registry context model metadata valid _ _ plan) ih

/-- A completed parent Instance fixes the canonical children. Leaf plans
supply their recursive evidence without any child Evidence premise. -/
theorem parent_evidence (registry : Registry) (context : Context)
    (model : GeneralNominalCommonBridge.Assignment)
    (metadata : Metadata registry context) (valid : GeneralNominalState.Models context.state model)
    (root : GeneralSourceDictionaries.Occurrence roles) (key : Nat)
    (children : List (GeneralSourceDictionaries.Occurrence roles)) (keys : List Nat)
    (parent : Instance registry context model root key children)
    (plans : All₂ (fun child leafKey => Nonempty (LeafPlan registry context model child leafKey)) children keys) :
    Evidence registry context model root (.node key (keys.map fun leafKey => .node leafKey [])) :=
  evidence_node registry context model root key children _ parent
    (children_evidence registry context model metadata valid children keys plans)
open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseBranch
open GeneralNominalReobservationSteps GeneralDictionaryNonterminalNonpointEvidence

/-- Transport a nonterminal parent Instance and independently discharge every
current leaf child through concrete plans. No child Evidence premise is used. -/
theorem transport_parent_evidence {state : GeneralNominalSaturationState.State roles}
    {revision : Revision state} (s : Shape revision) (registry : Registry)
    (registryChecked : Checked registry) (root : GeneralSourceDictionaries.Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (queries : GeneralNominalInspection.queries state.context.state state.context.interpretation declaration = [query s])
    (names : declaration.inputNames = [s.binder])
    (variables : GeneralDictionaryVariableRequirements.VariableClauses declaration)
    (located : arguments state.context root = some [(s.root,s.root)])
    (model : GeneralNominalCommonBridge.Assignment)
    (oldChildren : List (GeneralSourceDictionaries.Occurrence roles))
    (old : Instance registry state.context model root declaration.id oldChildren)
    (current : GeneralNominalState.Models revision.snapshot model)
    (metadata : Metadata registry (currentContext revision)) (keys : List Nat)
    (plans : All₂ (fun child key => Nonempty (LeafPlan registry (currentContext revision) model child key))
      (currentChildren s registry root declaration checked) keys) :
    Evidence registry (currentContext revision) model root
      (.node declaration.id (keys.map fun key => .node key [])) :=
  parent_evidence registry (currentContext revision) model metadata current root declaration.id _ keys
    (transport_instance s registry registryChecked root declaration visible checked queries names variables located
      model oldChildren old current) plans
end Yulang.GeneralDictionaryVariableLeafPlans
