import Yulang.GeneralDictionary171LocalInspectionObservation
import Yulang.GeneralDictionary171SpineCoverage

/-! Construct the local named-spine certificate from actual finished request
inspections. Input spine structure is still supplied: this is not general
coverage discovery from Reachable or Stable, and does not cover variable,
record, variant, or nonpoint-descriptor inspected request queries. -/
namespace Yulang.GeneralDictionary171SpineDiscovery
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionary171InspectionObservation
open GeneralDictionary171LocalInspectionObservation (PointInspection)
variable {roles : Roles.RoleDecls}

/-- Input-side structural facts only, with no requested output observation,
Instance, BranchModels, semantic Evidence, or assumed successful selection. -/
structure Input (context : Context) (root : Occurrence roles) (declaration : Declaration) where
  terminal : declaration.requirements = []
  role : declaration.role = root.demand.role
  slot : Fin context.state.base.slots
  arity : Nat
  names : Fin arity → Nat
  distinct : Function.Injective names
  inputs : declaration.inputNames = List.ofFn names
  bounds : Fin arity → GeneralNominalInspection.Bounds context.state
  spine : GeneralNominalSpineFacts.Spine context.state names bounds slot
  query : GeneralNominalInspection.queries context.state context.interpretation declaration = [spine.query]
  located : arguments context root = some [(slot,slot)]
  defined : GeneralNominalMaterialization.RootDefined declaration root

/-- These are actual tests of normalized emitted requests at physical slots.
The target-to-source identity equality is essential and is not model equality. -/
def RequestsFinished (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (input : Input context root declaration) : Prop :=
  ∀ request ∈ GeneralNominalMaterialization.requests context.state registry root declaration checked
      (bindings context.state (report context declaration [(input.slot,input.slot)])),
    ∃ slot : Fin context.state.base.slots,
      request.target = context.state.base.source slot ∧
      Closed (GeneralNominalInspection.translate context.state.constructors context.interpretation
        (GeneralDeclarationPatterns.normalize request.pattern)) ∧
      Finished (inspect context.state
        (GeneralNominalInspection.translate context.state.constructors context.interpretation
          (GeneralDeclarationPatterns.normalize request.pattern)) (slot,slot) (some (.source request.target))) ∧
      PointInspection context.state (inspect context.state
        (GeneralNominalInspection.translate context.state.constructors context.interpretation
          (GeneralDeclarationPatterns.normalize request.pattern)) (slot,slot) (some (.source request.target)))

def shape (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (input : Input context root declaration)
    (tested : RequestsFinished registry context root declaration checked input) :
    GeneralDictionary170NamedSpine.Shape registry context root declaration checked where
  terminal := input.terminal
  role := input.role
  slot := input.slot
  arity := input.arity
  names := input.names
  distinct := input.distinct
  inputs := input.inputs
  bounds := input.bounds
  spine := input.spine
  query := input.query
  located := input.located
  defined := input.defined
  observed := GeneralDictionary171LocalInspectionObservation.observed_requests context.state context.interpretation _ tested

/-- Finished request inspections construct the entire branch's semantic facts,
not only a new label for a supplied Instance. -/
theorem branch_models (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (input : Input context root declaration)
    (tested : RequestsFinished registry context root declaration checked input)
    (model : GeneralNominalCommonBridge.Assignment) (valid : GeneralNominalState.Models context.state model) :
    BranchModels registry context root declaration checked [(input.slot,input.slot)] model :=
  GeneralDictionary170NamedSpine.branch_models _ _ _ _ _ (shape registry context root declaration checked input tested) model valid

/-- The resulting local node is available without a model or a dictionary.
Coverage of any domain still requires its remaining nodes and closure. -/
def node (registry : Registry) (state : GeneralNominalSupport.Tracked roles) (root : Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (input : Input state.current.context root declaration)
    (tested : RequestsFinished registry state.current.context root declaration checked input) :
    GeneralDictionary171SpineCoverage.Node registry state root :=
  .namedSpine root declaration visible checked (shape registry state.current.context root declaration checked input tested)

/-- One explicit terminal payload works for all current source models. This
statement does not assert model existence or global V5 evidenceNode. -/
theorem uniform_evidence (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (input : Input context root declaration)
    (tested : RequestsFinished registry context root declaration checked input)
    (metadata : Metadata registry context) :
    ∀ model, GeneralNominalState.Models context.state model →
      GeneralDictionaryRecursiveEvidence.Evidence registry context model root (.node declaration.id []) :=
  fun model valid => GeneralDictionary170NamedSpine.evidence_of_shape context registry root declaration visible checked
    (shape registry context root declaration checked input tested) metadata model valid
end Yulang.GeneralDictionary171SpineDiscovery
