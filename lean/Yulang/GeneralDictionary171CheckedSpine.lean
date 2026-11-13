import Yulang.GeneralDictionary171RequestChecker
import Yulang.GeneralDictionary171SpineDiscovery

/-! A physical-slot request checker constructs the named-spine local
certificate. No caller-provided request tests or observation Trees are required.
The input spine is still an explicit structural premise. -/
namespace Yulang.GeneralDictionary171CheckedSpine
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionary171SpineDiscovery (Input)
open GeneralDictionary171RequestChecker
variable {roles : Roles.RoleDecls}

def requests (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (input : Input context root declaration) :=
  GeneralNominalMaterialization.requests context.state registry root declaration checked
    (bindings context.state (report context declaration [(input.slot,input.slot)]))

def check (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (input : Input context root declaration) : Bool :=
  checkRequests context.state context.interpretation (requests registry context root declaration checked input)

def shape (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (input : Input context root declaration)
    (success : check registry context root declaration checked input = true) :
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
  observed := checkRequests_sound context.state context.interpretation _ success

/-- A successful executable request check produces a new terminal local node.
Failure is only refusal of this sufficient checker, not language rejection. -/
def discover (registry : Registry) (state : GeneralNominalSupport.Tracked roles) (root : Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (input : Input state.current.context root declaration) :
    Option (GeneralDictionary171SpineCoverage.Node registry state root) :=
  if success : check registry state.current.context root declaration checked input = true then
    some (.namedSpine root declaration visible checked
      (shape registry state.current.context root declaration checked input success))
  else none

/-- Exact computational success criterion, without a coverage or model premise. -/
theorem discover_success_iff (registry : Registry) (state : GeneralNominalSupport.Tracked roles) (root : Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (input : Input state.current.context root declaration) :
    (∃ node, discover registry state root declaration visible checked input = some node) ↔
      check registry state.current.context root declaration checked input = true := by
  unfold discover
  split
  · rename_i success
    exact ⟨fun _ => success,fun _ => ⟨_,rfl⟩⟩
  · rename_i failed
    constructor
    · rintro ⟨node,impossible⟩; cases impossible
    · intro success; exact False.elim (failed success)

theorem uniform_evidence (registry : Registry) (context : Context) (root : Occurrence roles)
    (declaration : Declaration) (visible : declaration ∈ registry.declarations)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (input : Input context root declaration)
    (success : check registry context root declaration checked input = true)
    (metadata : Metadata registry context) :
    ∀ model, GeneralNominalState.Models context.state model →
      GeneralDictionaryRecursiveEvidence.Evidence registry context model root (.node declaration.id []) :=
  fun model valid => GeneralDictionary170NamedSpine.evidence_of_shape context registry root declaration visible checked
    (shape registry context root declaration checked input success) metadata model valid
end Yulang.GeneralDictionary171CheckedSpine
