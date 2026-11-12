import Yulang.GeneralNominalRecursiveInspection

/-! Source equations for compound emitted inputs and named output requests.
Each expression is read at its allocated source identity. Variable occurrences
retain the computed capture bounds or output binder identity. Constructor
observations are model decompositions, never a search over substitutions. -/
namespace Yulang.GeneralNominalMaterialization

open GeneralNominalRecursiveInspection
open GeneralNominalInspection (Query)
open GeneralDeclarations GeneralDeclarationDemands
open CommonNominalFullCarrier

inductive Mode where
  | lower | upper | actual
  deriving DecidableEq

structure Use where
  name : Nat
  origin : Origin
  mode : Mode

structure Schema where
  variables : List Use := []
  tests : List (Origin × Test) := []
  unknown : Bool := false

def Schema.append (first last : Schema) : Schema :=
  ⟨first.variables ++ last.variables,first.tests ++ last.tests,first.unknown || last.unknown⟩

mutual
  def schema (query : Query) (origin : Origin) (mode : Mode) : Schema :=
    match query with
    | .variables names => ⟨names.map (fun name => ⟨name,origin,mode⟩),[],false⟩
    | .scalar base => ⟨[],[(origin,.scalar base)],false⟩
    | .deferred _ => ⟨[],[],true⟩
    | .node shape children =>
        let nested := schemas children (fun index => .structural origin shape index) mode 0
        { nested with tests := (origin,.structural shape) :: nested.tests }
    | .nominal name children =>
        let nested := schemas children (fun index => .nominal origin name index) .actual 0
        { nested with tests := (origin,.nominal name children.length) :: nested.tests }
  termination_by sizeOf query

  def schemas : List Query → (Nat → Origin) → Mode → Nat → Schema
    | [],_,_,_ => {}
    | query :: rest,origins,mode,index =>
        (schema query (origins index) mode).append (schemas rest origins mode (index+1))
  termination_by queries _ _ _ => sizeOf queries
end

structure Request where
  pattern : GeneralDeclarationPatterns.Pattern
  target : Nat
  mode : Mode

def inputRequests (input : InputRequest) : List Request :=
  match GeneralDeclarationPatterns.normalize input.pattern with
  | .var _ => []
  | pattern => [⟨pattern,input.endpoints.1,.lower⟩,⟨pattern,input.endpoints.2,.upper⟩]

def emissionRequests (emission : Emission roles) : List Request :=
  emission.inputs.flatMap inputRequests ++ emission.outputs.map fun output => ⟨output.pattern,output.target,.actual⟩

def rootRequests (declaration : Declaration) (root : GeneralSourceDictionaries.Occurrence roles) : List Request :=
  root.demand.outputs.flatMap fun output =>
    ((declaration.associated.find? fun equation => equation.name == output.name).toList).map fun equation =>
      ⟨equation.rhs,output.target,.actual⟩

def RootDefined (declaration : Declaration) (root : GeneralSourceDictionaries.Occurrence roles) : Prop :=
  ∀ output ∈ root.demand.outputs, ∃ equation ∈ declaration.associated, equation.name = output.name

def requests (state : GeneralNominalState.State) (registry : Registry)
    (root : GeneralSourceDictionaries.Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (bindings : GeneralNominalAllocation.Bindings) : List Request :=
  rootRequests declaration root ++
    (GeneralCanonicalChildOrder.canonicalEmit root.identity declaration checked
      (GeneralNominalAllocation.capture state registry root.identity declaration.id bindings)
      (GeneralNominalAllocation.allocation state registry root.identity declaration.id)).flatMap emissionRequests

def generated (state : GeneralNominalState.State) (interpretation : GeneralNominalInspection.Interpretation)
    (requests : List Request) : Schema :=
  (requests.map fun request => schema
    (GeneralNominalInspection.translate state.constructors interpretation (GeneralDeclarationPatterns.normalize request.pattern))
    (.source request.target) request.mode).foldr Schema.append {}

def VariableHolds (declaration : Declaration) (capture : Capture)
    (model : GeneralNominalCommonBridge.Assignment) (name : Nat) (mode : Mode) (actual : Ty) : Prop :=
  if name ∈ declaration.outputNames then Equivalent actual (model (capture.outputs name)).1
  else match mode with
    | .lower => Equivalent actual (model (capture.inputs name).1).1
    | .upper => Equivalent actual (model (capture.inputs name).2).1
    | .actual => GeneralNominalCaptureMerges.Fits model (capture.inputs name) actual

def Models (state : GeneralNominalState.State) (declaration : Declaration) (capture : Capture)
    (report : Report state) (generated : Schema) (model : GeneralNominalCommonBridge.Assignment) : Prop :=
  (∀ test ∈ generated.tests, (∃ actual, Observes model test.1 actual) ∧
    ∀ actual, Observes model test.1 actual → test.2.Holds actual) ∧
  (∀ entry ∈ generated.variables, (∃ actual, Observes model entry.origin actual) ∧
    ∀ actual, Observes model entry.origin actual → VariableHolds declaration capture model entry.name entry.mode actual) ∧
  (∀ first ∈ generated.variables, ∀ last ∈ generated.variables, first.name = last.name → first.mode = .actual → last.mode = .actual →
    ∀ a b, Observes model first.origin a → Observes model last.origin b → Equivalent a b) ∧
  (∀ entry ∈ generated.variables, ∀ captured ∈ report.captures, entry.name = captured.name → entry.mode = .actual →
    ∀ origin, captured.origin = some origin → ∀ a b,
      Observes model entry.origin a → Observes model origin b → Equivalent a b)

theorem empty_models (state : GeneralNominalState.State) (declaration : Declaration) (capture : Capture)
    (report : Report state) (model : GeneralNominalCommonBridge.Assignment) :
    Models state declaration capture report {} model := by simp [Models]

theorem output_variable_equation (state : GeneralNominalState.State) (declaration : Declaration)
    (capture : Capture) (report : Report state) (generated : Schema)
    (model : GeneralNominalCommonBridge.Assignment) (models : Models state declaration capture report generated model)
    (name target : Nat) (outputOnly : name ∈ declaration.outputNames)
    (present : (⟨name,Origin.source target,.actual⟩ : Use) ∈ generated.variables) :
    Equivalent (model target).1 (model (capture.outputs name)).1 := by
  have valid := (models.2.1 ⟨name,.source target,.actual⟩ present).2 (model target).1 (.source target)
  simpa [VariableHolds,outputOnly] using valid


theorem endpoint_variable_equation (state : GeneralNominalState.State) (declaration : Declaration)
    (capture : Capture) (report : Report state) (generated : Schema)
    (model : GeneralNominalCommonBridge.Assignment) (models : Models state declaration capture report generated model)
    (name target : Nat) (input : name ∉ declaration.outputNames)
    (present : (⟨name,Origin.source target,.lower⟩ : Use) ∈ generated.variables) :
    Equivalent (model target).1 (model (capture.inputs name).1).1 := by
  have valid := (models.2.1 ⟨name,.source target,.lower⟩ present).2 (model target).1 (.source target)
  simpa [VariableHolds,input] using valid

theorem upper_endpoint_variable_equation (state : GeneralNominalState.State) (declaration : Declaration)
    (capture : Capture) (report : Report state) (generated : Schema)
    (model : GeneralNominalCommonBridge.Assignment) (models : Models state declaration capture report generated model)
    (name target : Nat) (input : name ∉ declaration.outputNames)
    (present : (⟨name,Origin.source target,.upper⟩ : Use) ∈ generated.variables) :
    Equivalent (model target).1 (model (capture.inputs name).2).1 := by
  have valid := (models.2.1 ⟨name,.source target,.upper⟩ present).2 (model target).1 (.source target)
  simpa [VariableHolds,input] using valid

theorem named_outputs_retained (emission : Emission roles) (output : OutputRequest)
    (present : output ∈ emission.outputs) : (⟨output.pattern,output.target,.actual⟩ : Request) ∈ emissionRequests emission :=
  List.mem_append_right _ (List.mem_map.mpr ⟨output,present,rfl⟩)

end Yulang.GeneralNominalMaterialization
