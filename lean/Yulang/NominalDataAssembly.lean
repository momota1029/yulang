import Yulang.NominalConstructionRuntime
import Yulang.CaseDataTerms

/-!
# Concrete data construction after resolved deferred boundaries

The deferred-site runtime and the concrete data AST meet here. Each original
site is evaluated once, in the planner's order, and its checked pure conversion
runs at that site. Its returned value is bound to the resolved site identity;
the supplied `CaseDataTerms` constructor body then assembles the result. Even
sites hidden by a record field or unused by the body keep their requests.

`Code` retains the nominal identity and enum tag from the plan. A struct's
constructor identity is explicitly supplied by declaration resolution. Lists
use the existing concrete `Value.list` representation and retain their nominal
identity in the construction metadata. No constructor identity is invented.

The value-safety theorem uses independent concrete AST typing, typed source
sites, compatibility preservation and a typed-code contract for the allowed
incompatible boundaries. Code purity follows from `PureCasts.Plan`. No choice
of weak-variable targets or synthesis of conversion code is made here.

This is the resolved construction stage, not a translation of arbitrary source
expressions. Extracting all original sites, generating the constructor body,
checking fixed field declarations/defaults and resolving Fold/Index dictionaries
remain elaboration obligations. Site computations may have signed requests;
the assembly body itself is the existing finite, pure data AST.
-/

namespace Yulang.NominalDataAssembly

open Directed Directed.Computation NominalConstructions NominalConstructionRuntime PureCasts
open CaseValues

variable {parameters n nodes : Nat} {F Key Payload Response : Type}

/-- The body is already resolved to source-site variables. Its outer nominal
wrapper is fixed by the plan rather than supplied as an unchecked expression. -/
inductive Code (F : Type) : Constructor → Type where
  | list (nominal : Nat) (body : CaseDataTerms.Expr F) : Code F (.listLiteral nominal)
  | structLiteral (nominal constructorId : Nat) (body : CaseDataTerms.Expr F) :
      Code F (.structLiteral nominal)
  | enumeration (nominal tag : Nat) (body : CaseDataTerms.Expr F) :
      Code F (.enumConstructor nominal tag)

def Code.expression : {constructor : Constructor} → Code F constructor → CaseDataTerms.Expr F
  | _, .list _ body => body
  | _, .structLiteral nominal constructorId body => .nominal nominal constructorId body
  | _, .enumeration nominal tag body => .nominal nominal tag body

inductive Typing (types : List (Nat × Ty F)) :
    {constructor : Constructor} → Code F constructor → Ty F → Prop where
  | list : CaseDataTerms.Typing types body type → Ty.Le type (Ty.list Ty.any) →
      Typing types (.list nominal body) type
  | structLiteral : CaseDataTerms.Typing types body type → Ty.Le type Ty.records →
      Typing types (.structLiteral nominal constructorId body) (Ty.nominal nominal constructorId type)
  | enumeration : CaseDataTerms.Typing types body type →
      Typing types (.enumeration nominal tag body) (Ty.nominal nominal tag type)

theorem Typing.expression {types : List (Nat × Ty F)} {constructor : Constructor}
    {code : Code F constructor} {type : Ty F} (typed : Typing types code type) :
    CaseDataTerms.Typing types code.expression type := by
  cases typed with
  | list bodyTyped _ => exact bodyTyped
  | structLiteral bodyTyped _ | enumeration bodyTyped => exact .nominal bodyTyped

def bindArguments : List (Argument parameters) → List (Value F) → Bindings F
  | argument :: rest, value :: values =>
      (argument.original.site, value) :: bindArguments rest values
  | _, _ => []

def bindSites (instructions : List (Instruction parameters)) (values : List (Value F)) : Bindings F :=
  bindArguments (instructions.map Instruction.original) values

def siteTypes (HasType : Casts.Ty → Ty F) (instructions : List (Instruction parameters)) :
    List (Nat × Ty F) :=
  instructions.map fun instruction => (instruction.original.original.site, HasType (resultType instruction))

theorem bindings_typed (HasType : Casts.Ty → Ty F)
    {instructions : List (Instruction parameters)} {values : List (Value F)}
    (typed : ValuesTyped HasType instructions values) :
    BindingsHold (siteTypes HasType instructions) (bindSites instructions values) := by
  induction typed with
  | nil => exact .nil
  | cons head _ ih => exact .cons head ih

structure Built (parameters : Nat) (F : Type) where
  constructor : Constructor
  construction : Nat
  parameterTypes : Fin parameters → ParameterType
  evaluation : CaseDataTerms.Result F

def execute (runtime : Runtime parameters n Key Payload Response (Value F))
    (plan : NominalConstructions.Plan parameters) (code : Code F plan.constructor) :
    Computation n Key Payload Response (Built parameters F) :=
  mapValue (fun values => ⟨plan.constructor, plan.construction, plan.parameterTypes,
    CaseDataTerms.eval (bindSites plan.instructions values) code.expression⟩)
    (runValues runtime plan.instructions)

/-- This assembly is an exact continuation of the existing site executor;
it does not independently replay or reorder the source computations. -/
theorem execute_runtime (runtime : Runtime parameters n Key Payload Response (Value F))
    (plan : NominalConstructions.Plan parameters) (code : Code F plan.constructor) :
    execute runtime plan code =
      mapValue (fun built : NominalConstructionRuntime.Built parameters (Value F) =>
        (⟨built.constructor, built.construction, built.parameterTypes,
          CaseDataTerms.eval (bindSites plan.instructions built.values) code.expression⟩ : Built parameters F))
        (NominalConstructionRuntime.execute runtime plan) := by
  rw [NominalConstructionRuntime.execute, mapValue_comp]
  rfl

/-- No typing premise is needed to preserve the entire request tree. Pure
assembly cannot erase requests even when its result later reports an error. -/
theorem execute_requestTree (runtime : Runtime parameters n Key Payload Response (Value F))
    (plan : NominalConstructions.Plan parameters) (code : Code F plan.constructor) :
    requestTree (execute runtime plan code) =
      requestTree (readValues runtime.source (plan.instructions.map Instruction.original)) := by
  unfold execute requestTree
  rw [mapValue_comp]
  exact runValues_requestTree runtime plan.instructions

theorem accepted_requestTree (runtime : Runtime parameters n Key Payload Response (Value F))
    (registry : CastGraph.Registry nodes) (construction : Construction parameters)
    (expected : Expectation parameters) (plan : NominalConstructions.Plan parameters)
    (accepted : finish runtime.fits registry construction expected = some plan)
    (code : Code F plan.constructor) :
    requestTree (execute runtime plan code) =
      requestTree (readValues runtime.source construction.arguments) := by
  have typed := (finish_exact runtime.fits registry construction expected plan).mp accepted
  cases typed
  rw [execute_requestTree, plan_retains_original_sites]

/-- EOF executes the same original sites and supplies their exact original
values to the concrete body, with the original union parameter descriptors. -/
theorem execute_eof (runtime : Runtime parameters n Key Payload Response (Value F))
    (construction : Construction parameters) (code : Code F construction.constructor) :
    execute runtime (construction.plan (fun _ => none)) code =
      mapValue (fun values =>
        (⟨construction.constructor, construction.construction,
          (construction.plan (fun _ => none)).parameterTypes,
          CaseDataTerms.eval (bindArguments construction.arguments values) code.expression⟩ : Built parameters F))
        (readValues runtime.source construction.arguments) := by
  unfold execute bindSites
  rw [plan_retains_original_sites, eof_no_boundaries, runValues_keep]
  rfl

/-- Code generation must discharge these local value contracts. The checked
boundary judgement does not itself provide executable conversion code. -/
structure CastContract (runtime : Runtime parameters n Key Payload Response (Value F))
    (registry : CastGraph.Registry nodes) (HasType : Casts.Ty → Ty F) : Prop where
  compatible : ∀ source target value, runtime.fits.Rel source target →
    HasType source value → HasType target value
  converted : ∀ argument target,
    Casts.Boundary runtime.fits.Rel registry.Explicit argument.original.source target →
    ¬ runtime.fits.Rel argument.original.source target → ∀ value,
    HasType argument.original.source value →
      HasType target ((runtime.convert argument target).value value)

theorem boundary_typed (runtime : Runtime parameters n Key Payload Response (Value F))
    (registry : CastGraph.Registry nodes) (HasType : Casts.Ty → Ty F)
    (contract : CastContract runtime registry HasType) (argument : Argument parameters) (target : Casts.Ty)
    (allowed : Casts.Boundary runtime.fits.Rel registry.Explicit argument.original.source target)
    (value : Value F) (valid : HasType argument.original.source value) :
    HasType target ((runtime.code (.boundary argument target)).value value) := by
  simp only [Runtime.code]
  split
  · rename_i compatibleCheck
    exact contract.compatible _ _ value ((runtime.fits.exact _ _).mp compatibleCheck) valid
  · rename_i differs
    exact contract.converted argument target allowed
      (fun same => differs ((runtime.fits.exact _ _).mpr same)) value valid

private theorem instruction_original (expected : Expectation parameters) (argument : Argument parameters) :
    (instruction expected argument).original = argument := by
  cases chosen : expected argument.parameter <;> simp [instruction, chosen, Instruction.original]

theorem accepted_values_typed (runtime : Runtime parameters n Key Payload Response (Value F))
    (registry : CastGraph.Registry nodes) (construction : Construction parameters)
    (expected : Expectation parameters) (plan : NominalConstructions.Plan parameters)
    (accepted : finish runtime.fits registry construction expected = some plan)
    (HasType : Casts.Ty → Ty F) (contract : CastContract runtime registry HasType)
    (sources : ∀ argument ∈ construction.arguments,
      AllReturns (HasType argument.original.source) (runtime.source argument)) :
    AllReturns (ValuesTyped HasType plan.instructions) (runValues runtime plan.instructions) := by
  have typed := (finish_exact runtime.fits registry construction expected plan).mp accepted
  cases typed with
  | build _ allowed =>
      apply runValues_typed
      · intro item member
        obtain ⟨argument, present, rfl⟩ := List.mem_map.mp member
        simpa only [instruction_original] using sources argument present
      · intro item member value valid
        obtain ⟨argument, present, rfl⟩ := List.mem_map.mp member
        rw [instruction_original] at valid
        cases chosen : expected argument.parameter with
        | none => simpa [instruction, chosen, resultType, Runtime.code, PureCasts.Plan.value] using valid
        | some target =>
            have boundary : Casts.Boundary runtime.fits.Rel registry.Explicit argument.original.source target := by
              simpa [SiteAllowed, chosen] using allowed argument present
            simpa [instruction, chosen, resultType] using
              boundary_typed runtime registry HasType contract argument target boundary value valid

private theorem allReturns_mono (source : Computation n Key Payload Response A)
    (P Q : A → Prop) (implies : ∀ value, P value → Q value) (valid : AllReturns P source) :
    AllReturns Q source := by
  induction source with
  | pure value => exact implies value valid
  | request occurrence payload resume ih => exact fun response => ih response (valid response)

/-- Accepted boundaries and the independent constructor-body derivation imply
successful concrete construction in every response branch. No successful body
evaluation or whole-expression operational validity is assumed. -/
theorem typing_evaluates (runtime : Runtime parameters n Key Payload Response (Value F))
    (registry : CastGraph.Registry nodes) (construction : Construction parameters)
    (expected : Expectation parameters) (plan : NominalConstructions.Plan parameters)
    (accepted : finish runtime.fits registry construction expected = some plan)
    (code : Code F plan.constructor) (HasType : Casts.Ty → Ty F)
    (contract : CastContract runtime registry HasType)
    (sources : ∀ argument ∈ construction.arguments,
      AllReturns (HasType argument.original.source) (runtime.source argument))
    (type : Ty F) (typed : Typing (siteTypes HasType plan.instructions) code type) :
    AllReturns (fun built => built.constructor = plan.constructor ∧
      built.construction = plan.construction ∧ built.parameterTypes = plan.parameterTypes ∧
      ∃ value, built.evaluation.result = .ok value ∧ type value)
      (execute runtime plan code) := by
  apply (allReturns_map _ _ _).mpr
  apply allReturns_mono _ (ValuesTyped HasType plan.instructions) _ _
    (accepted_values_typed runtime registry construction expected plan accepted HasType contract sources)
  intro values valuesTyped
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact CaseDataTerms.typing_evaluates typed.expression _ (bindings_typed HasType valuesTyped)

end Yulang.NominalDataAssembly
