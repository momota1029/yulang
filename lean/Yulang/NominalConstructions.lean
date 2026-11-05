import Yulang.LiteralCasts

/-!
# Deferred boundaries for nominal construction parameters

Spec §6.5 (2026-11-05) extends deferred list-element boundaries to every nominal
construction with invariant parameters, including struct literals and enum
constructors. Each deferred value site is assigned to one resolved parameter
slot; fixed fields retain their ordinary checks outside this planner. Several sites may constrain the same slot; different slots are
resolved independently. A supplied target is checked at every corresponding
site. At EOF an unsolved slot retains the union descriptor of exactly its
original source types and introduces no cast at those sites.

The plan preserves the constructor (including enum tag), construction identity,
site order, and each original site/parameter assignment. It does not modify a
previously constructed nominal value. Covariant tuple/record/variant traversal
continues to belong to `Casts`, not this invariant-parameter planner.

The one-parameter list construction specializes exactly to `LiteralCasts.finish`.
An unused, unsolved parameter records `unionOf []`, as the empty list already did:
this is a descriptor, not a choice of bottom/default or a proof that such a type
can be exported. Source elaboration must find every parameter occurrence and the
weak-variable solver / module finalizer must resolve or reject remaining holes.
-/

namespace Yulang.NominalConstructions

open Casts

inductive Constructor where
  | listLiteral (nominal : Nat)
  | structLiteral (nominal : Nat)
  | enumConstructor (nominal tag : Nat)
  deriving DecidableEq, Repr

/-- A resolved occurrence of an invariant parameter at its original source site. -/
structure Argument (parameters : Nat) where
  parameter : Fin parameters
  original : LiteralCasts.Element
  deriving DecidableEq, Repr

structure Construction (parameters : Nat) where
  constructor : Constructor
  construction : Nat
  arguments : List (Argument parameters)
  deriving DecidableEq, Repr

abbrev Expectation (parameters : Nat) := Fin parameters → Option Ty
abbrev ParameterType := LiteralCasts.ElementType

inductive Instruction (parameters : Nat) where
  | keep (argument : Argument parameters)
  | boundary (argument : Argument parameters) (target : Ty)
  deriving DecidableEq, Repr

def Instruction.original : Instruction parameters → Argument parameters
  | .keep argument | .boundary argument _ => argument

structure Plan (parameters : Nat) where
  constructor : Constructor
  construction : Nat
  parameterTypes : Fin parameters → ParameterType
  instructions : List (Instruction parameters)

def Construction.sourcesFor (construction : Construction parameters) (parameter : Fin parameters) :
    List Ty :=
  construction.arguments.filterMap (fun argument =>
    if argument.parameter = parameter then some argument.original.source else none)

def Construction.parameterType (construction : Construction parameters)
    (expected : Expectation parameters) (parameter : Fin parameters) : ParameterType :=
  match expected parameter with
  | some target => .expected target
  | none => .unionOf (construction.sourcesFor parameter)

def instruction (expected : Expectation parameters) (argument : Argument parameters) :
    Instruction parameters :=
  match expected argument.parameter with
  | some target => .boundary argument target
  | none => .keep argument

def Construction.plan (construction : Construction parameters)
    (expected : Expectation parameters) : Plan parameters where
  constructor := construction.constructor
  construction := construction.construction
  parameterTypes := construction.parameterType expected
  instructions := construction.arguments.map (instruction expected)

/-- The proposition uses the independent ground boundary judgement. -/
def SiteAllowed (fits explicit : Ty → Ty → Prop) (expected : Expectation parameters)
    (argument : Argument parameters) : Prop :=
  match expected argument.parameter with
  | some target => Boundary fits explicit argument.original.source target
  | none => True

def siteCheck (fits explicit : Ty → Ty → Bool) (expected : Expectation parameters)
    (argument : Argument parameters) : Bool :=
  match expected argument.parameter with
  | some target => accepts fits explicit argument.original.source target
  | none => true

theorem siteCheck_exact (fits : Compatibility) (registry : CastGraph.Registry n)
    (expected : Expectation parameters) (argument : Argument parameters) :
    siteCheck fits.check registry.find expected argument = true ↔
      SiteAllowed fits.Rel registry.Explicit expected argument := by
  cases chosen : expected argument.parameter with
  | none => simp [siteCheck, SiteAllowed, chosen]
  | some target =>
      simp only [siteCheck, SiteAllowed, chosen]
      exact accepts_exact fits registry.oracle _ _

def sitesAccept (fits : Compatibility) (registry : CastGraph.Registry n)
    (construction : Construction parameters) (expected : Expectation parameters) : Bool :=
  construction.arguments.all (siteCheck fits.check registry.find expected)

theorem sitesAccept_exact (fits : Compatibility) (registry : CastGraph.Registry n)
    (construction : Construction parameters) (expected : Expectation parameters) :
    sitesAccept fits registry construction expected = true ↔
      ∀ argument ∈ construction.arguments,
        SiteAllowed fits.Rel registry.Explicit expected argument := by
  simp only [sitesAccept, List.all_eq_true, siteCheck_exact]

def finish (fits : Compatibility) (registry : CastGraph.Registry n)
    (construction : Construction parameters) (expected : Expectation parameters) :
    Option (Plan parameters) :=
  if registry.validate && sitesAccept fits registry construction expected then
    some (construction.plan expected)
  else none

/-- A valid plan checks every known-parameter occurrence; unknown parameters
keep their original sites. The judgement does not call the executable checker. -/
inductive PlanTyping (fits : Compatibility) (registry : CastGraph.Registry n)
    (construction : Construction parameters) (expected : Expectation parameters) :
    Plan parameters → Prop where
  | build : registry.WellFormed →
      (∀ argument ∈ construction.arguments,
        SiteAllowed fits.Rel registry.Explicit expected argument) →
      PlanTyping fits registry construction expected (construction.plan expected)

theorem finish_exact (fits : Compatibility) (registry : CastGraph.Registry n)
    (construction : Construction parameters) (expected : Expectation parameters)
    (plan : Plan parameters) :
    finish fits registry construction expected = some plan ↔
      PlanTyping fits registry construction expected plan := by
  by_cases checks : (registry.validate && sitesAccept fits registry construction expected) = true
  · have parts : registry.validate = true ∧ sitesAccept fits registry construction expected = true := by
      simpa only [Bool.and_eq_true] using checks
    have valid := registry.validate_exact.mp parts.1
    have allowed := (sitesAccept_exact fits registry construction expected).mp parts.2
    constructor
    · intro finished
      have same : construction.plan expected = plan := by simpa [finish, checks] using finished
      cases same
      exact .build valid allowed
    · intro typed
      cases typed
      simp [finish, checks]
  · constructor
    · simp [finish, checks]
    · intro typed
      cases typed with
      | build valid allowed =>
          apply False.elim
          apply checks
          simp only [Bool.and_eq_true]
          exact ⟨registry.validate_exact.mpr valid,
            (sitesAccept_exact fits registry construction expected).mpr allowed⟩

theorem plan_retains_original_sites (construction : Construction parameters)
    (expected : Expectation parameters) :
    (construction.plan expected).instructions.map Instruction.original = construction.arguments := by
  have identity : (fun argument : Argument parameters =>
      (instruction expected argument).original) = id := by
    funext argument
    cases chosen : expected argument.parameter <;> simp [instruction, Instruction.original, chosen]
  simp only [Construction.plan, List.map_map, Function.comp_def, identity, List.map_id]

theorem plan_retains_constructor (construction : Construction parameters)
    (expected : Expectation parameters) :
    (construction.plan expected).constructor = construction.constructor := rfl

theorem plan_retains_construction (construction : Construction parameters)
    (expected : Expectation parameters) :
    (construction.plan expected).construction = construction.construction := rfl

theorem accepted_site_boundary (fits : Compatibility) (registry : CastGraph.Registry n)
    (construction : Construction parameters) (expected : Expectation parameters) (plan : Plan parameters)
    (accepted : finish fits registry construction expected = some plan)
    (argument : Argument parameters) (present : argument ∈ construction.arguments)
    (target : Ty) (known : expected argument.parameter = some target) :
    Boundary fits.Rel registry.Explicit argument.original.source target := by
  have typed := (finish_exact fits registry construction expected plan).mp accepted
  cases typed with
  | build _ allowed => simpa [SiteAllowed, known] using allowed argument present

theorem one_bad_site_rejects (fits : Compatibility) (registry : CastGraph.Registry n)
    (construction : Construction parameters) (expected : Expectation parameters)
    (argument : Argument parameters) (present : argument ∈ construction.arguments)
    (target : Ty) (known : expected argument.parameter = some target)
    (impossible : ¬ Boundary fits.Rel registry.Explicit argument.original.source target) :
    finish fits registry construction expected = none := by
  cases outcome : finish fits registry construction expected with
  | none => rfl
  | some plan =>
      exact False.elim (impossible (accepted_site_boundary fits registry construction expected plan
        outcome argument present target known))

theorem unresolved_site_kept (construction : Construction parameters)
    (expected : Expectation parameters) (argument : Argument parameters)
    (present : argument ∈ construction.arguments) (unknown : expected argument.parameter = none) :
    Instruction.keep argument ∈ (construction.plan expected).instructions := by
  apply List.mem_map.mpr
  exact ⟨argument, present, by simp [instruction, unknown]⟩

theorem resolved_site_boundary (construction : Construction parameters)
    (expected : Expectation parameters) (argument : Argument parameters)
    (present : argument ∈ construction.arguments) (target : Ty)
    (known : expected argument.parameter = some target) :
    Instruction.boundary argument target ∈ (construction.plan expected).instructions := by
  apply List.mem_map.mpr
  exact ⟨argument, present, by simp [instruction, known]⟩

theorem other_parameters_do_not_change_site (left right : Expectation parameters)
    (argument : Argument parameters) (same : left argument.parameter = right argument.parameter) :
    instruction left argument = instruction right argument := by
  simp only [instruction, same]

theorem eof_without_expectations (fits : Compatibility) (registry : CastGraph.Registry n)
    (construction : Construction parameters) (valid : registry.WellFormed) :
    finish fits registry construction (fun _ => none) =
      some (construction.plan (fun _ => none)) := by
  simp [finish, sitesAccept, siteCheck, registry.validate_exact.mpr valid]

theorem eof_original_union (construction : Construction parameters) (parameter : Fin parameters) :
    (construction.plan (fun _ => none)).parameterTypes parameter =
      .unionOf (construction.sourcesFor parameter) := rfl

theorem eof_no_boundaries (construction : Construction parameters) :
    (construction.plan (fun _ => none)).instructions =
      construction.arguments.map Instruction.keep := rfl

theorem unused_parameter_descriptor (construction : Construction parameters)
    (expected : Expectation parameters) (parameter : Fin parameters)
    (unknown : expected parameter = none)
    (unused : ∀ argument ∈ construction.arguments, argument.parameter ≠ parameter) :
    (construction.plan expected).parameterTypes parameter = .unionOf [] := by
  have empty : construction.sourcesFor parameter = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro type member
    obtain ⟨argument, present, selected⟩ := List.mem_filterMap.mp member
    have different := unused argument present
    simp [different] at selected
  simp [Construction.plan, Construction.parameterType, unknown, empty]

/-! ## The existing list planner is an exact special case. -/

def ofLiteral (name : Nat) (literal : LiteralCasts.DeferredLiteral) : Construction 1 :=
  ⟨.listLiteral name, literal.construction,
    literal.elements.map (fun element => ⟨0, element⟩)⟩

def Instruction.toLiteral : Instruction 1 → LiteralCasts.Instruction
  | .keep argument => .keep argument.original
  | .boundary argument target => .boundary argument.original target

def Plan.toLiteral (plan : Plan 1) : LiteralCasts.Plan :=
  ⟨plan.construction, plan.parameterTypes 0, plan.instructions.map Instruction.toLiteral⟩

theorem literal_sources (name : Nat) (literal : LiteralCasts.DeferredLiteral) :
    (ofLiteral name literal).sourcesFor 0 = literal.elements.map LiteralCasts.Element.source := by
  simp [ofLiteral, Construction.sourcesFor, List.filterMap_map, Function.comp_def]

theorem literal_target_plan (name : Nat) (literal : LiteralCasts.DeferredLiteral) (target : Ty) :
    ((ofLiteral name literal).plan (fun _ => some target)).toLiteral = literal.targetPlan target := by
  simp [ofLiteral, Construction.plan, Construction.parameterType, Plan.toLiteral,
    instruction, Instruction.toLiteral, LiteralCasts.DeferredLiteral.targetPlan,
    List.map_map, Function.comp_def]

theorem literal_fallback_plan (name : Nat) (literal : LiteralCasts.DeferredLiteral) :
    ((ofLiteral name literal).plan (fun _ => none)).toLiteral = literal.fallbackPlan := by
  simp only [Plan.toLiteral, Construction.plan, Construction.parameterType, literal_sources]
  simp [ofLiteral, instruction, Instruction.toLiteral, LiteralCasts.DeferredLiteral.fallbackPlan,
    List.map_map, Function.comp_def]

theorem finish_literal_exact (fits : Compatibility) (registry : CastGraph.Registry n)
    (name : Nat) (literal : LiteralCasts.DeferredLiteral) (expected : Option Ty) :
    (finish fits registry (ofLiteral name literal) (fun _ => expected)).map Plan.toLiteral =
      LiteralCasts.finish fits registry literal expected := by
  cases expected with
  | none =>
      by_cases valid : registry.validate = true
      · simp [finish, sitesAccept, siteCheck, valid, LiteralCasts.finish, literal_fallback_plan]
      · simp [finish, valid, LiteralCasts.finish]
  | some target =>
      have sameSites : sitesAccept fits registry (ofLiteral name literal) (fun _ => some target) =
          LiteralCasts.sitesAccept fits registry literal target := by
        simp [sitesAccept, siteCheck, ofLiteral, LiteralCasts.sitesAccept, List.all_map, Function.comp_def]
      by_cases valid : registry.validate = true
      · cases sites : LiteralCasts.sitesAccept fits registry literal target <;>
          simp [finish, valid, sameSites, sites, LiteralCasts.finish, literal_target_plan]
      · simp [finish, valid, LiteralCasts.finish]

namespace Examples

private def intType : Ty := .base .int
private def strType : Ty := .base .str
private def idType : Ty := .nominal 0 []

attribute [local simp] accepts converts Casts.fields Ty.isNominal Ty.isRecord Ty.lookup
  equalityCompatibility intType strType idType

def idToInt : CastGraph.Registry 2 where
  types := fun vertex => if vertex = 0 then idType else intType
  rules := [(0, 1)]

def box : Construction 1 :=
  ⟨.structLiteral 2, 100, [⟨0, ⟨101, idType⟩⟩]⟩

theorem box_checks_original_site :
    finish equalityCompatibility idToInt box (fun _ => some intType) =
      some (box.plan (fun _ => some intType)) := by
  simp only [finish]
  have checked : (idToInt.validate && sitesAccept equalityCompatibility idToInt box (fun _ => some intType)) = true := by
    simp [sitesAccept, siteCheck, box] <;> decide
  rw [checked]
  rfl

def fields : Construction 2 :=
  ⟨.structLiteral 3, 200,
    [⟨0, ⟨201, idType⟩⟩, ⟨1, ⟨202, strType⟩⟩, ⟨0, ⟨203, intType⟩⟩]⟩

def partialTargets : Expectation 2 := fun parameter => if parameter = 0 then some intType else none

theorem repeated_parameter_sites_all_checked :
    finish equalityCompatibility idToInt fields partialTargets =
      some (fields.plan partialTargets) := by
  simp only [finish]
  have checked : (idToInt.validate && sitesAccept equalityCompatibility idToInt fields partialTargets) = true := by
    simp [sitesAccept, siteCheck, fields, partialTargets] <;> decide
  rw [checked]
  rfl

theorem other_parameter_falls_back_independently :
    (fields.plan partialTargets).parameterTypes 1 = .unionOf [strType] := by rfl

theorem eof_joins_only_the_same_parameter :
    (fields.plan (fun _ => none)).parameterTypes 0 = .unionOf [idType, intType] := by rfl

def enumValue : Construction 1 :=
  ⟨.enumConstructor 4 7, 300, [⟨0, ⟨301, idType⟩⟩]⟩

theorem enum_payload_boundary_is_at_construction :
    finish equalityCompatibility idToInt enumValue (fun _ => some intType) =
      some (enumValue.plan (fun _ => some intType)) := by
  simp only [finish]
  have checked : (idToInt.validate && sitesAccept equalityCompatibility idToInt enumValue (fun _ => some intType)) = true := by
    simp [sitesAccept, siteCheck, enumValue] <;> decide
  rw [checked]
  rfl

theorem enum_tag_retained :
    (enumValue.plan (fun _ => some intType)).constructor = .enumConstructor 4 7 := rfl

def impossibleFields : Construction 1 :=
  ⟨.structLiteral 5, 400, [⟨0, ⟨401, idType⟩⟩, ⟨0, ⟨402, strType⟩⟩]⟩

theorem one_field_without_cast_rejects_construction :
    finish equalityCompatibility idToInt impossibleFields (fun _ => some intType) = none := by
  simp only [finish]
  have checked : (idToInt.validate && sitesAccept equalityCompatibility idToInt impossibleFields (fun _ => some intType)) = false := by
    simp [sitesAccept, siteCheck, impossibleFields] <;> decide
  rw [checked]
  rfl

end Examples
end Yulang.NominalConstructions
