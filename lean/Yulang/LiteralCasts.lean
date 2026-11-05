import Yulang.CastGraph

/-!
# Deferred boundaries at list-literal construction sites

A deferred literal retains each original source site and its ground element
type. A supplied expected element type is checked at every original site. At
file end without an expectation, the plan keeps every element and records the
union of the original element types; it inserts no element conversion boundary.

These are compile-time construction plans, not values already allocated at
runtime. The weak-variable solver supplies `expected`; this module neither
infers that choice nor modifies a constructed nominal list. `unionOf` retains a
finite union descriptor, including the empty list, without selecting a source
normal form or display for that union.
-/

namespace Yulang.LiteralCasts

open Casts

structure Element where
  site : Nat
  source : Ty
  deriving DecidableEq, Repr

structure DeferredLiteral where
  construction : Nat
  elements : List Element
  deriving DecidableEq, Repr

inductive ElementType where
  | expected (type : Ty)
  | unionOf (members : List Ty)
  deriving DecidableEq, Repr

/-- A boundary is a compile-time checking location, not an assertion that a
conversion executes: ordinary compatibility may make it a no-op. -/
inductive Instruction where
  | keep (original : Element)
  | boundary (original : Element) (target : Ty)
  deriving DecidableEq, Repr

def Instruction.original : Instruction → Element
  | .keep element | .boundary element _ => element

structure Plan where
  construction : Nat
  elementType : ElementType
  instructions : List Instruction
  deriving DecidableEq, Repr

def DeferredLiteral.targetPlan (literal : DeferredLiteral) (target : Ty) : Plan :=
  ⟨literal.construction, .expected target,
    literal.elements.map (fun original => .boundary original target)⟩

def DeferredLiteral.fallbackPlan (literal : DeferredLiteral) : Plan :=
  ⟨literal.construction, .unionOf (literal.elements.map Element.source),
    literal.elements.map Instruction.keep⟩

def sitesAccept (fits : Compatibility) (registry : CastGraph.Registry n)
    (literal : DeferredLiteral) (target : Ty) : Bool :=
  literal.elements.all (fun element => accepts fits.check registry.find element.source target)

theorem sitesAccept_exact (fits : Compatibility) (registry : CastGraph.Registry n)
    (literal : DeferredLiteral) (target : Ty) :
    sitesAccept fits registry literal target = true ↔
      ∀ element ∈ literal.elements, Boundary fits.Rel registry.Explicit element.source target := by
  simp only [sitesAccept, List.all_eq_true]
  exact forall_congr' (fun element => forall_congr' (fun _ =>
    accepts_exact fits registry.oracle element.source target))

def finish (fits : Compatibility) (registry : CastGraph.Registry n)
    (literal : DeferredLiteral) (expected : Option Ty) : Option Plan :=
  if registry.validate then
    match expected with
    | none => some literal.fallbackPlan
    | some target =>
      if sitesAccept fits registry literal target then some (literal.targetPlan target) else none
  else none

/-- Independent planning judgement. Known targets require a boundary at every
original element; fallback keeps original types without searching cast paths. -/
inductive PlanTyping (fits : Compatibility) (registry : CastGraph.Registry n)
    (literal : DeferredLiteral) : Option Ty → Plan → Prop where
  | fallback : registry.WellFormed → PlanTyping fits registry literal none literal.fallbackPlan
  | target : registry.WellFormed →
      (∀ element ∈ literal.elements, Boundary fits.Rel registry.Explicit element.source target) →
      PlanTyping fits registry literal (some target) (literal.targetPlan target)

theorem finish_exact (fits : Compatibility) (registry : CastGraph.Registry n)
    (literal : DeferredLiteral) (expected : Option Ty) (plan : Plan) :
    finish fits registry literal expected = some plan ↔
      PlanTyping fits registry literal expected plan := by
  by_cases valid : registry.validate = true
  · have wellFormed := registry.validate_exact.mp valid
    cases expected with
    | none =>
      constructor
      · intro finished
        have same : literal.fallbackPlan = plan := by simpa [finish, valid] using finished
        cases same
        exact .fallback wellFormed
      · intro typed
        cases typed with
        | fallback _ => simp [finish, valid]
    | some target =>
      by_cases accepted : sitesAccept fits registry literal target = true
      · have allSites := (sitesAccept_exact fits registry literal target).mp accepted
        constructor
        · intro finished
          have same : literal.targetPlan target = plan := by simpa [finish, valid, accepted] using finished
          cases same
          exact .target wellFormed allSites
        · intro typed
          cases typed with
          | target _ _ => simp [finish, valid, accepted]
      · constructor
        · simp [finish, valid, accepted]
        · intro typed
          cases typed with
          | target _ allSites =>
            exact False.elim (accepted ((sitesAccept_exact fits registry literal target).mpr allSites))
  · have malformed : ¬ registry.WellFormed := fun wf => valid (registry.validate_exact.mpr wf)
    constructor
    · simp [finish, valid]
    · intro typed
      cases typed with
      | fallback wf | target wf _ => exact False.elim (malformed wf)

theorem target_retains_original_sites (literal : DeferredLiteral) (target : Ty) :
    (literal.targetPlan target).instructions.map Instruction.original = literal.elements := by
  simp [DeferredLiteral.targetPlan, List.map_map, Function.comp_def, Instruction.original]

theorem fallback_retains_original_sites (literal : DeferredLiteral) :
    literal.fallbackPlan.instructions.map Instruction.original = literal.elements := by
  simp [DeferredLiteral.fallbackPlan, List.map_map, Function.comp_def, Instruction.original]

theorem eof_without_expectation (fits : Compatibility) (registry : CastGraph.Registry n)
    (literal : DeferredLiteral) (valid : registry.WellFormed) :
    finish fits registry literal none = some literal.fallbackPlan := by
  simp [finish, registry.validate_exact.mpr valid]

theorem eof_original_union (literal : DeferredLiteral) :
    literal.fallbackPlan.elementType = .unionOf (literal.elements.map Element.source) := rfl

theorem eof_no_element_boundaries (literal : DeferredLiteral) :
    literal.fallbackPlan.instructions = literal.elements.map Instruction.keep := rfl

end Yulang.LiteralCasts
