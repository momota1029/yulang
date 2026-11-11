import Yulang.GeneralSourceK2
import Yulang.GeneralDeclarationDemands
import Yulang.GeneralCandidateIntervals

/-!
# Lossless candidate inspection on checked normalized observations

The finite pattern controls descent, including across a cyclic observation.
Every sibling is retained. Recurrence is a separate predicate on the inspected
positions; neither an early unknown nor a mismatch hides the other positions.

The source translator takes explicit ordinary-constructor name metadata. It
normalizes closed record spines and keeps nominal applications, open tails,
arrow forms and other unsupported patterns as deferred requests. Extracting
that metadata from the source frontend remains a separate bridge.
-/
namespace Yulang.GeneralCandidateInspection

open GeneralSourceState (State)
open GeneralNormalizedObservation (Snapshot Shape Head)
open GeneralDeclarationPatterns (Pattern)

inductive Query where
  | variables (names : List Nat)
  | scalar (base : Inference.Base)
  | node (shape : Shape) (children : List Query)
  | deferred (source : Pattern)

def plainNames : Pattern → Option (List Nat)
  | .var name => some [name]
  | .join first last => do
      let before ← plainNames first
      let after ← plainNames last
      pure (before ++ after)
  | _ => none

/-- A partial source-name interpretation, supplied separately from the arity
catalogue. This module supplies no nominal interpretation. -/
inductive Primitive where
  | scalar (base : Inference.Base)
  | pair
  | emptyRecord
  | exactEmpty

abbrev Primitives := Nat → Option Primitive

def Primitive.parameters : Primitive → List GeneralDeclarationPatterns.ParameterKind
  | .pair => [.type, .type]
  | _ => []

/-- This checks arity and parameter kinds, not source name resolution. -/
def PrimitivesCompatible (constructors : GeneralDeclarationPatterns.Constructors)
    (primitives : Primitives) : Prop :=
  ∀ name primitive, primitives name = some primitive →
    ∃ declaration, constructors name = some declaration ∧ declaration.parameters = primitive.parameters

mutual
  def translate (primitives : Primitives) : Pattern → Query
    | .var name => .variables [name]
    | .variant tag payload => .node (.variant tag)
        [match plainNames payload with
          | some names => .variables names
          | none => translate primitives payload]
    | .app name arguments =>
        match primitives name, arguments with
        | some (.scalar base), [] => .scalar base
        | some .emptyRecord, [] => .node (.record []) []
        | some .exactEmpty, [] => .node .exactEmpty []
        | some .pair, [first, last] => .node .pair
            [translate primitives first, translate primitives last]
        | _, _ => .deferred (.app name arguments)
    | .record label payload tail =>
        match translate primitives tail with
        | .node (.record labels) children =>
            let fields := ((label, translate primitives payload) :: labels.zip children).mergeSort
              (fun first last => first.1 ≤ last.1)
            .node (.record (fields.map Prod.fst)) (fields.map Prod.snd)
        | _ => .deferred (.record label payload tail)
    | other => .deferred other
  termination_by pattern => sizeOf pattern
end

def headQueries (primitives : Primitives) (declaration : GeneralDeclarations.Declaration) : List Query :=
  declaration.normalHead.map (translate primitives)

abbrev Bounds (state : State) := Fin state.slots × Fin state.slots

structure Visit (state : State) where
  pattern : Query
  bounds : Bounds state

inductive Reason where
  | sourceInterpretation
  | lowerUnknown
  | upperNotSimplified
  | headRelation
  | arity

structure Report (state : State) where
  captures : GeneralCandidateIntervals.Bindings state := []
  inspected : List (Visit state) := []
  blocked : List (Visit state × Reason) := []
  conflicts : List (Visit state) := []
  arityProblems : List (List Query × List (Bounds state)) := []

def Report.append (first last : Report state) : Report state :=
  ⟨first.captures ++ last.captures, first.inspected ++ last.inspected,
    first.blocked ++ last.blocked, first.conflicts ++ last.conflicts,
    first.arityProblems ++ last.arityProblems⟩

def Report.visit (pattern : Query) (bounds : Bounds state) (report : Report state) : Report state :=
  { report with inspected := ⟨pattern, bounds⟩ :: report.inspected }

def blocked (pattern : Query) (bounds : Bounds state) (reason : Reason) : Report state :=
  { blocked := [(⟨pattern, bounds⟩, reason)] }

mutual
  def inspect (view : Snapshot state) (pattern : Query) (bounds : Bounds state) : Report state :=
    match pattern with
    | .variables names => { captures := names.map fun name => (name, bounds) }
    | .deferred source => blocked (.deferred source) bounds .sourceInterpretation
    | .scalar expected => Report.visit pattern bounds <|
        match view.heads bounds.1 with
        | .deferred _ => blocked pattern bounds .lowerUnknown
        | .scalar actual =>
            if expected = actual then
              match view.heads bounds.2 with
              | .scalar upper => if expected = upper then {} else
                  blocked pattern bounds .upperNotSimplified
              | _ => blocked pattern bounds .upperNotSimplified
            else { conflicts := [⟨pattern, bounds⟩] }
        | .structural _ _ => blocked pattern bounds .headRelation
    | .node expected patterns => Report.visit pattern bounds <|
        match view.heads bounds.1 with
        | .deferred _ => blocked pattern bounds .lowerUnknown
        | .scalar _ => blocked pattern bounds .headRelation
        | .structural lower children =>
            if view.shapes lower = expected then
              match view.heads bounds.2 with
              | .structural upper targets =>
                  if view.shapes upper = expected then
                    inspectMany view patterns ((List.ofFn children).zip (List.ofFn targets))
                  else blocked pattern bounds .upperNotSimplified
              | _ => blocked pattern bounds .upperNotSimplified
            else blocked pattern bounds .headRelation
  termination_by sizeOf pattern

  def inspectMany (view : Snapshot state) : List Query → List (Bounds state) → Report state
    | [], [] => {}
    | pattern :: patterns, bounds :: intervals =>
        (inspect view pattern bounds).append (inspectMany view patterns intervals)
    | patterns, intervals =>
        { arityProblems := [(patterns, intervals)] }
  termination_by patterns _ => sizeOf patterns
end

/-- List-length mismatch is tracked separately even when no interval exists to
attach a diagnostic to. The caller retains the entire patterns/intervals pair. -/
def Finished (patterns : List Query) (intervals : List (Bounds state)) (report : Report state) : Prop :=
  patterns.length = intervals.length ∧ report.blocked = [] ∧
    report.conflicts = [] ∧ report.arityProblems = []

def NeedsK2 (view : Snapshot state) (report : Report state) : Prop :=
  ∃ visit ∈ report.inspected, GeneralSourceK2.Complete view visit.bounds.1 ∧
    GeneralSourceBoundary.GraphK2 view.graph visit.bounds.1

theorem inspection_recurrence (view : Snapshot state) (report : Report state)
    (recursive : NeedsK2 view report) :
    ∃ visit ∈ report.inspected, GeneralSourceK2.Complete view visit.bounds.1 ∧
      GeneralSourceK2.RecursAt view visit.bounds.1 := by
  obtain ⟨visit, member, complete, cycle⟩ := recursive
  exact ⟨visit, member, complete, GeneralSourceK2.graphK2_sound view _ cycle⟩

theorem append_preserves_inspections (first last : Report state) (visit : Visit state) :
    visit ∈ (first.append last).inspected ↔
      visit ∈ first.inspected ∨ visit ∈ last.inspected := List.mem_append

theorem append_preserves_blockers (first last : Report state) (issue : Visit state × Reason) :
    issue ∈ (first.append last).blocked ↔
      issue ∈ first.blocked ∨ issue ∈ last.blocked := List.mem_append

theorem variable_does_not_inspect (view : Snapshot state) (names : List Nat) (bounds : Bounds state) :
    (inspect view (.variables names) bounds).inspected = [] ∧
      (inspect view (.variables names) bounds).captures = names.map (fun name => (name, bounds)) :=
  by simp [inspect]

theorem unresolved_constructor_defers (view : Snapshot state) (shape : Shape)
    (children : List Query) (bounds : Bounds state)
    (reason : GeneralNormalizedObservation.Deferred state.slots)
    (unknown : view.heads bounds.1 = .deferred reason) :
    (inspect view (.node shape children) bounds).blocked ≠ [] := by
  simp [inspect, unknown, Report.visit, blocked]

theorem untranslated_application_defers (view : Snapshot state) (primitives : Primitives) (constructor : Nat)
    (arguments : List Pattern) (bounds : Bounds state) (unknown : primitives constructor = none) :
    (inspect view (translate primitives (.app constructor arguments)) bounds).blocked ≠ [] := by
  simp [translate, unknown, inspect, blocked]

theorem merged_plain_payload (primitives : Primitives) (first last : Nat) (tag : Nat) :
    translate primitives (.variant tag (.join (.var first) (.var last))) =
      .node (.variant tag) [.variables [first, last]] := by simp [translate, plainNames]

end Yulang.GeneralCandidateInspection
