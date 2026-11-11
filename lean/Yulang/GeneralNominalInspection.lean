import Yulang.GeneralNominalAllocation
import Yulang.GeneralCandidateInspection

/-! Constructor inspection uses resolved nominal names and existing normalized
structural heads. The finite pattern bounds descent. Uninterpreted names,
row-pattern applications, non-point parameter descriptors, distinct nominal endpoint observations and unresolved
positions are retained as blockers. Nominal bodies are never inspected. -/
namespace Yulang.GeneralNominalInspection

open GeneralDeclarationPatterns (Pattern Constructors)
open GeneralCandidateInspection (Primitives PrimitivesCompatible Primitive)
open GeneralNormalizedObservation (Shape)
open GeneralNominalState (State)

/-- Source name metadata distinguishes primitive constructors from invariant
nominal applications. Variance/layout cases outside this interpretation defer. -/
structure Interpretation where
  primitives : Primitives
  invariantNominal : Nat → Bool
  disjoint : ∀ name, invariantNominal name = true → primitives name = none

inductive Query where
  | variables (names : List Nat)
  | scalar (base : Inference.Base)
  | node (shape : Shape) (children : List Query)
  | nominal (name : Nat) (children : List Query)
  | deferred (source : Pattern)

mutual
  def translate (constructors : Constructors) (interpretation : Interpretation) : Pattern → Query
    | .var name => .variables [name]
    | .variant tag payload => .node (.variant tag)
        [match GeneralCandidateInspection.plainNames payload with
         | some names => .variables names
         | none => translate constructors interpretation payload]
    | .app key arguments =>
        match interpretation.primitives key, arguments with
        | some (.scalar base), [] => .scalar base
        | some .emptyRecord, [] => .node (.record []) []
        | some .exactEmpty, [] => .node .exactEmpty []
        | some .pair, [first,last] => .node .pair
            [translate constructors interpretation first, translate constructors interpretation last]
        | _, actuals => match constructors key with
          | some declaration =>
              if interpretation.invariantNominal key &&
                declaration.parameters.all (· == .type) &&
                (declaration.parameters.length == actuals.length) then
                .nominal declaration.name (actuals.attach.map fun argument => translate constructors interpretation argument.val)
              else .deferred (.app key actuals)
          | none => .deferred (.app key actuals)
    | .record label payload tail =>
        match translate constructors interpretation tail with
        | .node (.record labels) children =>
            let fields := ((label, translate constructors interpretation payload) :: labels.zip children).mergeSort
              (fun first last => first.1 ≤ last.1)
            .node (.record (fields.map Prod.fst)) (fields.map Prod.snd)
        | _ => .deferred (.record label payload tail)
    | other => .deferred other
  termination_by pattern => sizeOf pattern
  decreasing_by
    all_goals simp_all [wfParam]
    all_goals first
      | omega
      | have bound := List.sizeOf_lt_of_mem argument.property
        simp only [wfParam] at bound
        omega
end

def queries (state : State) (interpretation : Interpretation) (declaration : GeneralDeclarations.Declaration) : List Query :=
  declaration.normalHead.map (translate state.constructors interpretation)

abbrev Bounds (state : State) := Fin state.base.slots × Fin state.base.slots

structure Report (state : State) where
  captures : List (Nat × Bounds state) := []
  inspected : List (Bounds state) := []
  blocked : List (Bounds state) := []
  conflicts : List (Bounds state) := []
  arity : List (Nat × Nat) := []

def Report.append (first last : Report state) : Report state :=
  ⟨first.captures ++ last.captures, first.inspected ++ last.inspected,
    first.blocked ++ last.blocked, first.conflicts ++ last.conflicts, first.arity ++ last.arity⟩

def Report.visit (bounds : Bounds state) (report : Report state) : Report state :=
  { report with inspected := bounds :: report.inspected }

def block (bounds : Bounds state) : Report state := { blocked := [bounds] }

def typeArguments (arguments : List (GeneralNominalState.Parameter slots)) :
    Option (List (Fin slots × Fin slots)) :=
  arguments.mapM fun argument => match argument with
    | .type bounds => if bounds.1 = bounds.2 then some bounds else none
    | .row _ => none

mutual
  def inspect (state : State) (query : Query) (bounds : Bounds state) : Report state :=
    match query with
    | .variables names => { captures := names.map fun name => (name,bounds) }
    | .deferred _ => block bounds
    | .nominal expected patterns => Report.visit bounds <|
        match state.nominals bounds.1 with
        | some descriptor =>
            if descriptor.declaration.name = expected then
              if bounds.1 = bounds.2 then
                match typeArguments descriptor.arguments with
                | some arguments => inspectMany state patterns arguments
                | none => block bounds
              else block bounds
            else { conflicts := [bounds] }
        | none => match state.view.heads bounds.1 with
          | .scalar _ => { conflicts := [bounds] }
          | _ => block bounds
    | .scalar expected => Report.visit bounds <|
        match state.nominals bounds.1 with
        | some _ => { conflicts := [bounds] }
        | none => match state.view.heads bounds.1 with
          | .scalar actual => if expected = actual then
              match state.view.heads bounds.2 with
              | .scalar upper => if expected = upper then {} else block bounds
              | _ => block bounds
            else { conflicts := [bounds] }
          | _ => block bounds
    | .node expected patterns => Report.visit bounds <|
        match state.view.heads bounds.1 with
        | .structural lower children =>
            if state.view.shapes lower = expected then
              match state.view.heads bounds.2 with
              | .structural upper targets =>
                  if state.view.shapes upper = expected then
                    inspectMany state patterns ((List.ofFn children).zip (List.ofFn targets))
                  else block bounds
              | _ => block bounds
            else block bounds
        | _ => block bounds
  termination_by sizeOf query

  def inspectMany (state : State) : List Query → List (Bounds state) → Report state
    | [], [] => {}
    | pattern :: patterns, bounds :: intervals =>
        (inspect state pattern bounds).append (inspectMany state patterns intervals)
    | patterns, intervals => { arity := [(patterns.length, intervals.length)] }
  termination_by patterns _ => sizeOf patterns
end

def Finished (report : Report state) : Prop :=
  report.blocked = [] ∧ report.conflicts = [] ∧ report.arity = []

def bindings (state : State) (report : Report state) : GeneralNominalAllocation.Bindings :=
  report.captures.map fun binding =>
    (binding.1, state.base.source binding.2.1, state.base.source binding.2.2)

def explicitSuccessors (state : State) (slot : Fin state.base.slots) : List (Fin state.base.slots) :=
  CommonRoleRegularGraph.successors state.view.graph slot ++
    match state.nominals slot with
    | none => []
    | some descriptor => descriptor.arguments.flatMap fun parameter => match parameter with
      | .type bounds => if bounds.1 = bounds.2 then [bounds.1] else []
      | .row _ => []

/-- Known observations include opaque nominal heads, without their bodies. -/
def observable (state : State) (slot : Fin state.base.slots) : Bool :=
  (state.nominals slot).isSome || (match state.view.heads slot with
    | .deferred _ => false
    | _ => true)

/-- Every reached explicit observation must be known; cycles through a
nominal parameter position remain unsupported even below the starting root.
Pure structural cycles are handled by the existing normalized K2 relation. -/
def NominalSupported (state : State) (slot : Fin state.base.slots) : Prop :=
  ∀ reached ∈ FiniteWorklist.reachable (explicitSuccessors state) state.base.slots slot,
    observable state reached = true ∧
      ((state.nominals reached).isSome = true →
        ∀ child ∈ explicitSuccessors state reached,
          reached ∉ FiniteWorklist.reachable (explicitSuccessors state) state.base.slots child)

/-- Structural recurrence evidence must be complete at every inspected
anonymous position. Nominal heads are opaque; their explicitly entered
arguments are checked separately. Incomplete cones remain deferred. -/
def Covered (state : State) (report : Report state) : Prop :=
  ∀ bounds ∈ report.inspected,
    (∃ descriptor, state.nominals bounds.1 = some descriptor ∧ NominalSupported state bounds.1) ∨ GeneralSourceK2.Complete state.view bounds.1

def NeedsK2 (state : State) (report : Report state) : Prop :=
  ∃ bounds ∈ report.inspected, GeneralNominalState.AtK2 state bounds.1

theorem inspected_recurrence (state : State) (report : Report state) (cycle : NeedsK2 state report) :
    ∃ bounds ∈ report.inspected, GeneralSourceK2.RecursAt state.view bounds.1 := by
  obtain ⟨bounds, member, recursive⟩ := cycle
  exact ⟨bounds, member, GeneralNominalState.atK2_recurrence state _ recursive⟩

theorem variables_capture_intervals (state : State) (names : List Nat) (bounds : Bounds state) :
    inspect state (.variables names) bounds = { captures := names.map fun name => (name,bounds) } := by
  simp [inspect]

theorem unknown_defers (state : State) (name : Nat) (patterns : List Query) (bounds : Bounds state)
    (nominal : state.nominals bounds.1 = none)
    (unknown : state.view.heads bounds.1 = .deferred .unresolved) :
    (inspect state (.nominal name patterns) bounds).blocked ≠ [] := by
  simp [inspect, nominal, unknown, Report.visit, block]

theorem nominal_bodies_opaque (state : State) (expected : Nat) (patterns : List Query)
    (slot : Fin state.base.slots) (descriptor : GeneralNominalState.Descriptor state.base.slots)
    (recorded : state.nominals slot = some descriptor) (name : descriptor.declaration.name = expected)
    (arguments : List (Bounds state)) (types : typeArguments descriptor.arguments = some arguments) :
    inspect state (.nominal expected patterns) (slot,slot) =
      (inspectMany state patterns arguments).visit (slot,slot) := by
  simp [inspect, recorded, name, types]

end Yulang.GeneralNominalInspection
