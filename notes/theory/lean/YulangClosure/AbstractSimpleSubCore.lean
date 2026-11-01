import YulangClosure.SimpleSubLatticeGrowingInference

/-!
R212 partial endogenous-core construction. This file does not define or prove
the R211 complete core. In particular there is no CoreAccepted/CoreReadout,
solver step, or whole-run theorem. The unresolved readout construction is
recorded at the end and in the exact R212 handoff.

The finite input records below contain data rather than successful histories,
preservation laws, terminal certificates, or a proposed type interpretation.
Source Values, their immutable births and references are separate from flexible
type coordinates. Source generation of these inputs is not proved here.

Authority: top-level inference principles sections 1--3; occurrence association;
the 2026-10-24 birth-level correction sections 2--4; R212 and the primary's
finite-graph-input clarification. Term/Constraint retain the pinned structural
algebra, with both kinds, all four Function ports and row metadata unchanged.
-/
namespace YulangClosure.SimpleSub.AbstractCore

/-- A concrete finite source-Value graph, without a type-coordinate decoder. -/
structure CoreValueGraph where
  births : List Nat
  references : List (Nat × Nat)

def CoreValueGraph.valid (graph : CoreValueGraph) : Bool :=
  graph.references.all (fun edge =>
    decide (edge.1 < graph.births.length) && decide (edge.2 < graph.births.length))

/-- Intrusion must use this actual adjacency, never subtype direction. -/
def CoreValueGraph.reference (graph : CoreValueGraph) (origin receiver : Nat) : Prop :=
  (origin, receiver) ∈ graph.references

/-- The table is immutable; callers must separately establish that the Value
exists. A total lookup does not make an out-of-range vertex part of the graph. -/
def CoreValueGraph.birth (graph : CoreValueGraph) (value : Nat) : Nat :=
  (graph.births[value]?).getD 0

/-- Input-demand endpoints precede extrusion; actual copies are created only
by the not-yet-constructed extrusion transition. -/
structure CoreDemand where
  clause : Constraint
  origin : Nat
  receiver : Nat

structure CorePublicationRequest where
  identity : Nat
  afterConstraint : Nat
  boundary : Nat
  roots : List ScopedPublication.Row

structure CoreUseRequest where
  identity : Nat
  afterConstraint : Nat
  publication : Nat
  atLevel : Nat

/-- Finite abstract input. No graph interpretation, reference assignment,
terminal proof table, run, or lawfulness certificate is an input field. -/
structure CoreProblem where
  demands : List CoreDemand
  valueGraph : CoreValueGraph
  valueLevels : List Nat
  effectLevels : List Nat
  publications : List CorePublicationRequest
  uses : List CoreUseRequest

def CoreProblem.originalConstraints (problem : CoreProblem) : Store :=
  problem.demands.map CoreDemand.clause

def CoreProblem.levels (problem : CoreProblem) : (kind : Kind) → List Nat
  | .value => problem.valueLevels
  | .effect => problem.effectLevels

def CoreProblem.allocated (problem : CoreProblem) (kind : Kind) : Nat :=
  (problem.levels kind).length

/-- Variable occurrence enumeration is the existing exact structural traversal.
This check does not classify complete source Call/effect evidence. -/
def CoreProblem.termAllocated (problem : CoreProblem) {kind : Kind}
    (term : Term kind) : Bool :=
  (ScopedPublication.vars term).all (fun row =>
    decide (row.index < problem.allocated row.kind))

def CoreProblem.demandValid (problem : CoreProblem) (demand : CoreDemand) : Bool :=
  decide (demand.origin < problem.valueGraph.births.length) &&
  decide (demand.receiver < problem.valueGraph.births.length) &&
  problem.termAllocated demand.clause.lower && problem.termAllocated demand.clause.upper

def CoreProblem.inputValid (problem : CoreProblem) : Bool :=
  problem.valueGraph.valid && problem.demands.all problem.demandValid

/-- A mutable solver coordinate is not a source Value or a regular solution
node. Both retained bound sides and current metadata belong to this coordinate. -/
structure CoreRow (kind : Kind) where
  level : Nat
  nonGeneric : Bool
  lowerBounds : List (Term kind)
  upperBounds : List (Term kind)

def CoreRow.initial (kind : Kind) (level : Nat) : CoreRow kind :=
  ⟨level, false, [], []⟩

structure CorePublication where
  identity : Nat
  boundary : Nat
  roots : List ScopedPublication.Row
  capturedValueRows : List Nat
  capturedEffectRows : List Nat

structure CoreUse where
  identity : Nat
  publication : Nat
  valueCopies : List (Nat × Nat)
  effectCopies : List (Nat × Nat)

inductive CoreStatus where
  | active
  | invalidInput
  | failed
  | finished
  deriving DecidableEq, Repr

/-- Candidate storage for an endogenous solver. It contains no Step/History
field and no semantic-preservation premise. The future readout must be built
from these bounds, copies and equality state, not supplied to this record. -/
structure CoreState where
  pending : List CoreDemand
  retainedConstraints : Store
  valueRows : List (CoreRow .value)
  effectRows : List (CoreRow .effect)
  valueRepresentatives : List Nat
  effectRepresentatives : List Nat
  termGraph : Lattice.Graph
  occurrences : List Occurrence
  nextOccurrence : Nat
  publications : List CorePublication
  uses : List CoreUse
  status : CoreStatus

/-- Computed initial allocation and queue, with no initial successful history
or terminal interpretation. This is only the initialized storage portion of
Stage A; no claim is made that it already determines a complete algorithm. -/
def CoreProblem.initial (problem : CoreProblem) : CoreState where
  pending := problem.demands
  retainedConstraints := problem.originalConstraints
  valueRows := problem.valueLevels.map (CoreRow.initial .value)
  effectRows := problem.effectLevels.map (CoreRow.initial .effect)
  valueRepresentatives := List.range problem.valueLevels.length
  effectRepresentatives := List.range problem.effectLevels.length
  termGraph := fun _ => []
  occurrences := []
  nextOccurrence := 0
  publications := []
  uses := []
  status := if problem.inputValid then .active else .invalidInput

def CoreState.rows (state : CoreState) : (kind : Kind) → List (CoreRow kind)
  | .value => state.valueRows
  | .effect => state.effectRows

def CoreState.representatives (state : CoreState) : Kind → List Nat
  | .value => state.valueRepresentatives
  | .effect => state.effectRepresentatives

def CoreState.withRows (state : CoreState) : (kind : Kind) →
    List (CoreRow kind) → CoreState
  | .value, rows => { state with valueRows := rows }
  | .effect, rows => { state with effectRows := rows }

/-- The directly selected same-level variable-upper-bound operation, including
opposite-bound replay. Wrong-level demands return none here: this is a partial
operation, not a substitute for the missing full step/extrusion relation. -/
def CoreState.insertPendingUpper (state : CoreState) : Option CoreState := do
  let demand :: rest := state.pending | none
  let .var identity := demand.clause.lower | none
  let representative ← (state.representatives demand.clause.kind)[identity]?
  let row ← (state.rows demand.clause.kind)[representative]?
  let low := (ScopedPublication.vars demand.clause.upper).all (fun dependency =>
    match (state.rows dependency.kind)[dependency.index]? with
    | none => false
    | some target => decide (target.level ≤ row.level))
  if !low then none else
    let row' := { row with upperBounds := demand.clause.upper :: row.upperBounds }
    let next := state.withRows demand.clause.kind
      ((state.rows demand.clause.kind).set representative row')
    let replay := row.lowerBounds.map (fun lower =>
      { demand with clause := ⟨demand.clause.kind, lower, demand.clause.upper⟩ })
    pure { next with pending := replay ++ rest }

/-- Recursive output syntax uses actual (kind,row,polarity) binder identity.
Free row names and recursive occurrences are distinct constructors. This is
ordinary paper coalescing syntax, not a definition of typing or safety. -/
inductive CoreCoalesced : Kind → Type where
  | free {kind} (identity : Nat) : CoreCoalesced kind
  | bound {kind} (identity : Nat) (polarity : Polarity) : CoreCoalesced kind
  | recursive {kind} (identity : Nat) (polarity : Polarity)
      (body : CoreCoalesced kind) : CoreCoalesced kind
  | atom {kind} (identity : Nat) : CoreCoalesced kind
  | bottom {kind} : CoreCoalesced kind
  | top {kind} : CoreCoalesced kind
  | union {kind} (left right : CoreCoalesced kind) : CoreCoalesced kind
  | intersection {kind} (left right : CoreCoalesced kind) : CoreCoalesced kind
  | function (argument : CoreCoalesced .value)
      (argumentEffect resultEffect : CoreCoalesced .effect)
      (result : CoreCoalesced .value) : CoreCoalesced .value
  | recordNil : CoreCoalesced .value
  | recordCons (label : Nat) (optional : Bool)
      (field tail : CoreCoalesced .value) : CoreCoalesced .value
  | tupleNil : CoreCoalesced .value
  | tupleCons (head tail : CoreCoalesced .value) : CoreCoalesced .value
  | variantNil : CoreCoalesced .value
  | variantCons (tag : Nat) (payloads tail : CoreCoalesced .value) : CoreCoalesced .value
  deriving Repr

structure CorePolarRow where
  kind : Kind
  identity : Nat
  polarity : Polarity
  deriving DecidableEq, Repr

inductive CoreCoalescingMode where
  | ordinary
  | unifying
  deriving DecidableEq, Repr

/-- Fuel counts row expansions, not structural depth. A recursive row hit is
returned as a bound occurrence; missing coordinates or exhausted fuel return
none. Fuel sufficiency on reachable states is still an unproved obligation.

Ordinary mode is paper Fig. 11. Unifying mode uses Fig. 12's distinct seeds:
negative rows start at top; positive rows include the negative coalescing,
then accumulate lower bounds. No equality of the polar results is assumed. -/
def coreCoalesce (mode : CoreCoalescingMode) (state : CoreState)
    (fuel : Nat) (polarity : Polarity) (seen : List CorePolarRow)
    {kind : Kind} (term : Term kind) : Option (CoreCoalesced kind) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    let rec visit (polarity : Polarity) {kind : Kind} (subterm : Term kind) :
        Option (CoreCoalesced kind) := match subterm with
      | .var identity => do
          let identity ← (state.representatives kind)[identity]?
          let key : CorePolarRow := ⟨kind, identity, polarity⟩
          if key ∈ seen then pure (.bound identity polarity) else
            let row ← (state.rows kind)[identity]?
            let seed : CoreCoalesced kind ← match mode, polarity with
              | .ordinary, _ => pure (.free identity)
              | .unifying, .negative => pure .top
              | .unifying, .positive =>
                  coreCoalesce mode state fuel .negative (key :: seen) (.var identity)
            let bounds : List (Term kind) := match polarity with
              | .positive => row.lowerBounds
              | .negative => row.upperBounds
            let body ← bounds.foldlM (fun accumulated bound => do
              let next ← coreCoalesce mode state fuel polarity (key :: seen) bound
              pure (match polarity with
                | .positive => .union accumulated next
                | .negative => .intersection accumulated next)) seed
            pure (.recursive identity polarity body)
      | .atom identity => pure (.atom identity)
      | .bottom => pure .bottom
      | .top => pure .top
      | .union left right => do pure (.union (← visit polarity left) (← visit polarity right))
      | .intersection left right =>
          do pure (.intersection (← visit polarity left) (← visit polarity right))
      | .function argument argumentEffect resultEffect result => do
          pure (.function
            (← visit polarity.flip argument)
            (← visit polarity.flip argumentEffect)
            (← visit polarity resultEffect) (← visit polarity result))
      | .recordNil => pure .recordNil
      | .recordCons label optional field tail =>
          do pure (.recordCons label optional (← visit polarity field) (← visit polarity tail))
      | .tupleNil => pure .tupleNil
      | .tupleCons head tail => do pure (.tupleCons (← visit polarity head) (← visit polarity tail))
      | .variantNil => pure .variantNil
      | .variantCons tag payloads tail =>
          do pure (.variantCons tag (← visit polarity payloads) (← visit polarity tail))
    termination_by (fuel, sizeOf subterm + 1)
    visit polarity term
termination_by (fuel, 0)

def CoreState.coalesce (mode : CoreCoalescingMode) (state : CoreState)
    (polarity : Polarity) {kind : Kind} (term : Term kind) : Option (CoreCoalesced kind) :=
  coreCoalesce mode state (2 * (state.valueRows.length + state.effectRows.length) + 1)
    polarity [] term

/- A concrete computed upper-bound discriminator. It is an actual initial
queue plus one selected insertion/replay operation, not an accepted R211 run.
The missing full CoreAccepted relation must not be inferred from this fixture. -/
def upperOnlyProblem : CoreProblem where
  demands := [⟨⟨.value, .var 0, .atom 0⟩, 0, 0⟩]
  valueGraph := ⟨[0], []⟩
  valueLevels := [0]
  effectLevels := []
  publications := []
  uses := []

def upperOnlyAfter : Option CoreState := upperOnlyProblem.initial.insertPendingUpper

/-- Acyclic diagnostic projection only. A real recursive occurrence returns
none; this is deliberately not the missing regular readout compiler. -/
def CoreCoalesced.toTerm {kind : Kind} : CoreCoalesced kind → Option (Term kind)
  | .free identity => pure (.var identity)
  | .bound _ _ => none
  | .recursive _ _ body => body.toTerm
  | .atom identity => pure (.atom identity)
  | .bottom => pure .bottom
  | .top => pure .top
  | .union left right => do pure (.union (← left.toTerm) (← right.toTerm))
  | .intersection left right => do pure (.intersection (← left.toTerm) (← right.toTerm))
  | .function argument argumentEffect resultEffect result => do
      pure (.function (← argument.toTerm) (← argumentEffect.toTerm)
        (← resultEffect.toTerm) (← result.toTerm))
  | .recordNil => pure .recordNil
  | .recordCons label optional field tail =>
      do pure (.recordCons label optional (← field.toTerm) (← tail.toTerm))
  | .tupleNil => pure .tupleNil
  | .tupleCons head tail => do pure (.tupleCons (← head.toTerm) (← tail.toTerm))
  | .variantNil => pure .variantNil
  | .variantCons tag payloads tail =>
      do pure (.variantCons tag (← payloads.toTerm) (← tail.toTerm))

def upperOnlyProjection (mode : CoreCoalescingMode) (polarity : Polarity) :
    Option (Term .value) := do
  let state ← upperOnlyAfter
  let result ← state.coalesce mode polarity (Term.var 0)
  result.toTerm

/-- A checked finite discriminator, not the R211 whole-run theorem. Ordinary
polar outputs stay different; the unifying equation supplies one value here. -/
theorem upper_only_polar_equations :
    upperOnlyProjection .ordinary .positive = some (.var 0) ∧
    upperOnlyProjection .ordinary .negative = some (.intersection (.var 0) (.atom 0)) ∧
    upperOnlyProjection .unifying .positive = some (.intersection .top (.atom 0)) ∧
    upperOnlyProjection .unifying .negative = some (.intersection .top (.atom 0)) := by
  simp [upperOnlyProjection, upperOnlyAfter, upperOnlyProblem,
    CoreProblem.initial, CoreState.insertPendingUpper, CoreState.withRows,
    CoreState.rows, CoreState.representatives, CoreState.coalesce,
    CoreRow.initial, ScopedPublication.vars,
    coreCoalesce, coreCoalesce.visit, CoreCoalesced.toTerm]

def upperOnlyValuation : Valuation := fun kind identity =>
  match kind with
  | .value => if identity = 0 then .intersection .top (.atom 0) else .var identity
  | .effect => .var identity

theorem upper_only_shared_satisfies :
    upperOnlyProblem.originalConstraints.Satisfied upperOnlyValuation := by
  intro clause member
  have same : clause = ⟨.value, .var 0, .atom 0⟩ := by
    simpa [CoreProblem.originalConstraints, upperOnlyProblem] using member
  subst clause
  exact Sub.intersectionRight _ _

/-- Each structural constructor is exercised in a single finite input. This
contains no row variables, so it tests traversal shape, labels and optional
metadata; it does not test the open bound-to-shared-model theorem. -/
def allConstructorsTerm : Term .value :=
  .union (.intersection .bottom .top)
    (.function
      (.recordCons 7 true (.tupleCons (.atom 2) .tupleNil) .recordNil)
      (.union (Term.bottom (k := .effect)) (.atom 3))
      (.intersection (Term.top (k := .effect)) (.atom 4))
      (.variantCons 9 (.tupleCons (.atom 5) .tupleNil) .variantNil))

def emptyProblem : CoreProblem := ⟨[], ⟨[], []⟩, [], [], [], []⟩

theorem all_constructors_acyclic_projection :
    ((emptyProblem.initial.coalesce .ordinary .positive allConstructorsTerm).bind
      CoreCoalesced.toTerm) = some allConstructorsTerm ∧
    ((emptyProblem.initial.coalesce .unifying .negative allConstructorsTerm).bind
      CoreCoalesced.toTerm) = some allConstructorsTerm := by
  simp [emptyProblem, allConstructorsTerm, CoreProblem.initial,
    CoreState.coalesce, coreCoalesce, coreCoalesce.visit, CoreCoalesced.toTerm,
    Polarity.flip]

def portProblem : CoreProblem where
  demands := [⟨⟨.value, .var 0, .atom 0⟩, 0, 0⟩,
    ⟨⟨.effect, .var 0, .atom 1⟩, 0, 0⟩]
  valueGraph := ⟨[0], []⟩
  valueLevels := [0]
  effectLevels := [0]
  publications := []
  uses := []

def portProjection (polarity : Polarity) : Option (Term .value) := do
  let first ← portProblem.initial.insertPendingUpper
  let second ← first.insertPendingUpper
  let result ← second.coalesce .ordinary polarity
    (.function (.var 0) (.var 0) (.var 0) (.var 0))
  result.toTerm

theorem four_port_variance :
    portProjection .positive = some (.function
      (.intersection (.var 0) (.atom 0))
      (.intersection (.var 0) (.atom 1)) (.var 0) (.var 0)) ∧
    portProjection .negative = some (.function (.var 0) (.var 0)
      (.intersection (.var 0) (.atom 1)) (.intersection (.var 0) (.atom 0))) := by
  simp [portProjection, portProblem, CoreProblem.initial,
    CoreState.insertPendingUpper, CoreState.withRows, CoreState.rows,
    CoreState.representatives, CoreState.coalesce, CoreRow.initial,
    ScopedPublication.vars, coreCoalesce, coreCoalesce.visit,
    CoreCoalesced.toTerm, Polarity.flip]

/-- A computed finite counterinterpretation to treating the ordinary free
name as an arbitrary common solution. Node 0 is Int; node 1 is a distinct
atom Bool; node 2 is Bool & Int. This is not a counterexample to R211. -/
def ordinaryFreeGraph : Lattice.Graph
  | .value => [.structural (.atom 0), .structural (.atom 1), .intersection 1 0]
  | .effect => []

theorem ordinary_readout_not_uniform :
    ¬ Lattice.RegularSub ordinaryFreeGraph ⟨.value, 1, 2⟩ := by
  intro related
  have valid : ordinaryFreeGraph.Valid :=
    (Lattice.checkGraph_iff ordinaryFreeGraph).mp (by decide)
  have accepted := (LatticeDecision.decideDemands_exact ordinaryFreeGraph
    [⟨.value, 1, 2⟩]).mpr ⟨valid, by decide, by
      intro pair member
      have same : pair = ⟨.value, 1, 2⟩ := by simpa using member
      subst pair
      exact related⟩
  have rejected : LatticeDecision.decideDemands ordinaryFreeGraph [⟨.value, 1, 2⟩] = false := by
    decide
  rw [rejected] at accepted
  cases accepted

/- The independent Int/Bool client discriminator cannot yet be promoted to an
endogenous use trace. CoreUse can store two maps [(template,rowInt)] and
[(template,rowBool)] with one publication origin, and the bound tables can keep
these rows distinct. But CoreProblem.demands currently names flat row IDs.
It does not yet translate each preallocated ORIGINAL use-coordinate to the
actual fresh row allocated by that use. Allocating those instance rows in the
initial table would only provide distinct inputs, not prove that publication
and fresh use create and preserve them. No such hand-written maps are used.

First unsupported generalization equation:

  resolveOriginalUse (performUse state publication use) use template
    = actualFreshRowAllocatedForThatUse state publication use template

with one memo/map within the use, disjoint maps across independent uses, and
fixed/captured/non-generic rows shared according to the original guards. This
must be derived from the transition, including both copied bound sides. Neither
the polar syntax above nor the supplied-metadata publication lemmas prove it.
-/

/-
FIRST OPEN CONSTRUCTION, not a theorem or a semantic definition:

  buildReadout : CoreState → Option (Lattice.Graph × LatticeInference.References)

The graph/reference pair must be computed from actual flexible-row bounds and
equality state and support all original constraints under one interpretation.
The pinned Completion.completeStore only completes constructor nodes relative
to an already supplied graph/reference map; it does not construct that map
from mutable lower/upper bounds. Likewise GrowingHistory.graph growth does not
update existing flexible variables, whose representation it does not define.

Fig. 11 ordinary coalescing is polarity-indexed. It cannot simply be used as
one substitution: for the consistent store with just x <: atom(0), ordinary
positive coalescing of x contains the still-free x, whereas negative coalescing
uses its upper bound. Fig. 12 unifying coalescing is the relevant paper route;
its finite shared regular-graph realization (including bound-only cycles),
consistency argument, and transport across extrusion/intrusion/publication
remain to be constructed here. No impossibility result is asserted.

No CoreAccepted, CoreReadout, CoreRun or whole-run soundness declaration is
defined until that concrete construction and the actual step relation exist.
In particular acceptance is not defined by checking the requested conclusion,
and the requested theorem has not been moved into an assumption.
-/

end YulangClosure.SimpleSub.AbstractCore

#check @YulangClosure.SimpleSub.AbstractCore.CoreProblem.initial
#check @YulangClosure.SimpleSub.AbstractCore.CoreState.insertPendingUpper
#check @YulangClosure.SimpleSub.AbstractCore.coreCoalesce
#check @YulangClosure.SimpleSub.AbstractCore.CoreState.coalesce
#check @YulangClosure.SimpleSub.AbstractCore.upper_only_polar_equations
#print axioms YulangClosure.SimpleSub.AbstractCore.upper_only_polar_equations
#check @YulangClosure.SimpleSub.AbstractCore.upper_only_shared_satisfies
#print axioms YulangClosure.SimpleSub.AbstractCore.upper_only_shared_satisfies
#check @YulangClosure.SimpleSub.AbstractCore.all_constructors_acyclic_projection
#print axioms YulangClosure.SimpleSub.AbstractCore.all_constructors_acyclic_projection
#check @YulangClosure.SimpleSub.AbstractCore.four_port_variance
#print axioms YulangClosure.SimpleSub.AbstractCore.four_port_variance
#check @YulangClosure.SimpleSub.AbstractCore.ordinary_readout_not_uniform
#print axioms YulangClosure.SimpleSub.AbstractCore.ordinary_readout_not_uniform
