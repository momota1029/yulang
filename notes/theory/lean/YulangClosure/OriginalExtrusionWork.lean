import YulangClosure.OriginalInferenceTerminationResolution

/-!
Operation-local Work construction from candidate_extrusion.rs. The local
machine represents actual row ordinals and explicit raw term labels, both row kinds, early row memo,
selected old-vector bounds, all eight Work variants and exact Function ports.
Native allocation/admission outcomes are explicit gates. The term-label stream
is an allocator readout boundary, not a dense-index model or proved extraction
from the branded page arena. Scoped evidence and
fiber publication are outside this projection: Bound returns an exact request
to that owner, never a fabricated fiber or successful whole-drain certificate.
The finite prefix evaluator below is not a termination argument or solver fuel.
-/
namespace YulangClosure.OriginalExtrusionWork

open NativeValuePorts (ValueEndpoint FunctionTerms)
open NativeValueStructure (Request TermView)
open NativeMergeExpansion (Polarity)
open OriginalInferenceTerminationResolution (Cell Row)

inductive Endpoint where
  | value (endpoint : ValueEndpoint)
  | effect (endpoint : NativeMergeExpansion.Endpoint)
  deriving DecidableEq, Repr

def opposite : Polarity → Polarity
  | .positive => .negative
  | .negative => .positive

structure CopyKey where
  endpoint : Endpoint
  polarity : Polarity
  target : Nat
  deriving DecidableEq, Repr

structure RawBound where
  owner : Endpoint
  polarity : Polarity
  endpoint : Endpoint
  deriving DecidableEq, Repr

def RawBound.decode : RawBound → Option OriginalInferenceTerminationResolution.Bound
  | ⟨.value (.row owner), p, .value item⟩ =>
      some (.value ⟨owner, match p with | .positive => .positive | .negative => .negative, item⟩)
  | ⟨.effect (.row owner), p, .effect item⟩ => some (.effect ⟨owner, p, item⟩)
  | _ => none

structure Operation where
  initial : Endpoint
  polarity : Polarity
  target : Nat
  occurrence : Nat
  processing : Option Nat
  caller : Request
  sources : Option Nat
  qualified : Bool

structure BoundRequest where
  original : RawBound
  insertion : RawBound
  destination : RawBound
  operation : Operation
  capture : Bool := true

inductive Work where
  | visit (key : CopyKey)
  | function (key : CopyKey) (children : List CopyKey) (originals : FunctionTerms)
  | tuple (key : CopyKey) (start len : Nat)
  | record (key : CopyKey) (start len : Nat)
  | variant (key : CopyKey) (start len : Nat)
  | effectView (key : CopyKey) (view : Nat) (child : CopyKey)
  | bound (owner : Endpoint) (polarity : Polarity) (child : CopyKey) (source : RawBound)
  | incomingAllowance (tail view : Nat) (source : CopyKey) (original : RawBound)
  deriving DecidableEq, Repr

structure Bounds (Atom : Type) where
  level : Nat
  lowerRows : List Nat := []
  upperRows : List Nat := []
  lowerAtoms : List Atom := []
  upperAtoms : List Atom := []
  deriving DecidableEq, Repr

/-- Live-variable polarity belongs to the physical term key. `none` denotes
an existing component/atom/structural cell, so opposite live row terms do not
accidentally intern together. All Function children remain actual term IDs. -/
structure StoredCell where
  cell : Cell
  livePolarity : Option Polarity := none
  deriving DecidableEq, Repr

structure Parent where
  copy : Endpoint
  parent : Endpoint
  polarity : Polarity
  target : Nat
  operation : Operation

structure Capture where
  source : Nat
  view : Nat
  deriving DecidableEq, Repr

abbrev Memo := CopyKey → Option Endpoint

def memoPut (memo : Memo) (key : CopyKey) (endpoint : Endpoint) : Memo :=
  fun query => if query = key then some endpoint else memo query

structure State where
  operation : Operation
  qv : Nat → Nat := id
  qe : Nat → Nat := id
  values : List (Bounds ValueEndpoint) := []
  effects : List (Bounds NativeMergeExpansion.Endpoint) := []
  /-- Raw labels in one fixed lineage; allocation chronology is separate. -/
  terms : List (Nat × StoredCell) := []
  termLabel : Nat → Nat := id
  termAllocations : Nat := 0
  views : Nat → Option (Option Nat) := fun _ => none
  captures : Nat → List Capture := fun _ => []
  rows : Memo := fun _ => none
  structureMemo : Memo := fun _ => none
  work : List Work := []
  pendingBounds : List Work := []
  tuplePorts : List (CopyKey × Nat) := []
  parents : List Parent := []
  pendingParents : List Nat := []
  calls : Nat := 0

def State.canonical (s : State) : Endpoint → Endpoint
  | .value endpoint => .value (endpoint.rename s.qv)
  | .effect endpoint => .effect (NativeMergeExpansion.renameEndpoint s.qe endpoint)

def State.canonicalBound (s : State) (bound : RawBound) : RawBound :=
  ⟨s.canonical bound.owner, bound.polarity, s.canonical bound.endpoint⟩

def State.lookup (s : State) (key : CopyKey) : Option Endpoint :=
  (s.rows key).orElse (fun _ => s.structureMemo key)

def State.storedTerm (s : State) (term : Nat) : Option StoredCell :=
  (s.terms.find? fun entry => entry.1 == term).map Prod.snd

def State.cells (s : State) : OriginalInferenceTerminationResolution.Cells :=
  fun term => (s.storedTerm term).map StoredCell.cell

def select (s : State) : Option (Work × State) :=
  match s.work with
  | item :: rest => some (item, {s with work := rest})
  | [] => match s.pendingBounds with
    | item :: rest => some (item, {s with pendingBounds := rest})
    | [] => none

inductive Failure where
  | identityExhausted
  | receiptMismatch
  | artifactMismatch
  | invariantViolation
  | native (code : Nat)
  deriving DecidableEq, Repr

/-- Results of the named native calls outside the Work-data projection.
They are neither a fiber-completeness predicate nor a successful-drain law.
`construct` includes errors before a Cell is committed; `constructAfter`
represents with_term_events sampling after publication. Capacity-only changes,
event arrays and resource-counter state are outside this projection. -/
inductive Check where
  | freshRow | retainParent | memo | linkBeforeAppend | linkAfterAppend
  | push | tupleReserve | tupleCharge | construct | constructAfter
  deriving DecidableEq, Repr

def requireSome (error : Failure) : Option α → Except Failure α
  | none => .error error
  | some value => .ok value

abbrev Funding := Nat → Check → Except Failure Unit

def funded : Funding := fun _ _ => .ok ()

inductive External where
  | bound (request : BoundRequest)
  | effectView (key : CopyKey) (view tail : Nat)
  | incomingAllowance (tail view : Nat) (source : Endpoint) (original : RawBound)
  | tuple (key : CopyKey) (children : List (CopyKey × Nat))
  | record (key : CopyKey) (fields : List (RecordBoundary.Field Nat))
      (children : List (CopyKey × Nat))
  | variant (key : CopyKey) (alternatives : List NativeValuePorts.Alternative)
      (children : List (CopyKey × Nat))
  | finish (root : Endpoint)

inductive Result where
  | next (state : State)
  | external (state : State) (call : External)
  | failed (state : State) (error : Failure)

def check (funds : Funding) (point : Check) (s : State) (next : State → Result) : Result :=
  let after := {s with calls := s.calls + 1}
  match funds s.calls point with
  | .error error => .failed after error
  | .ok () => next after

def push (funds : Funding) (pending : Bool) (item : Work) (s : State)
    (next : State → Result) : Result :=
  check funds .push s fun s =>
    next (if pending then {s with pendingBounds := item :: s.pendingBounds}
      else {s with work := item :: s.work})

def remember (funds : Funding) (row : Bool) (key : CopyKey) (endpoint : Endpoint)
    (s : State) (next : State → Result := Result.next) : Result :=
  check funds .memo s fun s =>
    next (if row then {s with rows := memoPut s.rows key endpoint}
      else {s with structureMemo := memoPut s.structureMemo key endpoint})

def pushAll (funds : Funding) (pending : Bool) (items : List Work) (s : State)
    (next : State → Result := Result.next) : Result :=
  match items with
  | [] => next s
  | item :: rest => push funds pending item s fun s => pushAll funds pending rest s next

def selectedValue (p : Polarity) (row : Bounds ValueEndpoint) : List Endpoint :=
  match p with
  | .positive => row.lowerRows.map (fun r => .value (.row r)) ++ row.lowerAtoms.map Endpoint.value
  | .negative => row.upperRows.map (fun r => .value (.row r)) ++ row.upperAtoms.map Endpoint.value

def selectedEffect (p : Polarity) (row : Bounds NativeMergeExpansion.Endpoint) : List Endpoint :=
  match p with
  | .positive => row.lowerRows.map (fun r => .effect (.row r)) ++ row.lowerAtoms.map Endpoint.effect
  | .negative => row.upperRows.map (fun r => .effect (.row r)) ++ row.upperAtoms.map Endpoint.effect

def State.rowInfo (s : State) (key : CopyKey) : Option (Nat × List Endpoint) :=
  match key.endpoint with
  | .value (.row id) => (s.values[id]?).map fun row => (row.level, selectedValue key.polarity row)
  | .effect (.row id) => (s.effects[id]?).map fun row => (row.level, selectedEffect key.polarity row)
  | _ => none

def State.freshEndpoint (s : State) (endpoint : Endpoint) : Endpoint :=
  match endpoint with
  | .value _ => .value (.row s.values.length)
  | .effect _ => .effect (.row s.effects.length)

def State.allocate (s : State) (key : CopyKey) : State :=
  match key.endpoint with
  | .value _ => {s with values := s.values ++ [⟨key.target, [], [], [], []⟩], qv := fun id => if id = s.values.length then id else s.qv id}
  | .effect _ => {s with effects := s.effects ++ [⟨key.target, [], [], [], []⟩], qe := fun id => if id = s.effects.length then id else s.qe id}

def State.retain (s : State) (key : CopyKey) (copy : Endpoint) : State :=
  {s with
    parents := s.parents ++ [⟨copy, key.endpoint, key.polarity, key.target, s.operation⟩]
    pendingParents := if s.operation.qualified then s.pendingParents ++ [s.parents.length]
      else s.pendingParents}

def addValue (p : Polarity) (item : ValueEndpoint) (row : Bounds ValueEndpoint) : Bounds ValueEndpoint :=
  match p, item with
  | .positive, .row id => {row with lowerRows := row.lowerRows ++ [id]}
  | .negative, .row id => {row with upperRows := row.upperRows ++ [id]}
  | .positive, item => {row with lowerAtoms := row.lowerAtoms ++ [item]}
  | .negative, item => {row with upperAtoms := row.upperAtoms ++ [item]}

def addEffect (p : Polarity) (item : NativeMergeExpansion.Endpoint)
    (row : Bounds NativeMergeExpansion.Endpoint) : Bounds NativeMergeExpansion.Endpoint :=
  match p, item with
  | .positive, .row id => {row with lowerRows := row.lowerRows ++ [id]}
  | .negative, .row id => {row with upperRows := row.upperRows ++ [id]}
  | .positive, item => {row with lowerAtoms := row.lowerAtoms ++ [item]}
  | .negative, item => {row with upperAtoms := row.upperAtoms ++ [item]}

def physicalInsert (s : State) (raw : RawBound) : Except Failure State := do
  let bound := s.canonicalBound raw
  match bound.owner, bound.endpoint with
  | .value (.row id), .value item =>
      let row ← requireSome .identityExhausted (s.values[id]?)
      return {s with values := s.values.set id (addValue bound.polarity item row)}
  | .effect (.row id), .effect item =>
      let row ← requireSome .identityExhausted (s.effects[id]?)
      return {s with effects := s.effects.set id (addEffect bound.polarity item row)}
  | _, _ => throw .identityExhausted

def childKey (s : State) (key : CopyKey) (bound : Endpoint) : CopyKey :=
  ⟨s.canonical bound, key.polarity, key.target⟩

/-- Pop order is Visit then Bound, with the original raw physical bound kept
in the source key. This is the reverse iteration plus two native pushes. -/
def boundJobs (s : State) (key : CopyKey) (copy : Endpoint) (bounds : List Endpoint) : List Work :=
  bounds.flatMap fun bound =>
    [.visit (childKey s key bound), .bound copy key.polarity (childKey s key bound)
      ⟨key.endpoint, key.polarity, bound⟩]

def incomingJobs (s : State) (key : CopyKey) (copy : Endpoint) : List Work :=
  match key.endpoint, key.polarity, copy with
  | .effect (.row id), .positive, .effect (.row tail) =>
      (s.captures id).reverse.flatMap fun incidence =>
        let source := s.canonical (.effect (.row incidence.source))
        let child : CopyKey := ⟨source, .positive, key.target⟩
        [.visit child, .incomingAllowance tail incidence.view child
          ⟨source, .negative, .effect (.allowance incidence.view)⟩]
  | _, _, _ => []

def scheduleBounds (funds : Funding) (s : State) (key : CopyKey) (copy : Endpoint)
    (old : List Endpoint) : Result :=
  pushAll funds true (boundJobs s key copy old).reverse s fun s =>
    pushAll funds true (incomingJobs s key copy).reverse s

/-- The two link gates retain failures before and after physical append.
They summarize external native admission/accounting outcomes, not an origin
fiber or semantic success. The exact link append is computed here. -/
def copiedRow (funds : Funding) (s : State) (key : CopyKey) (old : List Endpoint) : Result :=
  let copy := s.freshEndpoint key.endpoint
  let index := match copy with | .value (.row id) | .effect (.row id) => id | _ => 0
  if index ≥ 2^32 then .failed s .identityExhausted else
  check funds .freshRow s fun s =>
    let s := s.allocate key
    check funds .retainParent s fun s =>
      let s := s.retain key copy
      remember funds true key copy s fun s =>
        check funds .linkBeforeAppend s fun s =>
          match physicalInsert s ⟨key.endpoint, opposite key.polarity, copy⟩ with
          | .error error => .failed s error
          | .ok s => check funds .linkAfterAppend s fun s => scheduleBounds funds s key copy old

def readValue (s : State) (term : Nat) (p : Polarity) : Except Failure ValueEndpoint := do
  let stored ← requireSome .invariantViolation (s.storedTerm term)
  match stored.livePolarity with
  | some actual => if actual ≠ p then throw .invariantViolation
  | none => pure ()
  let endpoint ← requireSome .invariantViolation (stored.cell.readValue term)
  match endpoint with
  | .positiveFunction _ | .positiveRecord _ | .positiveVariant _ | .positiveTuple _ _ =>
      if p ≠ .positive then throw .invariantViolation
  | .negativeFunction _ | .negativeRecord _ | .negativeVariant _ | .negativeTuple _ _ =>
      if p ≠ .negative then throw .invariantViolation
  | _ => pure ()
  return endpoint.rename s.qv

def readEffect (s : State) (term : Nat) (p : Polarity) : Except Failure NativeMergeExpansion.Endpoint := do
  let stored ← requireSome .invariantViolation (s.storedTerm term)
  match stored.livePolarity with
  | some actual => if actual ≠ p then throw .invariantViolation
  | none => pure ()
  match stored.cell with
  | .effectLeaf (.row id) => return .row (s.qe id)
  | .effectLeaf .bottom => return .bottom
  | .effectLeaf .emptyNegative => return .emptyNegative
  | _ => throw .invariantViolation

def functionKeys (s : State) (p : Polarity) (target : Nat) (terms : FunctionTerms) :
    Except Failure (List CopyKey) :=
  match readValue s terms.argument (opposite p) with
  | .error error => .error error
  | .ok argument => match readEffect s terms.argumentEffect (opposite p) with
    | .error error => .error error
    | .ok argumentEffect => match readEffect s terms.resultEffect p with
      | .error error => .error error
      | .ok resultEffect => match readValue s terms.result p with
        | .error error => .error error
        | .ok result => .ok [⟨.value argument, opposite p, target⟩,
            ⟨.effect argumentEffect, opposite p, target⟩,
            ⟨.effect resultEffect, p, target⟩, ⟨.value result, p, target⟩]

def visitFunction (funds : Funding) (s : State) (key : CopyKey) (terms : FunctionTerms) : Result :=
  match functionKeys s key.polarity key.target terms with
  | .error error => .failed s error
  | .ok children =>
      push funds false (.function key children terms) s fun s =>
        pushAll funds false (children.reverse.map Work.visit) s

def State.termView (s : State) (term : Nat) : Option TermView := do
  let stored ← s.storedTerm term
  match stored.cell with
  | .structure view => some view
  | _ => none

inductive Aggregate where
  | tuple | record | variant
  deriving DecidableEq, Repr

def aggregateWork : Aggregate → CopyKey → Nat → Nat → Work
  | .tuple => Work.tuple
  | .record => Work.record
  | .variant => Work.variant

def collectPorts (s : State) (key : CopyKey) : List Nat → State × Except Failure Unit
  | [] => (s, .ok ())
  | term :: rest => match readValue s term key.polarity with
    | .error error => (s, .error error)
    | .ok value => collectPorts
        {s with tuplePorts := s.tuplePorts ++ [(⟨.value value, key.polarity, key.target⟩, term)]} key rest

def visitAggregate (funds : Funding) (s : State) (key : CopyKey) (kind : Aggregate)
    (terms : List Nat) : Result :=
  check funds .tupleReserve s fun s =>
    let start := s.tuplePorts.length
    let collected := collectPorts s key terms
    match collected.2 with
    | .error error => .failed collected.1 error
    | .ok () => check funds .tupleCharge collected.1 fun s =>
        let ports := (s.tuplePorts.drop start).take terms.length
        push funds false (aggregateWork kind key start terms.length) s fun s =>
          pushAll funds false (ports.reverse.map fun port => .visit port.1) s

def visitStructure (funds : Funding) (s : State) (key : CopyKey) : Result :=
  match key.endpoint with
  | .effect (.allowance view) | .effect (.support view) | .effect (.annotationMember view _) =>
      match s.views view with
      | none => .failed s .invariantViolation
      | some none => remember funds false key key.endpoint s
      | some (some tail) =>
          let child : CopyKey := ⟨s.canonical (.effect (.row tail)), key.polarity, key.target⟩
          push funds false (.effectView key view child) s fun s => push funds false (.visit child) s .next
  | .value (.positiveFunction term) =>
      match s.termView term with
      | some (.positiveFunction ports) => visitFunction funds s key ports
      | _ => .failed s .invariantViolation
  | .value (.negativeFunction term) =>
      match s.termView term with
      | some (.negativeFunction ports) => visitFunction funds s key ports
      | _ => .failed s .invariantViolation
  | .value (.positiveTuple term arity) | .value (.negativeTuple term arity) =>
      let elements := match key.polarity, s.termView term with
        | .positive, some (.positiveTuple xs) | .negative, some (.negativeTuple xs) => some xs
        | _, _ => none
      match elements with
      | some xs => if xs.length = arity ∧ arity ≠ 0 then visitAggregate funds s key .tuple xs
          else .failed s .identityExhausted
      | none => .failed s .identityExhausted
  | .value (.positiveRecord term) | .value (.negativeRecord term) =>
      match key.polarity, s.termView term with
      | .positive, some (.positiveRecord fields) | .negative, some (.negativeRecord fields) =>
          visitAggregate funds s key .record (fields.map fun field => field.2.ty)
      | _, _ => .failed s .receiptMismatch
  | .value (.positiveVariant term) | .value (.negativeVariant term) =>
      match key.polarity, s.termView term with
      | .positive, some (.positiveVariant xs) | .negative, some (.negativeVariant xs) =>
          visitAggregate funds s key .variant (xs.flatMap fun alternative => alternative.payloads)
      | _, _ => .failed s .receiptMismatch
  | _ => remember funds false key key.endpoint s

def visit (funds : Funding) (s : State) (key : CopyKey) : Result :=
  if (s.rows key).isSome || (s.structureMemo key).isSome then .next s else
  match key.endpoint with
  | .value (.row _) | .effect (.row _) =>
      match s.rowInfo key with
      | none => .failed s .invariantViolation
      | some (level, selected) =>
          if level ≤ key.target then remember funds true key key.endpoint s
          else copiedRow funds s key selected
  | _ => visitStructure funds s key

/-- Finite exact-key directory with actual raw labels, not dense term IDs.
`termLabel` is the still-external page allocator readout. Bad/colliding raw
readouts are invariant violations of this projection, not invented native
availability guards. No freshness or successful-formation proof is an input. -/
def internCell (s : State) (cell : StoredCell) : Except Failure (State × Nat) :=
  match s.terms.find? (fun entry => entry.2 == cell) with
  | some (term, _) =>
      if s.storedTerm term = some cell then .ok (s, term) else .error .invariantViolation
  | none =>
      let term := s.termLabel s.termAllocations
      if (s.storedTerm term).isSome then .error .invariantViolation else
        .ok ({s with terms := (term, cell) :: s.terms, termAllocations := s.termAllocations + 1}, term)

def endpointTerm (s : State) (endpoint : Endpoint) (p : Polarity) : Except Failure (State × Nat) :=
  match endpoint with
  | .value (.row id) => internCell s ⟨.valueLeaf (.row id), some p⟩
  | .effect (.row id) => internCell s ⟨.effectLeaf (.row id), some p⟩
  | .value (.positiveFunction term) | .value (.negativeFunction term)
  | .value (.positiveTuple term _) | .value (.negativeTuple term _)
  | .value (.positiveRecord term) | .value (.negativeRecord term)
  | .value (.positiveVariant term) | .value (.negativeVariant term) => .ok (s, term)
  | _ => .error .identityExhausted

def rebuildOne (funds : Funding) (s : State) (child : CopyKey) (original : Nat) :
    State × Except Failure (Nat × Bool) :=
      match s.lookup child with
      | none => (s, .error .identityExhausted)
      | some endpoint =>
          let changed := endpoint != child.endpoint
          let attempt : State × Except Failure Nat := if changed then
            match endpoint with
            | .value (.row _) | .effect (.row _) =>
                let after := {s with calls := s.calls + 1}
                match funds s.calls .construct with
                | .error error => (after, .error error)
                | .ok () => match endpointTerm after endpoint child.polarity with
                  | .error error => (after, .error error)
                  | .ok (state, term) =>
                      let sampled := {state with calls := state.calls + 1}
                      match funds state.calls .constructAfter with
                      | .error error => (sampled, .error error)
                      | .ok () => (sampled, .ok term)
            | _ => match endpointTerm s endpoint child.polarity with
              | .error error => (s, .error error)
              | .ok (state, term) => (state, .ok term)
            else (s, .ok original)
          (attempt.1, attempt.2.map fun term => (term, changed))

def rebuildTerms (funds : Funding) (s : State) (children : List CopyKey) (originals : List Nat) :
    State × Except Failure (List Nat × Bool) :=
  match children, originals with
  | [], [] => (s, .ok ([], false))
  | child :: rest, original :: originals =>
      let head := rebuildOne funds s child original
      match head.2 with
      | .error error => (head.1, .error error)
      | .ok (term, changed) =>
          let tail := rebuildTerms funds head.1 rest originals
          (tail.1, tail.2.map fun (terms, tailChanged) => (term :: terms, changed || tailChanged))
  | _, _ => (s, .error .invariantViolation)

/-- The actual BranchTermArena Function child guard, on the represented
Cell kinds. Source Component cells are not branch live-variable cells. -/
def matchesCell (effect : Bool) (p : Polarity) (stored : StoredCell) : Bool :=
  match stored.cell with
  | .valueLeaf endpoint =>
      if effect then false else match endpoint with
      | .row _ => stored.livePolarity == some p
      | .intPositive | .unitPositive | .boolPositive | .strPositive | .bottomPositive => p == .positive
      | .intNegative | .unitNegative | .boolNegative | .strNegative | .topNegative | .bottomNegative => p == .negative
      | _ => false
  | .effectLeaf endpoint =>
      if !effect then false else match endpoint with
      | .row _ => stored.livePolarity == some p
      | .bottom => p == .positive
      | .emptyNegative => p == .negative
      | _ => false
  | .structure view =>
      if effect then false else match view with
      | .positiveFunction _ | .positiveTuple _ | .positiveRecord _ | .positiveVariant _ => p == .positive
      | .negativeFunction _ | .negativeTuple _ | .negativeRecord _ | .negativeVariant _ => p == .negative
      | _ => false

def childMatches (s : State) (effect : Bool) (p : Polarity) (term : Nat) : Bool :=
  (s.storedTerm term).any (matchesCell effect p)

def functionMatches (s : State) (p : Polarity) (ports : FunctionTerms) : Bool :=
  childMatches s false (opposite p) ports.argument &&
  childMatches s true (opposite p) ports.argumentEffect &&
  childMatches s true p ports.resultEffect && childMatches s false p ports.result

def finishFunction (funds : Funding) (s : State) (key : CopyKey)
    (children : List CopyKey) (originals : FunctionTerms) : Result :=
  let result := rebuildTerms funds s children [originals.argument, originals.argumentEffect, originals.resultEffect, originals.result]
  let s := result.1
  match result.2 with
  | .error error => .failed s error
  | .ok (terms, changed) =>
      if !changed then remember funds false key key.endpoint s else
      match terms with
      | [a, ae, re, r] =>
          let ports : FunctionTerms := ⟨a, ae, re, r⟩
          if !functionMatches s key.polarity ports then .failed s .artifactMismatch else
          check funds .construct s fun s =>
            let view := match key.polarity with
              | .positive => TermView.positiveFunction ports
              | .negative => TermView.negativeFunction ports
            match internCell s ⟨.structure view, none⟩ with
            | .error error => .failed s error
            | .ok (s, term) => check funds .constructAfter s fun s =>
                let endpoint := match key.polarity with
                  | .positive => Endpoint.value (.positiveFunction term)
                  | .negative => Endpoint.value (.negativeFunction term)
                remember funds false key endpoint s
      | _ => .failed s .invariantViolation

def slice (s : State) (start len : Nat) (error : Failure) : Except Failure (List (CopyKey × Nat)) :=
  if start + len ≥ 2^64 then .error .identityExhausted else
  if start + len ≤ s.tuplePorts.length then .ok ((s.tuplePorts.drop start).take len)
  else .error error

def finishAggregate (funds : Funding) (s : State) (kind : Aggregate)
    (key : CopyKey) (start len : Nat) : Result :=
  let error := if kind = .tuple then Failure.identityExhausted else .receiptMismatch
  match slice s start len error with
  | .error error => .failed s error
  | .ok children =>
      if kind = .tuple ∧ children.any (fun child => (s.lookup child.1).isNone) then
        .failed s .identityExhausted
      else if !(children.any fun child => s.lookup child.1 != some child.1.endpoint) then
        remember funds false key key.endpoint s
      else match kind, key.endpoint with
      | .tuple, _ => .external s (.tuple key children)
      | .record, .value (.positiveRecord term) | .record, .value (.negativeRecord term) =>
          match key.polarity, s.termView term with
          | .positive, some (.positiveRecord fields) | .negative, some (.negativeRecord fields) =>
              .external s (.record key fields children)
          | _, _ => .failed s .receiptMismatch
      | .variant, .value (.positiveVariant term) | .variant, .value (.negativeVariant term) =>
          match key.polarity, s.termView term with
          | .positive, some (.positiveVariant xs) | .negative, some (.negativeVariant xs) =>
              .external s (.variant key xs children)
          | _, _ => .failed s .receiptMismatch
      | _, _ => .failed s .receiptMismatch

def boundRequest (s : State) (owner : Endpoint) (p : Polarity) (copied : Endpoint)
    (source : RawBound) : BoundRequest :=
  ⟨source, ⟨owner, p, copied⟩, s.canonicalBound ⟨owner, p, copied⟩, s.operation, true⟩

def perform (funds : Funding) (s : State) : Work → Result
  | .visit key => visit funds s key
  | .function key children originals => finishFunction funds s key children originals
  | .tuple key start len => finishAggregate funds s .tuple key start len
  | .record key start len => finishAggregate funds s .record key start len
  | .variant key start len => finishAggregate funds s .variant key start len
  | .effectView key view child => match s.lookup child with
    | some (.effect (.row tail)) => .external s (.effectView key view tail)
    | _ => .failed s .identityExhausted
  | .incomingAllowance tail view source original => match s.lookup source with
    | some copied => .external s (.incomingAllowance tail view copied original)
    | none => .failed s .identityExhausted
  | .bound owner p child source => match s.lookup child with
    | some copied => .external s (.bound (boundRequest s owner p copied source))
    | none => .failed s .identityExhausted

def step (funds : Funding) (s : State) : Result :=
  match select s with
  | some (task, state) => perform funds state task
  | none => match s.lookup ⟨s.canonical s.operation.initial, s.operation.polarity, s.operation.target⟩ with
    | some root => .external s (.finish root)
    | none => .failed s .identityExhausted

/-- Explicit finite observation prefix only: exhausting its index returns the
current unfinished state. It is never interpreted as inference completion. -/
def runPrefix (funds : Funding) : Nat → State → Result
  | 0, s => .next s
  | n + 1, s => match step funds s with
    | .next next => runPrefix funds n next
    | other => other


/-- Entry after begin_candidate_extrusion has supplied its occurrence.
Only operation-local tables are cleared; shared physical stores survive. -/
def initializeLocal (s : State) (operation : Operation) : State :=
  {s with
    operation := operation
    rows := fun _ => none
    structureMemo := fun _ => none
    work := []
    pendingBounds := []
    tuplePorts := []}

def start (funds : Funding) (s : State) (operation : Operation) : Result :=
  let initial := initializeLocal s operation
  push funds false (.visit ⟨initial.canonical operation.initial, operation.polarity, operation.target⟩) initial .next

/-! Computed producer equations. -/

theorem operation_local_memos (s : State) (operation : Operation) (key : CopyKey) :
    (initializeLocal s operation).rows key = none ∧ (initializeLocal s operation).structureMemo key = none ∧
    (initializeLocal s operation).values = s.values ∧ (initializeLocal s operation).effects = s.effects ∧
    (initializeLocal s operation).terms = s.terms := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem fresh_value_after_receiver (s : State) (receiver : Nat) (row : Bounds ValueEndpoint)
    (present : s.values[receiver]? = some row) : receiver < s.values.length :=
  (List.getElem?_eq_some_iff.mp present).1

theorem structural_work_first (s : State) (task : Work) (rest : List Work) :
    select {s with work := task :: rest} = some (task, {s with work := rest}) := rfl

theorem pending_work_selected (s : State) (task : Work) (rest : List Work) :
    select {s with work := [], pendingBounds := task :: rest} =
      some (task, {s with work := [], pendingBounds := rest}) := rfl

theorem rows_memo_first (s : State) (key : CopyKey) (copied : Endpoint)
    (found : s.rows key = some copied) : s.lookup key = some copied := by
  simp [State.lookup, found]

theorem memoized_visit (funds : Funding) (s : State) (key : CopyKey) (copied : Endpoint)
    (found : s.rows key = some copied) : visit funds s key = .next s := by
  simp [visit, found]

theorem memo_insert_read (memo : Memo) (key : CopyKey) (copied : Endpoint) :
    memoPut memo key copied key = some copied := by simp [memoPut]

theorem old_value_vector_selected (p : Polarity) (row : Bounds ValueEndpoint)
    (link : ValueEndpoint) : selectedValue p (addValue (opposite p) link row) = selectedValue p row := by
  cases p <;> cases link <;> rfl

theorem old_effect_vector_selected (p : Polarity) (row : Bounds NativeMergeExpansion.Endpoint)
    (link : NativeMergeExpansion.Endpoint) :
    selectedEffect p (addEffect (opposite p) link row) = selectedEffect p row := by
  cases p <;> cases link <;> rfl

theorem allocate_value_ordinal (s : State) (parent : ValueEndpoint) (p : Polarity) (target : Nat) :
    s.freshEndpoint (.value parent) = .value (.row s.values.length) ∧
    (s.allocate ⟨.value parent, p, target⟩).values[s.values.length]? = some ⟨target, [], [], [], []⟩ ∧
    (s.allocate ⟨.value parent, p, target⟩).effects = s.effects ∧
    (s.allocate ⟨.value parent, p, target⟩).qv s.values.length = s.values.length := by
  simp [State.freshEndpoint, State.allocate]

theorem allocate_effect_ordinal (s : State) (parent : NativeMergeExpansion.Endpoint) (p : Polarity) (target : Nat) :
    s.freshEndpoint (.effect parent) = .effect (.row s.effects.length) ∧
    (s.allocate ⟨.effect parent, p, target⟩).effects[s.effects.length]? = some ⟨target, [], [], [], []⟩ ∧
    (s.allocate ⟨.effect parent, p, target⟩).values = s.values ∧
    (s.allocate ⟨.effect parent, p, target⟩).qe s.effects.length = s.effects.length := by
  simp [State.freshEndpoint, State.allocate]

theorem retain_does_not_merge (s : State) (key : CopyKey) (copy : Endpoint) :
    (s.retain key copy).values = s.values ∧ (s.retain key copy).effects = s.effects ∧
    (s.retain key copy).qv = s.qv ∧ (s.retain key copy).qe = s.qe ∧
    (s.retain key copy).parents = s.parents ++ [⟨copy, key.endpoint, key.polarity, key.target, s.operation⟩] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

def prepared (s : State) (key : CopyKey) : State :=
  let copy := s.freshEndpoint key.endpoint
  let a := ({s with calls := s.calls + 1} : State).allocate key
  let b := ({a with calls := a.calls + 1} : State).retain key copy
  {b with calls := b.calls + 1, rows := memoPut b.rows key copy}

theorem prepared_row_memo (s : State) (key : CopyKey) :
    (prepared s key).rows key = some (s.freshEndpoint key.endpoint) := by
  simp [prepared, memoPut]

/-- An actual failed native link call witnesses that memoization already
occurred. The failure does not pretend that a selected bound or fiber exists. -/
theorem memo_precedes_link_call (s : State) (key : CopyKey) (old : List Endpoint)
    (error : Failure)
    (room : (match key.endpoint with | .value _ => s.values.length | .effect _ => s.effects.length) < 2^32) :
    copiedRow (fun _ point => if point = .linkBeforeAppend then .error error else .ok ()) s key old =
      .failed {prepared s key with calls := (prepared s key).calls + 1} error := by
  rcases key with ⟨endpoint, p, target⟩
  cases endpoint <;> dsimp only at room <;>
    simp [copiedRow, State.freshEndpoint, prepared, check, remember, Nat.not_le.mpr room]

def pushed (pending : Bool) (items : List Work) (s : State) : State :=
  if pending then {s with pendingBounds := items.reverse ++ s.pendingBounds, calls := s.calls + items.length}
  else {s with work := items.reverse ++ s.work, calls := s.calls + items.length}

theorem push_all_funded (pending : Bool) (items : List Work) (s : State) (next : State → Result) :
    pushAll funded pending items s next = next (pushed pending items s) := by
  induction items generalizing s with
  | nil => cases pending <;> simp [pushAll, pushed]
  | cons item rest ih =>
      simp only [pushAll, push, check, funded]
      rw [ih]
      cases pending <;> simp [pushed, List.reverse_cons, List.append_assoc, Nat.add_left_comm, Nat.add_comm]

theorem selected_bound_job (s : State) (key : CopyKey) (copy bound : Endpoint)
    (old : List Endpoint) (member : bound ∈ old) :
    Work.bound copy key.polarity (childKey s key bound) ⟨key.endpoint, key.polarity, bound⟩ ∈
      boundJobs s key copy old := by
  simp only [boundJobs, List.mem_flatMap]
  exact ⟨bound, member, by simp⟩

theorem selected_visit_job (s : State) (key : CopyKey) (copy bound : Endpoint)
    (old : List Endpoint) (member : bound ∈ old) :
    Work.visit (childKey s key bound) ∈ boundJobs s key copy old := by
  simp only [boundJobs, List.mem_flatMap]
  exact ⟨bound, member, by simp⟩

theorem bound_job_preserves_raw (s : State) (key : CopyKey) (copy bound : Endpoint) :
    boundJobs s key copy [bound] =
      [.visit ⟨s.canonical bound, key.polarity, key.target⟩,
       .bound copy key.polarity ⟨s.canonical bound, key.polarity, key.target⟩
         ⟨key.endpoint, key.polarity, bound⟩] := rfl

def scheduled (s : State) (key : CopyKey) (copy : Endpoint) (old : List Endpoint) : State :=
  {s with
    pendingBounds := incomingJobs s key copy ++ boundJobs s key copy old ++ s.pendingBounds
    calls := s.calls + (boundJobs s key copy old).length + (incomingJobs s key copy).length}

theorem schedule_bounds_computed (s : State) (key : CopyKey) (copy : Endpoint) (old : List Endpoint) :
    scheduleBounds funded s key copy old = .next (scheduled s key copy old) := by
  unfold scheduleBounds
  rw [push_all_funded, push_all_funded]
  simp [pushed, scheduled, incomingJobs, State.canonical]

theorem scheduled_old_bound (s : State) (key : CopyKey) (copy bound : Endpoint)
    (old : List Endpoint) (member : bound ∈ old) :
    Work.bound copy key.polarity (childKey s key bound) ⟨key.endpoint, key.polarity, bound⟩ ∈
      (scheduled s key copy old).pendingBounds := by
  exact List.mem_append_left _ (List.mem_append_right _ (selected_bound_job s key copy bound old member))

theorem function_keys_computed (s : State) (p : Polarity) (target : Nat) (terms : FunctionTerms)
    (a r : ValueEndpoint) (ae re : NativeMergeExpansion.Endpoint)
    (argument : readValue s terms.argument (opposite p) = .ok a)
    (argumentEffect : readEffect s terms.argumentEffect (opposite p) = .ok ae)
    (resultEffect : readEffect s terms.resultEffect p = .ok re)
    (result : readValue s terms.result p = .ok r) :
    functionKeys s p target terms = .ok
      [⟨.value a, opposite p, target⟩, ⟨.effect ae, opposite p, target⟩,
       ⟨.effect re, p, target⟩, ⟨.value r, p, target⟩] := by
  simp [functionKeys, argument, argumentEffect, resultEffect, result]

theorem function_keys_have_four (s : State) (p : Polarity) (target : Nat) (terms : FunctionTerms)
    (children : List CopyKey) (computed : functionKeys s p target terms = .ok children) :
    children.length = 4 := by
  cases a : readValue s terms.argument (opposite p) <;>
    cases ae : readEffect s terms.argumentEffect (opposite p) <;>
    cases re : readEffect s terms.resultEffect p <;>
    cases r : readValue s terms.result p <;>
    simp [functionKeys, a, ae, re, r] at computed
  cases computed
  rfl

theorem bound_missing_stops (funds : Funding) (s : State) (owner : Endpoint) (p : Polarity)
    (child : CopyKey) (original : RawBound) (missing : s.lookup child = none) :
    perform funds s (.bound owner p child original) = .failed s .identityExhausted := by
  simp [perform, missing]

theorem cell_constructor_readback (s after : State) (cell : StoredCell) (term : Nat)
    (computed : internCell s cell = .ok (after, term)) : after.storedTerm term = some cell := by
  unfold internCell at computed
  split at computed
  next found =>
    split at computed
    next same => cases computed; exact same
    next => cases computed
  next =>
    dsimp only at computed
    split at computed
    · cases computed
    · cases computed
      simp [State.storedTerm]

/-- Every pre-existing raw slot survives a successfully checked constructor.
No theorem equates a physical term label with its allocation ordinal. -/
theorem cell_constructor_immutable (s after : State) (cell : StoredCell) (term : Nat)
    (computed : internCell s cell = .ok (after, term)) :
    ∀ old value, s.storedTerm old = some value → after.storedTerm old = some value := by
  unfold internCell at computed
  split at computed
  next found =>
    split at computed
    · cases computed; exact fun _ _ h => h
    · cases computed
  next =>
    dsimp only at computed
    split at computed
    · cases computed
    next fresh =>
      cases computed
      intro old value present
      have different : s.termLabel s.termAllocations ≠ old := by
        intro same
        simp [same, present] at fresh
      simpa [State.storedTerm, different] using present

/-- The client consumes this equation: the request is constructed from the
actual selected Work and rows-first memo, not supplied as an arbitrary value. -/
theorem selected_bound_dispatch (funds : Funding) (s popped : State)
    (owner : Endpoint) (p : Polarity) (child : CopyKey) (original : RawBound)
    (copied : Endpoint)
    (selected : select s = some (.bound owner p child original, popped))
    (memo : popped.lookup child = some copied) :
    step funds s = .external popped (.bound (boundRequest popped owner p copied original)) := by
  simp [step, selected, perform, memo]

theorem bound_dispatch_from_pending (funds : Funding) (s : State)
    (owner : Endpoint) (p : Polarity) (child : CopyKey) (original : RawBound)
    (copied : Endpoint) (rest : List Work) (memo : s.lookup child = some copied) :
    step funds {s with work := [], pendingBounds := .bound owner p child original :: rest} =
      .external {s with work := [], pendingBounds := rest}
        (.bound (boundRequest s owner p copied original)) := by
  exact selected_bound_dispatch funds _ _ owner p child original copied rfl memo

theorem bound_request_whole (s : State) (owner : Endpoint) (p : Polarity)
    (copied : Endpoint) (original : RawBound) :
    (boundRequest s owner p copied original).original = original ∧
    (boundRequest s owner p copied original).insertion = ⟨owner, p, copied⟩ ∧
    (boundRequest s owner p copied original).destination = s.canonicalBound ⟨owner, p, copied⟩ ∧
    (boundRequest s owner p copied original).operation = s.operation ∧
    (boundRequest s owner p copied original).capture = true := ⟨rfl, rfl, rfl, rfl, rfl⟩



theorem function_visit_computed (s : State) (key : CopyKey) (terms : FunctionTerms)
    (children : List CopyKey) (computed : functionKeys s key.polarity key.target terms = .ok children) :
    visitFunction funded s key terms = .next
      {s with work := children.map Work.visit ++ .function key children terms :: s.work, calls := s.calls + 1 + children.length} := by
  simp only [visitFunction, computed, push, check, funded]
  rw [push_all_funded]
  simp [pushed, List.map_reverse]

def preLink (s : State) (key : CopyKey) : State :=
  {prepared s key with calls := (prepared s key).calls + 1}

theorem copied_row_schedules (s : State) (key : CopyKey) (old : List Endpoint) (linked : State)
    (room : (match key.endpoint with | .value _ => s.values.length | .effect _ => s.effects.length) < 2^32)
    (link : physicalInsert (preLink s key)
      ⟨key.endpoint, opposite key.polarity, s.freshEndpoint key.endpoint⟩ = .ok linked) :
    copiedRow funded s key old = .next
      (scheduled {linked with calls := linked.calls + 1} key (s.freshEndpoint key.endpoint) old) := by
  have indexRoom : ¬ (match s.freshEndpoint key.endpoint with
      | .value (.row id) | .effect (.row id) => id | _ => 0) ≥ 2^32 := by
    cases endpoint : key.endpoint <;> simpa [State.freshEndpoint, endpoint] using Nat.not_le.mpr room
  unfold copiedRow
  simp only [indexRoom, ↓reduceIte, check, funded, remember]
  change (match physicalInsert (preLink s key)
      ⟨key.endpoint, opposite key.polarity, s.freshEndpoint key.endpoint⟩ with
    | .error error => Result.failed (preLink s key) error
    | .ok after => scheduleBounds funded {after with calls := after.calls + 1}
        key (s.freshEndpoint key.endpoint) old) = _
  rw [link]
  exact schedule_bounds_computed _ _ _ _

theorem high_row_visit_schedules (s : State) (key : CopyKey) (old : List Endpoint)
    (level : Nat) (linked : State)
    (rowFresh : s.rows key = none) (structureFresh : s.structureMemo key = none)
    (row : ∃ id, key.endpoint = .value (.row id) ∨ key.endpoint = .effect (.row id))
    (selected : s.rowInfo key = some (level, old)) (high : key.target < level)
    (room : (match key.endpoint with | .value _ => s.values.length | .effect _ => s.effects.length) < 2^32)
    (link : physicalInsert (preLink s key)
      ⟨key.endpoint, opposite key.polarity, s.freshEndpoint key.endpoint⟩ = .ok linked) :
    visit funded s key = .next
      (scheduled {linked with calls := linked.calls + 1} key (s.freshEndpoint key.endpoint) old) := by
  have copied := copied_row_schedules s key old linked room link
  obtain ⟨id, endpoint | endpoint⟩ := row <;>
    simpa [visit, rowFresh, structureFresh, endpoint, selected, Nat.not_le.mpr high] using copied

namespace Computed

/-- A local native-shaped input, not extraction of the source seed in NQ.
The symbolic caller keeps its complete context/source/Flow payload. -/
def functionInput (caller : Request) : State :=
  {operation := ⟨.value (.positiveFunction 50), .positive, 1, 87, some 52, caller, caller.sources, false⟩
   values := [⟨2, [], [1], [], []⟩, ⟨2, [], [2], [], []⟩,
     ⟨2, [], [3], [], []⟩, ⟨1, [], [], [], []⟩]
   effects := [⟨2, [], [], [], []⟩]
   terms := [(10, ⟨.valueLeaf (.row 0), some .negative⟩),
     (20, ⟨.effectLeaf (.row 0), some .negative⟩),
     (30, ⟨.effectLeaf (.row 0), some .positive⟩),
     (40, ⟨.valueLeaf (.row 0), some .positive⟩),
     (50, ⟨.structure (.positiveFunction ⟨10, 20, 30, 40⟩), none⟩)]
   termLabel := fun index => 4096 + index
   work := [.visit ⟨.value (.positiveFunction 50), .positive, 1⟩]}

def outcomeState : Result → State
  | .next s | .external s _ | .failed s _ => s

/-- Explicit in-progress Function frame: its four copied rows have already
been allocated. No completed Function, bound or fiber is an input. General
row-producer equations above own construction of such prefixes; this instance
checks the actual rebuild operation and its immutable Cell publication. -/
def rebuildInput (caller : Request) : State :=
  let s := functionInput caller
  {s with
    values := s.values ++ [⟨1, [], [], [], []⟩, ⟨1, [], [], [], []⟩]
    effects := s.effects ++ [⟨1, [], [], [], []⟩, ⟨1, [], [], [], []⟩]
    rows := memoPut (memoPut (memoPut (memoPut (fun _ => none)
      ⟨.value (.row 0), .negative, 1⟩ (.value (.row 4)))
      ⟨.effect (.row 0), .negative, 1⟩ (.effect (.row 1)))
      ⟨.effect (.row 0), .positive, 1⟩ (.effect (.row 2)))
      ⟨.value (.row 0), .positive, 1⟩ (.value (.row 5))
    work := [.function ⟨.value (.positiveFunction 50), .positive, 1⟩
      [⟨.value (.row 0), .negative, 1⟩, ⟨.effect (.row 0), .negative, 1⟩,
       ⟨.effect (.row 0), .positive, 1⟩, ⟨.value (.row 0), .positive, 1⟩] ⟨10, 20, 30, 40⟩]}

def samplingFailure : Funding := fun index point =>
  if index = 9 ∧ point = .constructAfter then .error (.native 17) else .ok ()

def prefixFunds (failing : Bool) : Funding := if failing then samplingFailure else funded

def rowCells (caller : Request) (cells : List (Nat × StoredCell)) : State :=
  {rebuildInput caller with
    work := []
    terms := cells ++ (functionInput caller).terms
    termAllocations := cells.length
    calls := cells.length * 2}

def argumentCell : Nat × StoredCell := (4096, ⟨.valueLeaf (.row 4), some .negative⟩)
def argumentEffectCell : Nat × StoredCell := (4097, ⟨.effectLeaf (.row 1), some .negative⟩)
def resultEffectCell : Nat × StoredCell := (4098, ⟨.effectLeaf (.row 2), some .positive⟩)
def resultCell : Nat × StoredCell := (4099, ⟨.valueLeaf (.row 5), some .positive⟩)

theorem argument_cell_computed (caller : Request) (failing : Bool) :
    rebuildOne (prefixFunds failing) (rowCells caller [])
      ⟨.value (.row 0), .negative, 1⟩ 10 =
      (rowCells caller [argumentCell], .ok (4096, true)) := by
  cases failing <;> rfl

theorem argument_effect_cell_computed (caller : Request) (failing : Bool) :
    rebuildOne (prefixFunds failing) (rowCells caller [argumentCell])
      ⟨.effect (.row 0), .negative, 1⟩ 20 =
      (rowCells caller [argumentEffectCell, argumentCell], .ok (4097, true)) := by
  cases failing <;> rfl

theorem result_effect_cell_computed (caller : Request) (failing : Bool) :
    rebuildOne (prefixFunds failing) (rowCells caller [argumentEffectCell, argumentCell])
      ⟨.effect (.row 0), .positive, 1⟩ 30 =
      (rowCells caller [resultEffectCell, argumentEffectCell, argumentCell], .ok (4098, true)) := by
  cases failing <;> rfl

theorem result_cell_computed (caller : Request) (failing : Bool) :
    rebuildOne (prefixFunds failing) (rowCells caller [resultEffectCell, argumentEffectCell, argumentCell])
      ⟨.value (.row 0), .positive, 1⟩ 40 =
      (rowCells caller [resultCell, resultEffectCell, argumentEffectCell, argumentCell], .ok (4099, true)) := by
  cases failing <;> rfl

theorem row_terms_computed (caller : Request) (failing : Bool) :
    rebuildTerms (prefixFunds failing) (rowCells caller [])
      [⟨.value (.row 0), .negative, 1⟩, ⟨.effect (.row 0), .negative, 1⟩,
       ⟨.effect (.row 0), .positive, 1⟩, ⟨.value (.row 0), .positive, 1⟩]
      [10, 20, 30, 40] =
      (rowCells caller [resultCell, resultEffectCell, argumentEffectCell, argumentCell],
        .ok ([4096, 4097, 4098, 4099], true)) := by
  simp [rebuildTerms, argument_cell_computed, argument_effect_cell_computed,
    result_effect_cell_computed, result_cell_computed, Except.map]

def publishedCells (caller : Request) : State :=
  let s := rebuildInput caller
  {s with
    work := []
    terms := [(4100, ⟨.structure (.positiveFunction ⟨4096, 4097, 4098, 4099⟩), none⟩),
      (4099, ⟨.valueLeaf (.row 5), some .positive⟩),
      (4098, ⟨.effectLeaf (.row 2), some .positive⟩),
      (4097, ⟨.effectLeaf (.row 1), some .negative⟩),
      (4096, ⟨.valueLeaf (.row 4), some .negative⟩)] ++ s.terms
    termAllocations := 5
    calls := 10}

def rebuilt (caller : Request) : State :=
  let s := publishedCells caller
  let memo := memoPut s.structureMemo
    ⟨.value (.positiveFunction 50), .positive, 1⟩ (.value (.positiveFunction 4100))
  {s with calls := 11, structureMemo := memo}

theorem function_keys_from_cells (caller : Request) :
    functionKeys (functionInput caller) .positive 1 ⟨10, 20, 30, 40⟩ = .ok
      [⟨.value (.row 0), .negative, 1⟩, ⟨.effect (.row 0), .negative, 1⟩,
       ⟨.effect (.row 0), .positive, 1⟩, ⟨.value (.row 0), .positive, 1⟩] := rfl

theorem function_rebuilt (caller : Request) :
    step funded (rebuildInput caller) = .next (rebuilt caller) ∧
    (rebuilt caller).structureMemo ⟨.value (.positiveFunction 50), .positive, 1⟩ = some (.value (.positiveFunction 4100)) ∧
    (rebuilt caller).cells 4100 = some (.structure (.positiveFunction ⟨4096, 4097, 4098, 4099⟩)) ∧
    (rebuilt caller).cells 4096 = some (.valueLeaf (.row 4)) ∧
    (rebuilt caller).cells 4097 = some (.effectLeaf (.row 1)) ∧
    (rebuilt caller).cells 4098 = some (.effectLeaf (.row 2)) ∧
    (rebuilt caller).cells 4099 = some (.valueLeaf (.row 5)) := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  change finishFunction funded (rowCells caller [])
    ⟨.value (.positiveFunction 50), .positive, 1⟩
    [⟨.value (.row 0), .negative, 1⟩, ⟨.effect (.row 0), .negative, 1⟩,
     ⟨.effect (.row 0), .positive, 1⟩, ⟨.value (.row 0), .positive, 1⟩]
    ⟨10, 20, 30, 40⟩ = .next (rebuilt caller)
  unfold finishFunction
  rw [show funded = prefixFunds false from rfl, row_terms_computed]
  rfl

def failedPublished (caller : Request) : State := publishedCells caller

/-- with_term_events may fail after the Function Cell was committed. That
Cell and all four earlier row Cells survive; structure memoization has not
happened. The error is supplied at its real post-publication call boundary. -/
theorem post_publication_failure_retains_cells (caller : Request) :
    step samplingFailure (rebuildInput caller) = .failed (failedPublished caller) (.native 17) ∧
    (failedPublished caller).cells 4100 = some (.structure (.positiveFunction ⟨4096, 4097, 4098, 4099⟩)) ∧
    (failedPublished caller).cells 4096 = some (.valueLeaf (.row 4)) ∧
    (failedPublished caller).cells 4097 = some (.effectLeaf (.row 1)) ∧
    (failedPublished caller).cells 4098 = some (.effectLeaf (.row 2)) ∧
    (failedPublished caller).cells 4099 = some (.valueLeaf (.row 5)) ∧
    (failedPublished caller).structureMemo ⟨.value (.positiveFunction 50), .positive, 1⟩ = none := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  change finishFunction samplingFailure (rowCells caller [])
    ⟨.value (.positiveFunction 50), .positive, 1⟩
    [⟨.value (.row 0), .negative, 1⟩, ⟨.effect (.row 0), .negative, 1⟩,
     ⟨.effect (.row 0), .positive, 1⟩, ⟨.value (.row 0), .positive, 1⟩]
    ⟨10, 20, 30, 40⟩ = .failed (failedPublished caller) (.native 17)
  unfold finishFunction
  rw [show samplingFailure = prefixFunds true from rfl, row_terms_computed]
  rfl

theorem negative_copy_in_function (caller : Request) :
    OriginalInferenceTerminationResolution.ValueUses (rebuilt caller).cells
      (.positiveFunction 4100) (.value 4) :=
  OriginalInferenceTerminationResolution.positive_function_uses_argument
    (function_rebuilt caller).2.2.1 (function_rebuilt caller).2.2.2.1

/-- Nonempty actual selected upper vector; unlike the Function frame above,
this example computes the entire row Visit -> child Visit -> Bound prefix. -/
def rowInput (caller : Request) : State :=
  {operation := ⟨.value (.row 0), .negative, 1, 87, some 52, caller, caller.sources, false⟩
   values := [⟨2, [], [1], [], []⟩, ⟨1, [], [], [], []⟩]
   work := [.visit ⟨.value (.row 0), .negative, 1⟩]}

def rowBoundState (caller : Request) : State := outcomeState (runPrefix funded 3 (rowInput caller))

def rowBoundRequest (caller : Request) : BoundRequest :=
  boundRequest (rowBoundState caller) (.value (.row 2)) .negative (.value (.row 1))
    ⟨.value (.row 0), .negative, .value (.row 1)⟩

theorem row_bound_produced (caller : Request) :
    runPrefix funded 3 (rowInput caller) =
      .external (rowBoundState caller) (.bound (rowBoundRequest caller)) ∧
    (rowBoundState caller).values.map Bounds.level = [2, 1, 1] ∧
    (rowBoundState caller).rows ⟨.value (.row 0), .negative, 1⟩ = some (.value (.row 2)) ∧
    (rowBoundRequest caller).operation.caller = caller ∧
    (rowBoundRequest caller).original = ⟨.value (.row 0), .negative, .value (.row 1)⟩ ∧
    (rowBoundRequest caller).destination = ⟨.value (.row 2), .negative, .value (.row 1)⟩ := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Computed

end YulangClosure.OriginalExtrusionWork
