import YulangClosure.FormalPermissionConstructorRealization

/-! Mathematical decoder of finite constructor instructions and typed observations.
No native trace authenticity, capture simulation or actual export is asserted.
Original rows and observed representatives remain separate coordinates. -/
namespace YulangClosure.FormalPermissionExportWitness
open FormalPermissionSourceOrigin FormalPermissionConstructorRealization
open FormalPermissionCaptureConstruction
open FormalPermissionLiveCapture (prependPath atPort shift)
noncomputable section

structure MemoDecoded (scope name : Nat) (s : State) where
  row : Nat
  state : State
  births : List Nat
  event : EffectMemo scope name s row state births

def decodeMemo (scope name : Nat) (s : State) : MemoDecoded scope name s := by
  cases found : s.effects (scope, name) with
  | some row => exact ⟨row, s, [], .hit s row found⟩
  | none => exact ⟨s.nextEffect, {s with nextEffect := s.nextEffect + 1, effects := fun key => if key = (scope, name) then some s.nextEffect else s.effects key},
      [s.nextEffect], .miss s found⟩

structure ViewDecoded (c : Context) (position : Nat) (concrete : List Nat)
    (tail : Option Nat) (s : State) where
  view : Nat
  state : State
  event : ViewEvent c position concrete tail s view state

def decodeView (c : Context) (position : Nat) (concrete : List Nat)
    (tail : Option Nat) (s : State) : ViewDecoded c position concrete tail s := by
  cases found : s.views position with
  | some view => exact ⟨view, s, .hit s view found⟩
  | none => exact ⟨s.nextView, {s with nextView := s.nextView + 1, views := fun p => if p = position then some s.nextView else s.views p, viewData := fun i => if i = s.nextView then some ⟨c.owner, c.scope, position, concrete, tail⟩ else s.viewData i}, .miss s found⟩

structure SignatureDecoded (c : Context) (position : Nat) (concrete : List Nat)
    (p : Bool) (symbolVar : Option Nat) (s : State) where
  row : Nat
  bound : SignatureBound
  state : State
  births : List Nat
  event : SignatureEvent c position concrete p symbolVar s row bound state births

def decodeSignature (c : Context) (position : Nat) (concrete : List Nat)
    (p : Bool) (symbolVar : Option Nat) (s : State) :
    SignatureDecoded c position concrete p symbolVar s :=
  match symbolVar with
  | none =>
      let v := decodeView c position concrete none s
      ⟨v.state.nextEffect, ⟨v.state.nextEffect, p, v.view, none⟩,
        {v.state with nextEffect := v.state.nextEffect + 1}, [v.state.nextEffect], .closed v.event⟩
  | some name =>
      let m := decodeMemo c.scope name s
      let v := decodeView c position concrete (some m.row) m.state
      ⟨v.state.nextEffect, ⟨v.state.nextEffect, p, v.view, some m.row⟩,
        {v.state with nextEffect := v.state.nextEffect + 1}, m.births ++ [v.state.nextEffect],
        .tailed m.event v.event⟩

theorem signature_decoded_birth (c : Context) (position : Nat) (concrete : List Nat)
    (p : Bool) (symbolVar : Option Nat) (s : State) :
    (decodeSignature c position concrete p symbolVar s).row ∈
      (decodeSignature c position concrete p symbolVar s).births := by
  cases symbolVar <;> simp [decodeSignature]

theorem delegated_allocations (c : Context) (position : Nat) (concrete : List Nat)
    (symbolVar : Option Nat) (s : State) :
    let pos := decodeSignature c position concrete true symbolVar s
    let neg := decodeSignature c position concrete false symbolVar pos.state
    SignaturePairEvent c position concrete symbolVar s
      ⟨.row pos.row, .row neg.row, none⟩ [pos.bound, neg.bound] neg.state (pos.births ++ neg.births) ∧
      pos.row ∈ pos.births ∧ neg.row ∈ neg.births := by
  exact ⟨.pair (decodeSignature c position concrete true symbolVar s).event
    (decodeSignature c position concrete false symbolVar
      (decodeSignature c position concrete true symbolVar s).state).event, signature_decoded_birth c position concrete true symbolVar s,
    signature_decoded_birth c position concrete false symbolVar _⟩

structure PortDecoded (c : Context) (p : Bool) (source : SourcePort) (s : State) where
  out : PortResult
  births : List Nat
  event : PortEvent c p source s out births

def decodePort (c : Context) (p : Bool) (source : SourcePort) (s : State) :
    Option (PortDecoded c p source s) := by
  cases source with
  | omitted => exact some ⟨⟨sharedPorts s.nextEffect, [], [],
      {s with nextEffect := s.nextEffect + 1}⟩, [s.nextEffect], .omitted p s⟩
  | symbolic name =>
      let m := decodeMemo c.scope name s
      exact some ⟨⟨sharedPorts m.row, [], [], m.state⟩, m.births, .symbolic m.event⟩
  | explicit position concrete symbolVar =>
      by_cases singleton : concrete = [] ∧ symbolVar ≠ none
      · cases symbolVar with
        | none => exact False.elim (singleton.2 rfl)
        | some name =>
            obtain ⟨rfl, _⟩ := singleton
            let m := decodeMemo c.scope name s
            exact some ⟨⟨sharedPorts m.row, [], [], m.state⟩, m.births, .singleton m.event⟩
      · cases p with
        | true =>
            let pos := decodeSignature c position concrete true symbolVar s
            let neg := decodeSignature c position concrete false symbolVar pos.state
            exact some ⟨⟨⟨.row pos.row, .row neg.row, none⟩, [], [pos.bound, neg.bound], neg.state⟩,
              pos.births ++ neg.births, .delegated singleton (.pair pos.event neg.event)⟩
        | false =>
            by_cases allowed : concrete ≠ [] ∧ symbolVar = none
            · obtain ⟨nonempty, rfl⟩ := allowed
              exact some ⟨⟨sharedPorts s.nextEffect (some (c.metadata position concrete)),
                [⟨c.metadata position concrete, s.nextEffect⟩], [],
                {s with nextEffect := s.nextEffect + 1}⟩,
                [s.nextEffect], .concrete s position concrete nonempty⟩
            · exact none

/- Data instructions, not a typing judgment or an assumed event history. -/
mutual
  inductive ValueCode where
    | scalar (identity : Nat)
    | symbolVar (name : Nat) (hole : Bool)
    | function (argument result : ValueCode) (argumentEffect resultEffect : SourcePort)
    | tuple (elements : TupleCode)
  inductive TupleCode where
    | nil
    | cons (head : ValueCode) (tail : TupleCode)
end

structure ValueDecoded (c : Context) (p : Bool) (s : State) where
  shape : Shape
  entries : List Retained
  state : State
  births : List Nat
  events : ValueEvents c p s shape entries state births

structure TupleDecoded (c : Context) (p : Bool) (s : State) where
  elements : List Shape
  entries : List Retained
  state : State
  births : List Nat
  events : TupleEvents c p s elements entries state births

mutual
  def decodeValue (c : Context) (p : Bool) (s : State) : ValueCode → Option (ValueDecoded c p s)
    | .scalar identity => some ⟨.atom identity, [], s, [], .scalar p s identity⟩
    | .symbolVar name hole => some ⟨.atom (scopedValue s c.scope name hole).1, [],
        (scopedValue s c.scope name hole).2, [], .symbolVar p s name hole⟩
    | .function argument result ae re => do
        let a ← decodeValue c (!p) s argument
        let r ← decodeValue c p a.state result
        let ao ← decodePort c (!p) ae r.state
        let ro ← decodePort c p re ao.out.state
        pure ⟨.function a.shape ao.out.ports r.shape ro.out.ports,
          prependPath .argument a.entries ++ prependPath .result r.entries ++
            atPort .argument ao.out.entries ++ atPort .result ro.out.entries,
          ro.out.state, a.births ++ r.births ++ ao.births ++ ro.births,
          .function a.events r.events ao.event ro.event⟩
    | .tuple elements => do
        let children ← decodeTuple c p s elements
        if nonempty : children.elements ≠ [] then
          pure ⟨.tuple children.elements, children.entries, children.state, children.births,
            .tuple children.events nonempty⟩
        else none
  def decodeTuple (c : Context) (p : Bool) (s : State) : TupleCode → Option (TupleDecoded c p s)
    | .nil => some ⟨[], [], s, [], .nil p s⟩
    | .cons head tail => do
        let first ← decodeValue c p s head
        let rest ← decodeTuple c p first.state tail
        pure ⟨first.shape :: rest.elements, prependPath (.element 0) first.entries ++ shift rest.entries,
          rest.state, first.births ++ rest.births, .cons first.events rest.events⟩
end

theorem decoded_origins (c : Context) (p : Bool) (s : State) (code : ValueCode)
    (out : ValueDecoded c p s) (_decoded : decodeValue c p s code = some out) :
    ∀ entry ∈ out.entries,
      Origin out.shape p entry.path entry.allocatedRow entry.metadata ∧
      Owned c entry.metadata ∧ entry.allocatedRow ∈ out.births :=
  event_origins_and_births out.events

theorem decoded_catalog (c : Context) (s : State) (code : ValueCode)
    (out : ValueDecoded c false s) (_decoded : decodeValue c false s code = some out) :
    projectAll out.shape out.entries = some (out.entries.map (fun e =>
      ⟨e.metadata, e.path, image out.shape (.effect (.row e.allocatedRow) false)⟩)) :=
  event_catalog_export out.events

/-- Keeps the definition wrapper distinct from other source-root encodings. -/
inductive OwnerKey where
  | definition (identity : Nat)
  | other (identity : Nat)
  deriving DecidableEq, Repr

/-- Snapshot DATA. Native extraction and correspondence of both tables are OPEN.
No canonical-image equality or export proposition is an input. -/
structure CaptureSnapshot where
  capture : Nat
  root : Nat
  representatives : List (Nat × Nat)
  nodes : List ((Nat × Bool) × Nat)
  deriving DecidableEq, Repr

def representative (snapshot : CaptureSnapshot) (row : Nat) : Nat :=
  ((snapshot.representatives.find? (fun pair => pair.1 == row)).map Prod.snd).getD row

def nodeFor (snapshot : CaptureSnapshot) (row : Nat) : Option Nat :=
  (snapshot.nodes.find? (fun pair => pair.1 == (row, false))).map Prod.snd

structure Observation where
  lineage : Nat
  owner : OwnerKey
  metadata : Metadata
  path : List Step
  originalRow : Nat
  canonicalRow : Nat
  positive : Bool
  capture : Nat
  root : Nat
  internNode : Nat
  returnedPort : Nat
  deriving DecidableEq, Repr

/-- Computed expected record for each source-order entry; no row-distinctness
premise. Equal rows do not collapse original lineages or paths. -/
def expected (c : Context) (snapshot : CaptureSnapshot) (lineage : Nat)
    (entry : Retained) : Option Observation := do
  let q := representative snapshot entry.allocatedRow
  let node ← nodeFor snapshot q
  pure ⟨lineage, .definition c.owner, entry.metadata, entry.path,
    entry.allocatedRow, q, false, snapshot.capture, snapshot.root, node, node⟩

theorem expected_fields {c : Context} {snapshot : CaptureSnapshot} {lineage : Nat}
    {entry : Retained} {observation : Observation}
    (decoded : expected c snapshot lineage entry = some observation) :
    observation.metadata = entry.metadata ∧ observation.path = entry.path ∧
      observation.originalRow = entry.allocatedRow ∧
      observation.canonicalRow = representative snapshot entry.allocatedRow ∧
      observation.owner = .definition c.owner ∧ observation.positive = false := by
  unfold expected at decoded
  cases found : nodeFor snapshot (representative snapshot entry.allocatedRow) with
  | none => simp [found] at decoded
  | some node =>
      simp [found] at decoded
      cases decoded
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def expectedAll (c : Context) (snapshot : CaptureSnapshot) : Nat → List Retained → Option (List Observation)
  | _, [] => some []
  | n, entry :: rest => do
      let first ← expected c snapshot n entry
      let remaining ← expectedAll c snapshot (n + 1) rest
      pure (first :: remaining)

/-- A finite record-consistency decoder. Acceptance is not native authenticity. -/
def observationsMatch (c : Context) (snapshot : CaptureSnapshot)
    (entries : List Retained) (observations : List Observation) : Bool :=
  expectedAll c snapshot 0 entries == some observations

theorem observations_match_iff (c : Context) (snapshot : CaptureSnapshot)
    (entries : List Retained) (observations : List Observation) :
    observationsMatch c snapshot entries observations = true ↔
      expectedAll c snapshot 0 entries = some observations := by
  simp [observationsMatch]

/-- Decoder uses raw code to compute a history before checking observations. -/
def decodeObserved (c : Context) (s : State) (code : ValueCode)
    (snapshot : CaptureSnapshot) (observations : List Observation) : Option (ValueDecoded c false s) := do
  let out ← decodeValue c false s code
  if observationsMatch c snapshot out.entries observations then pure out else none

theorem observed_origins {c : Context} {s : State} {code : ValueCode}
    {snapshot : CaptureSnapshot} {observations : List Observation} {out : ValueDecoded c false s}
    (_decoded : decodeObserved c s code snapshot observations = some out) :
    ∀ entry ∈ out.entries,
      Origin out.shape false entry.path entry.allocatedRow entry.metadata ∧
      Owned c entry.metadata ∧ entry.allocatedRow ∈ out.births :=
  event_origins_and_births out.events

/-- Exact offset arithmetic remains separate from constructor/capture identity. -/
def parameterRow (base parameter : Nat) : Nat := base + parameter

theorem parameter_row_equation (base parameter : Nat) :
    parameterRow base parameter = base + parameter := rfl

/-- Finite mathematical regression fixture, not a recorded Rust execution. -/
def fixtureContext : Context := ⟨0, 5, 7, 11⟩
def fixtureEntries : List Retained :=
  [⟨fixtureContext.metadata 20 [3], [.element 0, .result], 10⟩,
   ⟨fixtureContext.metadata 21 [3], [.element 1, .result], 12⟩]
def fixtureSnapshot : CaptureSnapshot := ⟨30, 40, [(10, 9), (12, 8)], [((9, false), 50), ((8, false), 51)]⟩
def fixtureObservations : List Observation :=
  [⟨0, .definition 7, fixtureContext.metadata 20 [3], [.element 0, .result], 10, 9, false, 30, 40, 50, 50⟩,
   ⟨1, .definition 7, fixtureContext.metadata 21 [3], [.element 1, .result], 12, 8, false, 30, 40, 51, 51⟩]

theorem fixture_accepts : observationsMatch fixtureContext fixtureSnapshot fixtureEntries fixtureObservations = true := by decide

theorem wrong_owner_rejected : observationsMatch fixtureContext fixtureSnapshot fixtureEntries
    (fixtureObservations.map (fun o => {o with owner := .other 7})) = false := by decide

theorem missing_second_rejected : observationsMatch fixtureContext fixtureSnapshot fixtureEntries
    (fixtureObservations.take 1) = false := by decide

theorem swapped_ports_rejected : observationsMatch fixtureContext fixtureSnapshot fixtureEntries
    (fixtureObservations.map (fun o => {o with returnedPort := if o.lineage = 0 then 51 else 50})) = false := by decide

theorem lost_transport_rejected : observationsMatch fixtureContext fixtureSnapshot fixtureEntries
    (fixtureObservations.map (fun o => {o with canonicalRow := o.originalRow})) = false := by decide

end
end YulangClosure.FormalPermissionExportWitness
