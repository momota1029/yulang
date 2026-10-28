import YulangClosure.FormalPermissionLiveCapture

/-!
Successful constructor recurrence for candidate_effect.rs. Source identifiers
are encoded by Nat; their decoding/authentication is a separate Rust bridge.
Scoped memo lookups are computed, never supplied as a free result. Covariant
explicit ports perform BOTH signature-effect allocations and share a view.
Only successful formal Function/Tuple/leaf construction is represented here;
this is not a proof of source preflight, constraints, capture completion or
whole-language effect hygiene. In particular the capture request extractor
below is a finite frozen store, whose agreement with Rust remains OPEN.
-/
namespace YulangClosure.FormalPermissionSourceOrigin

open FormalPermissionCaptureConstruction
open FormalPermissionLiveCapture (prependPath atPort shift shiftPath shifted_tuple_origin)
noncomputable section

structure Context where
  parameter : Nat
  occurrence : Nat
  owner : Nat
  scope : Nat
  deriving DecidableEq, Repr

def Context.metadata (c : Context) (position : Nat) (concrete : List Nat) : Metadata :=
  ⟨c.parameter, c.occurrence, c.owner, c.scope, position, concrete⟩

structure ViewData where
  owner : Nat
  scope : Nat
  position : Nat
  concrete : List Nat
  tail : Option Nat
  deriving DecidableEq, Repr

structure State where
  nextValue : Nat := 0
  nextEffect : Nat := 0
  nextView : Nat := 0
  values : Nat × Nat → Option Nat := fun _ => none
  holes : Nat × Nat → Option Nat := fun _ => none
  effects : Nat × Nat → Option Nat := fun _ => none
  views : Nat → Option Nat := fun _ => none
  viewData : Nat → Option ViewData := fun _ => none

def memo (table : Nat × Nat → Option Nat) (key : Nat × Nat) (next : Nat) :
    Nat × (Nat × Nat → Option Nat) × Nat :=
  match table key with
  | some row => (row, table, next)
  | none => (next, fun k => if k = key then some next else table k, next + 1)

theorem memo_hit (table : Nat × Nat → Option Nat) (key : Nat × Nat) (next row : Nat)
    (found : table key = some row) : memo table key next = (row, table, next) := by
  simp [memo, found]

theorem memo_miss (table : Nat × Nat → Option Nat) (key : Nat × Nat) (next : Nat)
    (fresh : table key = none) :
    (memo table key next).1 = next ∧ (memo table key next).2.2 = next + 1 ∧
      (memo table key next).2.1 key = some next := by
  simp [memo, fresh]

def scopedEffect (s : State) (scope name : Nat) : Nat × State :=
  let (row, table, next) := memo s.effects (scope, name) s.nextEffect
  (row, {s with effects := table, nextEffect := next})

def scopedValue (s : State) (scope name : Nat) (hole : Bool) : Nat × State :=
  let table := if hole then s.holes else s.values
  let (row, table, next) := memo table (scope, name) s.nextValue
  (row, if hole then {s with holes := table, nextValue := next}
        else {s with values := table, nextValue := next})

structure SignatureBound where
  row : Nat
  positive : Bool
  view : Nat
  tail : Option Nat
  deriving DecidableEq, Repr

/-- Annotation context, explicit row, positive variance, no operation family.
The view cache is local to this formal annotation; effects are scope-keyed.
Successful allocation/bound insertion is represented; refusal is not hidden. -/
def signatureEffect (c : Context) (position : Nat) (concrete : List Nat) (symbolVar : Option Nat)
    (positive : Bool) (s : State) : Nat × SignatureBound × State :=
  let (tail, s) := match symbolVar with
    | none => (none, s)
    | some name => let (row, s) := scopedEffect s c.scope name; (some row, s)
  let (view, s) := match s.views position with
    | some view => (view, s)
    | none => (s.nextView, {s with nextView := s.nextView + 1, views := fun p => if p = position then some s.nextView else s.views p, viewData := fun i => if i = s.nextView then some ⟨c.owner, c.scope, position, concrete, tail⟩ else s.viewData i})
  (s.nextEffect, ⟨s.nextEffect, positive, view, tail⟩,
    {s with nextEffect := s.nextEffect + 1})

def signaturePair (c : Context) (position : Nat) (concrete : List Nat) (symbolVar : Option Nat) (s : State) :
    Ports × List SignatureBound × State :=
  let (positive, pb, s) := signatureEffect c position concrete symbolVar true s
  let (negative, nb, s) := signatureEffect c position concrete symbolVar false s
  (⟨.row positive, .row negative, none⟩, [pb, nb], s)

/-- A covariant explicit pair consumes two rows even when the view already
exists. This concrete closed-row specialization exposes the earlier missing
allocation recurrence without assuming a delegated result. -/
theorem signature_pair_closed_allocation (c : Context) (position : Nat) (concrete : List Nat) (s : State) :
    (signaturePair c position concrete none s).1.positive = .row s.nextEffect ∧
    (signaturePair c position concrete none s).1.negative = .row (s.nextEffect + 1) ∧
    (signaturePair c position concrete none s).2.2.nextEffect = s.nextEffect + 2 := by
  unfold signaturePair signatureEffect
  cases h : s.views position <;> simp [h, Nat.add_assoc]

inductive SourcePort where
  | omitted
  | symbolic (name : Nat)
  | explicit (position : Nat) (concrete : List Nat) (symbolVar : Option Nat)
  deriving DecidableEq, Repr

structure PortResult where
  ports : Ports
  entries : List FormalPermissionLiveCapture.Emission
  bounds : List SignatureBound
  state : State

/-- The successful branches of candidate_formal_effect_port. Invalid negative
empty/mixed explicit rows return none. Multiple symbolic variables have no
encoding here and remain an explicit source-decoding/refusal obligation. -/
def constructPort (c : Context) (positive : Bool) (source : SourcePort) (s : State) :
    Option PortResult :=
  match source with
  | .omitted => some ⟨sharedPorts s.nextEffect, [], [],
      {s with nextEffect := s.nextEffect + 1}⟩
  | .symbolic name =>
      let (row, t) := scopedEffect s c.scope name
      some ⟨sharedPorts row, [], [], t⟩
  | .explicit position concrete symbolVar =>
      if concrete = [] ∧ symbolVar ≠ none then
        match symbolVar with
        | none => none
        | some name => let (row, t) := scopedEffect s c.scope name
                       some ⟨sharedPorts row, [], [], t⟩
      else if positive then
        let (ports, bounds, t) := signaturePair c position concrete symbolVar s
        some ⟨ports, [], bounds, t⟩
      else if concrete ≠ [] ∧ symbolVar = none then
        let metadata := c.metadata position concrete
        some ⟨sharedPorts s.nextEffect (some metadata), [⟨metadata, s.nextEffect⟩], [],
          {s with nextEffect := s.nextEffect + 1}⟩
      else none

def Owned (c : Context) (metadata : Metadata) : Prop :=
  metadata.parameter = c.parameter ∧ metadata.occurrence = c.occurrence ∧
    metadata.owner = c.owner ∧ metadata.scope = c.scope

theorem port_origin {c : Context} {p : Bool} {source : SourcePort} {s : State}
    {out : PortResult} (built : constructPort c p source s = some out)
    {entry : FormalPermissionLiveCapture.Emission} (member : entry ∈ out.entries) :
    p = false ∧ out.ports = sharedPorts entry.row (some entry.metadata) ∧
      entry.row = s.nextEffect ∧ entry.metadata.concrete ≠ [] ∧ Owned c entry.metadata := by
  cases source with
  | omitted => simp [constructPort] at built; cases built; simp at member
  | symbolic name => simp [constructPort] at built; cases built; simp at member
  | explicit position concrete symbolVar =>
      by_cases symbolic : concrete = [] ∧ symbolVar ≠ none
      · cases symbolVar with
        | none => exact False.elim (symbolic.2 rfl)
        | some name =>
            simp [constructPort, symbolic] at built
            cases built
            simp at member
      · cases p with
        | true => simp [constructPort, symbolic] at built; cases built; simp at member
        | false =>
            by_cases allowed : concrete ≠ [] ∧ symbolVar = none
            · simp [constructPort, symbolic, allowed] at built
              cases built
              simp only [List.mem_singleton] at member
              subst entry
              exact ⟨rfl, rfl, rfl, allowed.1, rfl, rfl, rfl, rfl⟩
            · simp [constructPort, symbolic, allowed] at built

mutual
  /-- Each recursive child uses the same source owner/scope/parameter and
  occurrence; argument variance reverses. Function order is value argument,
  value result, effect argument, effect result. Scalar encodings are opaque. -/
  inductive Construction (c : Context) : Bool → State → Shape → List Retained → State → Prop where
    | scalar (p : Bool) (s : State) (identity : Nat) :
        Construction c p s (.atom identity) [] s
    | symbolVar (p : Bool) (s : State) (name : Nat) (hole : Bool) :
        Construction c p s (.atom (scopedValue s c.scope name hole).1) []
          (scopedValue s c.scope name hole).2
    | function {p : Bool} {s s₁ s₂ : State} {a r : Shape} {as rs : List Retained}
        {ae re : SourcePort} {ao ro : PortResult}
        (argument : Construction c (!p) s a as s₁)
        (result : Construction c p s₁ r rs s₂)
        (argumentEffect : constructPort c (!p) ae s₂ = some ao)
        (resultEffect : constructPort c p re ao.state = some ro) :
        Construction c p s (.function a ao.ports r ro.ports)
          (prependPath .argument as ++ prependPath .result rs ++
            atPort .argument ao.entries ++ atPort .result ro.entries) ro.state
    | tuple {p : Bool} {s t : State} {elements : List Shape} {entries : List Retained}
        (children : TupleConstruction c p s elements entries t) (nonempty : elements ≠ []) :
        Construction c p s (.tuple elements) entries t
  inductive TupleConstruction (c : Context) : Bool → State → List Shape → List Retained → State → Prop where
    | nil (p : Bool) (s : State) : TupleConstruction c p s [] [] s
    | cons {p : Bool} {s middle t : State} {head : Shape} {tail : List Shape}
        {first rest : List Retained}
        (child : Construction c p s head first middle)
        (remaining : TupleConstruction c p middle tail rest t) :
        TupleConstruction c p s (head :: tail)
          (prependPath (.element 0) first ++ shift rest) t
end

mutual
  theorem construction_origins {c : Context} {p : Bool} {s t : State} {shape : Shape}
      {entries : List Retained} (built : Construction c p s shape entries t) :
      ∀ entry ∈ entries, Origin shape p entry.path entry.allocatedRow entry.metadata ∧
        Owned c entry.metadata := by
    cases built with
    | scalar => simp
    | symbolVar => simp
    | @function p s s₁ s₂ a r as rs ae re ao ro argument result argEffect resEffect =>
        intro entry member
        simp only [List.mem_append] at member
        rcases member with ((first | second) | third) | fourth
        · obtain ⟨e, mem, rfl⟩ := List.mem_map.mp first
          obtain ⟨origin, owned⟩ := construction_origins argument e mem
          exact ⟨.inArgument origin, owned⟩
        · obtain ⟨e, mem, rfl⟩ := List.mem_map.mp second
          obtain ⟨origin, owned⟩ := construction_origins result e mem
          exact ⟨.inResult origin, owned⟩
        · obtain ⟨e, mem, rfl⟩ := List.mem_map.mp third
          obtain ⟨negative, same, _, _, owned⟩ := port_origin argEffect mem
          cases p with
          | false => simp at negative
          | true => rw [same]; exact ⟨.argument a r ro.ports e.row e.metadata, owned⟩
        · obtain ⟨e, mem, rfl⟩ := List.mem_map.mp fourth
          obtain ⟨negative, same, _, _, owned⟩ := port_origin resEffect mem
          cases p with
          | true => simp at negative
          | false => rw [same]; exact ⟨.result a r ao.ports e.row e.metadata, owned⟩
    | tuple children _ => exact tuple_construction_origins children
  theorem tuple_construction_origins {c : Context} {p : Bool} {s t : State}
      {elements : List Shape} {entries : List Retained}
      (built : TupleConstruction c p s elements entries t) :
      ∀ entry ∈ entries, Origin (.tuple elements) p entry.path entry.allocatedRow entry.metadata ∧
        Owned c entry.metadata := by
    cases built with
    | nil => simp
    | cons child remaining =>
        intro entry member
        rcases List.mem_append.mp member with first | rest
        · obtain ⟨e, mem, rfl⟩ := List.mem_map.mp first
          obtain ⟨origin, owned⟩ := construction_origins child e mem
          exact ⟨.inElement rfl origin, owned⟩
        · obtain ⟨e, mem, rfl⟩ := List.mem_map.mp rest
          obtain ⟨origin, owned⟩ := tuple_construction_origins remaining e mem
          exact ⟨shifted_tuple_origin origin, owned⟩
end

theorem constructed_catalog_export {c : Context} {s t : State} {shape : Shape}
    {entries : List Retained} (built : Construction c false s shape entries t) :
    projectAll shape entries = some (entries.map (fun e =>
      ⟨e.metadata, e.path, image shape (.effect (.row e.allocatedRow) false)⟩)) :=
  constructor_list_export shape entries (fun e member => (construction_origins built e member).1)

/-- The parameter ordinal and its allocated value row are different coordinates.
Successful checked_add/u32 conversion in Rust must decode to this equation. -/
structure Domain where
  context : Context
  parameterBase : Nat
  shape : Shape

def Domain.liveRow (d : Domain) : Nat := d.parameterBase + d.context.parameter
def Domain.negativeRoot (d : Domain) : Endpoint := .value d.shape false

theorem parameter_capture_identity (d : Domain) :
    d.liveRow = d.parameterBase + d.context.parameter ∧
      d.negativeRoot = .value d.shape false := ⟨rfl, rfl⟩

/-- Discovery is indexed by its real origin category, with frozen request
lists. The extraction of these lists from actual row/bound/evidence/context
stores, and loop-cursor ordering across categories, remains an OPEN bridge. -/
structure DiscoveryStore where
  row : Nat → List Endpoint
  bound : Nat → List Endpoint
  evidence : Nat → List Endpoint
  context : Nat → List Endpoint

inductive Discovery where
  | row | bound | evidence | context
  deriving DecidableEq, Repr

def Discovery.requests (store : DiscoveryStore) (kind : Discovery) (index : Nat) : List Endpoint :=
  match kind with
  | .row => store.row index
  | .bound => store.bound index
  | .evidence => store.evidence index
  | .context => store.context index

structure Live where
  capture : FormalPermissionLiveCapture.Capture
  writes : List (Nat × Node) := []

/-- Node indices are computed AFTER child interning, as in expand_node.
Pending uses list-head pop, the reverse of the Rust Vec. Each write records
the exact assigned index and structural node; this is a write log. Row nodes
still carry raw row keys from the prior catalog model, not Rust graph-row
indices. Effect views with tails are not expanded by this structural slice.
Exact row interning, tail discovery and completed-graph interpretation are OPEN. -/
def Live.popWrite (canon : Endpoint → Endpoint) (s : Live) : Option Live :=
  match s.capture.pending with
  | [] => none
  | endpoint :: rest =>
      let base : FormalPermissionLiveCapture.Capture :=
        {s.capture with pending := rest, expanded := s.capture.expanded ++ [endpoint]}
      let next := base.internAll canon (children endpoint)
      let node := expand (fun child => next.index (canon child)) endpoint
      some ⟨next, s.writes ++ [(s.capture.index endpoint, node)]⟩

theorem pop_write_lifo (canon : Endpoint → Endpoint) (s : Live) (e : Endpoint)
    (rest : List Endpoint) (pending : s.capture.pending = e :: rest) :
    s.popWrite canon = some ⟨
      ({s.capture with pending := rest, expanded := s.capture.expanded ++ [e]} :
        FormalPermissionLiveCapture.Capture).internAll canon (children e),
      s.writes ++ [(s.capture.index e,
        expand (fun child =>
          (({s.capture with pending := rest, expanded := s.capture.expanded ++ [e]} :
            FormalPermissionLiveCapture.Capture).internAll canon (children e)).index (canon child)) e)]⟩ := by
  simp only [Live.popWrite, pending]

def Live.discover (canon : Endpoint → Endpoint) (store : DiscoveryStore)
    (kind : Discovery) (index : Nat) (s : Live) : Live :=
  {s with capture := s.capture.internAll canon (kind.requests store index)}

theorem discovery_membership (canon : Endpoint → Endpoint) (store : DiscoveryStore)
    (kind : Discovery) (index : Nat) (s : Live) (e : Endpoint)
    (requested : e ∈ kind.requests store index) :
    canon e ∈ (s.discover canon store kind index).capture.keys :=
  (FormalPermissionLiveCapture.mem_internAll_keys canon _ _ _).mpr
    (.inr (List.mem_map.mpr ⟨e, requested, rfl⟩))

/-- Publication is about the exact retained negative term key. Canonical
transport must therefore fix that key (or supply an independently proved
equivalent lookup), and its membership must be shown separately. -/
theorem canonical_function_publication (canon : Endpoint → Endpoint)
    (s : FormalPermissionLiveCapture.Capture) (a r : Shape) (ae re : Ports)
    (fixed : canon (.value (.function a ae r re) false) =
      .value (.function a ae r re) false)
    (arrived : canon (.value (.function a ae r re) false) ∈ s.keys) :
    FormalPermissionLiveCapture.publish s (.function a ae r re) =
      some (s.index (canon (.value (.function a ae r re) false))) := by
  rw [fixed] at arrived ⊢
  exact (FormalPermissionLiveCapture.publish_function_iff _ _ _ _ _ _).mpr ⟨arrived, rfl⟩

/-- Both endpoints can have the same out-of-range idxOf when neither exists.
Thus index equality alone is not a root/port membership or export theorem. -/
theorem empty_indices_no_arrival (first second : Endpoint) :
    ([] : List Endpoint).idxOf first = ([] : List Endpoint).idxOf second ∧
      first ∉ ([] : List Endpoint) := by simp

end
end YulangClosure.FormalPermissionSourceOrigin
