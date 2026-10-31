import YulangClosure.SourceInternalContextR55

/-! R57 owner-local primitive construction. No existing Context/Inputs is an
input to the constructor. Runtime extraction and original source soundness
remain independent obligations. Source keys retain their full branded payload. -/
namespace YulangClosure.ProviderNativeContextR57


inductive ValueEndpoint (Term : Type) where
  | bottomPositive | bottomNegative | topNegative
  | intPositive | intNegative | unitPositive | boolPositive | strPositive
  | unitNegative | boolNegative | strNegative | row (ordinal : Nat)
  | positiveFunction (term : Term) | negativeFunction (term : Term)
  | positiveVariant (term : Term) | negativeVariant (term : Term)
  | positiveRecord (term : Term) | negativeRecord (term : Term)
  | positiveTuple (term : Term) (arity : Nat) | negativeTuple (term : Term) (arity : Nat)
  deriving DecidableEq
inductive EffectEndpoint where
  | bottomPositive | emptyNegative | contribution (index : Nat) | allowance (index : Nat)
  | support (view : Nat) | annotationMember (view ordinal : Nat) | row (ordinal : Nat)
  deriving DecidableEq
inductive Key (Source Term : Type) where
  | source (key : Source)
  | valueRow (state ordinal : Nat) | effectRow (state ordinal : Nat)
  | valueAtom (state : Nat) (endpoint : ValueEndpoint Term)
  | effectAtom (state : Nat) (endpoint : EffectEndpoint)
  deriving DecidableEq
inductive Fact where
  | semantic (store index : Nat) | collected (batch index : Nat)
  deriving DecidableEq
inductive Endpoint (Term : Type) where
  | value (endpoint : ValueEndpoint Term) | effect (endpoint : EffectEndpoint)
  deriving DecidableEq

def endpoint {S T : Type} (state : Nat) : Endpoint T → CurrentEmissionOwnershipR47.Endpoint (Key S T)
  | .value (.row index) => .valueRow (.valueRow state index)
  | .effect (.row index) => .effectRow (.effectRow state index)
  | .value item => .valueAtom (.valueAtom state item)
  | .effect item => .effectAtom (.effectAtom state item)

inductive Row where | value (index : Nat) | effect (index : Nat) deriving DecidableEq
inductive Polarity where | positive | negative deriving DecidableEq
inductive Lane where
  | valueLowerRow | valueUpperRow | valueLowerAtom | valueUpperAtom
  | effectLowerRow | effectUpperRow | effectLowerAtom | effectUpperAtom
  deriving DecidableEq
structure Bound (T : Type) where
  owner : Row
  polarity : Polarity
  item : Endpoint T
  deriving DecidableEq
structure Slot where
  owner : Row
  lane : Lane
  index : Nat
  deriving DecidableEq
structure Admission (T : Type) where
  state : Nat
  bound : Bound T
  relation : Option Nat
  deriving DecidableEq
structure Emission (T : Type) where
  state : Nat
  admission : Nat
  bound : Bound T
  physical : Slot
  readbackSlot : Slot
  readbackBound : Bound T
  deriving DecidableEq
structure Physical (T : Type) where
  admissionIndex : Nat
  emissionIndex : Nat
  admission : Admission T
  emission : Emission T
  relation : Nat
  ancestry : List Nat
  deriving DecidableEq
structure Bounds (A : Type) where
  lowerRows : List Nat
  upperRows : List Nat
  lowerAtoms : List A
  upperAtoms : List A
structure ValueRow (T : Type) where
  state : Nat
  index : Nat
  canonical : Nat
  bounds : Bounds (ValueEndpoint T)
structure EffectRow where
  state : Nat
  index : Nat
  canonical : Nat
  bounds : Bounds EffectEndpoint
structure Relation (T : Type) where
  state : Nat
  index : Nat
  lower : Endpoint T
  upper : Endpoint T
structure Dependency where
  state : Nat
  parent : Nat
  child : Nat
structure SourceFact (S T : Type) where
  identity : Fact
  occurrence : S
  slot : Nat
  rawLower : Endpoint T
  rawUpper : Endpoint T
  canonicalLower : Endpoint T
  canonicalUpper : Endpoint T
structure Drain (S T : Type) where
  state : Nat
  originIndex : Nat
  createdSeed : Nat
  selectedRelation : Nat
  cause : S
  slot : Nat
  taskLower : Endpoint T
  taskUpper : Endpoint T
  incoming : Option Nat
  replay : Bool
  completed : Bool
structure Origin (S T : Type) where
  state : Nat
  relation : Nat
  occurrence : S
  slot : Nat
  drain : Option (Drain S T)
inductive ViewOrigin (S : Type) where | annotation | operation (occurrence declaration : S) deriving DecidableEq
structure View (S : Type) where
  state : Nat
  index : Nat
  origin : ViewOrigin S
  position : S
  allowed : List S
  tail : Option Nat
  deriving DecidableEq
structure Operation (S : Type) where
  occurrence : S
  declaration : S
  family : S

variable {S T : Type} [DecidableEq S] [DecidableEq T]

def row (state : Nat) : Row → CurrentEmissionOwnershipR47.RowKey (Key S T)
  | .value index => .value (.valueRow state index)
  | .effect index => .effect (.effectRow state index)
def polarity : Polarity → CurrentEmissionOwnershipR47.Polarity | .positive => .positive | .negative => .negative
def lane : Lane → CurrentEmissionOwnershipR47.Lane
  | .valueLowerRow => .valueLowerRow | .valueUpperRow => .valueUpperRow
  | .valueLowerAtom => .valueLowerAtom | .valueUpperAtom => .valueUpperAtom
  | .effectLowerRow => .effectLowerRow | .effectUpperRow => .effectUpperRow
  | .effectLowerAtom => .effectLowerAtom | .effectUpperAtom => .effectUpperAtom
def bound (state : Nat) (b : Bound T) : CurrentEmissionOwnershipR47.Bound (Key S T) := ⟨row state b.owner, polarity b.polarity, endpoint state b.item⟩
def slot (state : Nat) (s : Slot) : CurrentEmissionOwnershipR47.Slot (Key S T) := ⟨row state s.owner, lane s.lane, s.index⟩
def admission (a : Admission T) : CurrentEmissionOwnershipR47.Admission (Key S T) := ⟨bound a.state a.bound, a.relation⟩
def emission (e : Emission T) : CurrentEmissionOwnershipR47.Emission (Key S T) :=
  ⟨e.admission, bound e.state e.bound, slot e.state e.physical,
    ⟨slot e.state e.readbackSlot, bound e.state e.readbackBound⟩⟩
def physical (p : Physical T) : CurrentEmissionOwnershipR47.Probe (Key S T) :=
  ⟨p.admissionIndex, p.emissionIndex, admission p.admission, emission p.emission, p.relation, p.ancestry⟩
def view (v : View S) : ProviderEntryArrivalR48.View (Key S T) :=
  ⟨match v.origin with | .annotation => .annotation | .operation occurrence declaration => .operation (.source occurrence) (.source declaration),
    .source v.position, v.allowed.map Key.source, v.tail.map (Key.effectRow v.state)⟩
def valueBounds (state : Nat) (b : Bounds (ValueEndpoint T)) : CurrentEmissionOwnershipR47.RowBounds (Key S T) :=
  ⟨b.lowerRows.map (Key.valueRow state), b.upperRows.map (Key.valueRow state),
    b.lowerAtoms.map (Key.valueAtom state), b.upperAtoms.map (Key.valueAtom state)⟩
def effectBounds (state : Nat) (b : Bounds EffectEndpoint) : CurrentEmissionOwnershipR47.RowBounds (Key S T) :=
  ⟨b.lowerRows.map (Key.effectRow state), b.upperRows.map (Key.effectRow state),
    b.lowerAtoms.map (Key.effectAtom state), b.upperAtoms.map (Key.effectAtom state)⟩

/-- Full owner inventories, assembled before provider/path selection. Directed
dependencies are (parent,child), including both replay parents. -/
structure Native (S T : Type) where
  artifact : Nat
  state : Nat
  store : Nat
  batch : Nat
  entryRow : Nat
  entryRoot : Nat
  admissions : List (Admission T)
  emissions : List (Emission T)
  valueRows : List (ValueRow T)
  effectRows : List EffectRow
  relations : List (Relation T)
  dependencies : List Dependency
  origins : List (Origin S T)
  facts : List (SourceFact S T)
  views : List (View S)
  operations : List (Operation S)

def unique {A : Type} (test : A → Bool) (xs : List A) : Option A := SourceInternalContextR55.unique test xs
def factRead (n : Native S T) (id : Fact) : Option (SourceFact S T) := unique (fun f => decide (f.identity = id)) n.facts
def sourceFact (n : Native S T) (key : Key S T × Nat) : Option Fact :=
  match key.1 with
  | .source occurrence => (unique (fun f => decide (f.occurrence = occurrence ∧ f.slot = key.2) &&
      match f.identity with | .collected owner _ => decide (owner = n.batch ∧ key.2 = 51)
                            | .semantic owner _ => decide (owner = n.store ∧ key.2 ≠ 51)) n.facts).map SourceFact.identity
  | _ => none
def relationRead (n : Native S T) (index : Nat) : Option (Relation T) :=
  unique (fun r => decide (r.state = n.state ∧ r.index = index)) n.relations
def originRead (n : Native S T) (relation : Nat) : Option (Origin S T) :=
  unique (fun o => decide (o.state = n.state ∧ o.relation = relation)) n.origins
def rootDrain (n : Native S T) (relation : Nat) : Option (Drain S T) := (originRead n relation).bind Origin.drain
def rootTask (n : Native S T) (relation : Nat) : Option Fact := do
  let d ← rootDrain n relation
  let id ← sourceFact n (.source d.cause, d.slot)
  let f ← factRead n id
  if d.taskLower = f.canonicalLower ∧ d.taskUpper = f.canonicalUpper then some id else none
def completed (n : Native S T) (relation : Nat) : Bool :=
  match originRead n relation, rootDrain n relation with
  | some o, some d => decide (d.state = n.state ∧
      (n.origins[d.originIndex]?).isSome ∧
      ((n.origins[d.originIndex]?).map Origin.relation = some o.relation) ∧ d.createdSeed = o.relation ∧
      d.selectedRelation = o.relation ∧ d.incoming = none ∧ d.replay = false ∧
      d.cause = o.occurrence ∧ d.slot = o.slot) && d.completed
  | _, _ => false
def dependencies (n : Native S T) : List (Nat × Nat) :=
  (n.dependencies.filter (fun d => decide (d.state = n.state))).map (fun d => (d.parent, d.child))
def rootCandidates (n : Native S T) (u : InternalPermissionIncidenceR45.UseId Nat (Key S T)) (id : Fact) : List Nat :=
  match u.occurrence, factRead n id with
  | .source occurrence, some f => if u.artifact = n.artifact then
      (n.origins.filter (fun o => decide (o.state = n.state ∧ o.occurrence = occurrence ∧ o.slot = 0) &&
        match relationRead n o.relation with
        | some r => decide (r.lower = f.canonicalLower ∧ r.upper = f.canonicalUpper)
        | none => false)).map Origin.relation else []
  | _, _ => []

def current (n : Native S T) : CurrentEmissionOwnershipR47.Inputs Nat (Key S T) Fact :=
  { artifact := n.artifact
    admissions := n.admissions.map admission
    emissions := n.emissions.map emission
    valueRows := fun key => match key with
      | .valueRow state index => (unique (fun r => decide (r.state = state ∧ state = n.state ∧ r.index = index)) n.valueRows).map
          (fun r => valueBounds r.state r.bounds)
      | _ => none
    effectRows := fun key => match key with
      | .effectRow state index => (unique (fun r => decide (r.state = state ∧ state = n.state ∧ r.index = index)) n.effectRows).map
          (fun r => effectBounds r.state r.bounds)
      | _ => none
    liveRelations := (n.relations.filter (fun r => decide (r.state = n.state))).map Relation.index
    dependencies := dependencies n
    relationPair := fun index => (relationRead n index).map (fun r => (endpoint n.state r.lower, endpoint n.state r.upper))
    rootSource := fun index => (originRead n index).map (fun o => (.source o.occurrence, o.slot))
    sourceFact := sourceFact n
    rootCandidates := rootCandidates n
    rootCause := fun index => (rootDrain n index).map (fun d => (.source d.cause, d.slot))
    rootTask := rootTask n
    rootCompleted := completed n }

def nativeAtom (n : Native S T) : Key S T → Option ProviderEntryArrivalR48.NativeAtom
  | .effectAtom state (.annotationMember v i) =>
      if state = n.state then
        ((unique (fun view => decide (view.state = state ∧ view.index = v)) n.views).bind
          (fun view => view.allowed[i]?)).map (fun _ => .annotationMember v i)
      else none
  | .effectAtom state _ => if state = n.state then some .other else none
  | .valueAtom state _ => if state = n.state then some .other else none
  | _ => none
def arrival (n : Native S T) : ProviderEntryArrivalR48.Inputs Nat (Key S T) Fact :=
  { current := current n
    catchCandidates := fun key => match key with
      | .source occurrence => (n.facts.filter (fun f => decide (f.occurrence = occurrence ∧ f.slot = 51) &&
          match f.identity with | .collected owner _ => decide (owner = n.batch) | _ => false)).map SourceFact.identity
      | _ => []
    factOrigin := fun id => (factRead n id).map (fun f => (.source f.occurrence, f.slot))
    factPair := fun id => (factRead n id).map (fun f => (endpoint n.state f.canonicalLower, endpoint n.state f.canonicalUpper))
    nativeAtom := nativeAtom n
    views := fun index => (unique (fun v => decide (v.state = n.state ∧ v.index = index)) n.views).map view
    sourceOperation := fun key => match key with
      | .source occurrence => (unique (fun o => decide (o.occurrence = occurrence)) n.operations).map
          (fun o => (.source o.declaration, .source o.family))
      | _ => none }

def operationOrigin (origin : ViewOrigin S) (provider declaration : Key S T) : Prop :=
  match origin with
  | .operation occurrence decl => provider = .source occurrence ∧ declaration = .source decl
  | .annotation => False
instance (origin : ViewOrigin S) (provider declaration : Key S T) :
    Decidable (operationOrigin origin provider declaration) := by
  cases origin <;> unfold operationOrigin <;> infer_instance

/-- Enumerate every member of every view, before singleton selection. -/
def providers (n : Native S T) (provider declaration family : Key S T) : List (Key S T) :=
  n.views.flatMap (fun v => (v.allowed.zipIdx).filterMap (fun (f, ordinal) =>
    if v.state = n.state ∧ operationOrigin v.origin provider declaration ∧ family = .source f
    then some (.effectAtom n.state (.annotationMember v.index ordinal)) else none))

theorem provider_inventory_coverage (n : Native S T) (provider declaration family : Key S T) (candidate : Key S T) :
    candidate ∈ providers n provider declaration family ↔
    ∃ v ∈ n.views, ∃ f ordinal, (f, ordinal) ∈ v.allowed.zipIdx ∧
      v.state = n.state ∧ operationOrigin v.origin provider declaration ∧ family = .source f ∧
      candidate = .effectAtom n.state (.annotationMember v.index ordinal) := by
  simp only [providers, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro ⟨v, member, x, position, found⟩
    rcases x with ⟨f, ordinal⟩
    split at found
    · rename_i checks
      exact ⟨v, member, f, ordinal, position, checks.1, checks.2.1, checks.2.2, (Option.some.inj found).symm⟩
    · contradiction
  · rintro ⟨v, member, f, ordinal, position, own, origin, family, rfl⟩
    exact ⟨v, member, (f, ordinal), position, by simp [own, origin, family]⟩

/- Path coverage is proved below for the finite owner inventory; the producer
must supply that complete inventory, not only its successful path. -/
structure Support (S : Type) where
  state : Nat
  viewIndex : Nat
  ordinal : Nat
  family : S
  view : View S
  deriving DecidableEq
inductive Step (S T : Type) where
  | physical (probe : Physical T)
  | support (member : Support S)
  deriving DecidableEq
def support (s : Support S) : AuthenticatedResidualConsumerR49.SupportMember (Key S T) :=
  ⟨.effectAtom s.state (.support s.viewIndex), .effectAtom s.state (.annotationMember s.viewIndex s.ordinal),
    s.viewIndex, s.ordinal, .source s.family, view s.view⟩
def step : Step S T → AuthenticatedResidualConsumerR49.Step (Key S T)
  | .physical p => .physical (physical p) | .support s => .supportMember (support s)
def stepRoot : Step S T → CurrentEmissionOwnershipR47.Endpoint (Key S T)
  | .physical p => CurrentEmissionOwnershipR47.rowEndpoint (row p.admission.state p.admission.bound.owner)
  | .support s => .effectAtom (.effectAtom s.state (.support s.viewIndex))
def stepNext (s : Step S T) : CurrentEmissionOwnershipR47.Endpoint (Key S T) := AuthenticatedResidualConsumerR49.next (step s)

def rowEndpoint : Row → Endpoint T
  | .value index => .value (.row index) | .effect index => .effect (.row index)
def rawPair (b : Bound T) : Endpoint T × Endpoint T :=
  match b.polarity with | .positive => (b.item, rowEndpoint b.owner) | .negative => (rowEndpoint b.owner, b.item)

/-- Choose an ancestry witness from the complete directed dependency graph.
Multiple ancestry witnesses are harmless: physical path identity uses one
canonical first witness, reconstructed identically for the entry probe. -/
def ancestry (dependencies : List (Nat × Nat)) : Nat → List Nat → Nat → Nat → Option (List Nat)
  | 0, _, root, target => if root = target then some [] else none
  | fuel+1, seen, root, target => if root = target then some [] else
      dependencies.foldl (fun found (parent, child) => found.orElse (fun _ =>
        if parent = root ∧ child ∉ seen then
          (ancestry dependencies fuel (child :: seen) child target).map (child :: ·) else none)) none

/-- Enumerate every physical lower slot, not only slots in a successful path. -/
def lowerSlots (n : Native S T) : List (Slot × Bound T) := n.effectRows.flatMap (fun r =>
  (r.bounds.lowerRows.zipIdx).map (fun (item, index) =>
    (⟨.effect r.index, .effectLowerRow, index⟩, ⟨.effect r.index, .positive, .effect (.row item)⟩)) ++
  (r.bounds.lowerAtoms.zipIdx).map (fun (item, index) =>
    (⟨.effect r.index, .effectLowerAtom, index⟩, ⟨.effect r.index, .positive, .effect item⟩)))

def physicalAt (n : Native S T) (expected : Slot × Bound T) : Option (Step S T) := do
  let (e, emissionIndex) ← unique (fun (e, _) => decide (e.state = n.state ∧ e.physical = expected.1)) n.emissions.zipIdx
  let a ← n.admissions[e.admission]?
  let relation ← a.relation
  let r ← relationRead n relation
  let ancestry ← if expected.1.owner = .effect n.entryRow then
    ancestry (dependencies n) n.relations.length [n.entryRoot] n.entryRoot relation else some []
  if a.state = n.state ∧ e.bound = expected.2 ∧ a.bound = expected.2 ∧
      e.readbackSlot = expected.1 ∧ e.readbackBound = expected.2 ∧ (r.lower, r.upper) = rawPair expected.2
  then some (.physical ⟨e.admission, emissionIndex, a, e, relation, ancestry⟩) else none

def collect {A B : Type} (f : A → Option B) : List A → Option (List B)
  | [] => some []
  | head :: rest => do let image ← f head; let tail ← collect f rest; pure (image :: tail)

theorem complete_owner_traversal {A B : Type} (f : A → Option B) (xs : List A) (ys : List B)
    (finished : collect f xs = some ys) (x : A) (member : x ∈ xs) :
    ∃ y ∈ ys, f x = some y := by
  induction xs generalizing ys with
  | nil => simp at member
  | cons head rest ih =>
    cases first : f head with
    | none => simp [collect, first] at finished
    | some image =>
      cases tail : collect f rest with
      | none => simp [collect, first, tail] at finished
      | some images =>
        have equal : image :: images = ys := by simpa [collect, first, tail] using finished
        subst ys
        rcases List.mem_cons.mp member with same | later
        · subst x; exact ⟨image, by simp, first⟩
        · obtain ⟨y, present, read⟩ := ih images tail later
          exact ⟨y, List.mem_cons_of_mem image present, read⟩

def supportEdges (n : Native S T) : List (Step S T) := n.views.flatMap (fun v =>
  if v.tail = none then v.allowed.zipIdx.map (fun (f, ordinal) =>
    .support ⟨v.state, v.index, ordinal, f, v⟩) else [])
def derivedEdges (n : Native S T) : Option (List (Step S T)) :=
  (collect (physicalAt n) (lowerSlots n)).map (fun physical => physical ++ supportEdges n)

omit [DecidableEq S] in
theorem every_physical_owner_slot (n : Native S T) (physical : List (Step S T))
    (finished : collect (physicalAt n) (lowerSlots n) = some physical)
    (coordinate : Slot × Bound T) (present : coordinate ∈ lowerSlots n) :
    ∃ edge ∈ physical ++ supportEdges n, physicalAt n coordinate = some edge := by
  obtain ⟨edge, member, read⟩ := complete_owner_traversal _ _ _ finished _ present
  exact ⟨edge, List.mem_append_left _ member, read⟩

omit [DecidableEq S] [DecidableEq T] in
theorem every_closed_support_member (n : Native S T) (v : View S) (f : S) (ordinal : Nat)
    (present : v ∈ n.views) (closed : v.tail = none) (member : (f, ordinal) ∈ v.allowed.zipIdx) :
    Step.support ⟨v.state, v.index, ordinal, f, v⟩ ∈ supportEdges n := by
  simp only [supportEdges, List.mem_flatMap]
  refine ⟨v, present, ?_⟩
  rw [ite_eq_left closed]
  exact List.mem_map.mpr ⟨(f, ordinal), member, rfl⟩

def walks (edges : List (Step S T)) : Nat → List (CurrentEmissionOwnershipR47.Endpoint (Key S T)) →
    CurrentEmissionOwnershipR47.Endpoint (Key S T) → CurrentEmissionOwnershipR47.Endpoint (Key S T) → List (List (Step S T))
  | 0, _, root, target => if root = target then [[]] else []
  | fuel+1, seen, root, target => if root = target then [[]] else
      edges.flatMap (fun e => if stepRoot e = root ∧ stepNext e ∉ seen then
        (walks edges fuel (stepNext e :: seen) (stepNext e) target).map (e :: ·) else [])

inductive FinitePath (edges : List (Step S T)) : Nat → List (CurrentEmissionOwnershipR47.Endpoint (Key S T)) →
    CurrentEmissionOwnershipR47.Endpoint (Key S T) → CurrentEmissionOwnershipR47.Endpoint (Key S T) → List (Step S T) → Prop where
  | refl (fuel seen point) : FinitePath edges fuel seen point point []
  | cons {fuel seen root target tail} (e : Step S T)
      (different : root ≠ target) (member : e ∈ edges) (owner : stepRoot e = root)
      (fresh : stepNext e ∉ seen)
      (rest : FinitePath edges fuel (stepNext e :: seen) (stepNext e) target tail) :
      FinitePath edges (fuel+1) seen root target (e :: tail)

theorem complete_finite_path_inventory (edges : List (Step S T))
    (fuel : Nat) (seen : List (CurrentEmissionOwnershipR47.Endpoint (Key S T))) (root target : CurrentEmissionOwnershipR47.Endpoint (Key S T))
    (path : List (Step S T)) (represented : FinitePath edges fuel seen root target path) :
    path ∈ walks edges fuel seen root target := by
  induction represented with
  | refl fuel seen point => cases fuel <;> simp [walks]
  | cons e different member owner fresh rest ih =>
      simp only [walks, ite_eq_right different, List.mem_flatMap]
      exact ⟨e, member, by simp [owner, fresh, ih]⟩

/-- Simple source paths retain the complete visited-endpoint set. No fuel
assumption or selected-path uniqueness is built into this relation. -/
inductive SimplePath (edges : List (Step S T)) : List (CurrentEmissionOwnershipR47.Endpoint (Key S T)) →
    CurrentEmissionOwnershipR47.Endpoint (Key S T) → CurrentEmissionOwnershipR47.Endpoint (Key S T) → List (Step S T) → Prop where
  | refl (seen point) : SimplePath edges seen point point []
  | cons {seen root target tail} (e : Step S T)
      (different : root ≠ target) (member : e ∈ edges) (owner : stepRoot e = root)
      (fresh : stepNext e ∉ seen)
      (rest : SimplePath edges (stepNext e :: seen) (stepNext e) target tail) :
      SimplePath edges seen root target (e :: tail)

omit [DecidableEq S] [DecidableEq T] in
theorem simple_path_fresh {edges : List (Step S T)} {seen root target path}
    (h : SimplePath edges seen root target path) : ∀ e ∈ path, stepNext e ∉ seen := by
  induction h with
  | refl => simp
  | cons head different member owner fresh rest ih =>
    intro e present
    rcases List.mem_cons.mp present with same | later
    · subst e; exact fresh
    · intro old
      exact ih e later (List.mem_cons_of_mem _ old)

omit [DecidableEq S] [DecidableEq T] in
theorem simple_path_nodup {edges : List (Step S T)} {seen root target path}
    (h : SimplePath edges seen root target path) : path.Nodup := by
  induction h with
  | refl => exact List.nodup_nil
  | cons head different member owner fresh rest ih =>
    refine List.nodup_cons.mpr ⟨?_, ih⟩
    intro repeated
    exact simple_path_fresh rest head repeated (by simp)

omit [DecidableEq S] [DecidableEq T] in
theorem simple_path_members {edges : List (Step S T)} {seen root target path}
    (h : SimplePath edges seen root target path) : path ⊆ edges := by
  induction h with
  | refl => simp
  | cons head different member owner fresh rest ih =>
    intro e present
    rcases List.mem_cons.mp present with same | later
    · subst e; exact member
    · exact ih later

omit [DecidableEq S] [DecidableEq T] in
theorem simple_path_to_finite {edges : List (Step S T)} {seen root target path}
    (h : SimplePath edges seen root target path) (fuel : Nat) (bound : path.length ≤ fuel) :
    FinitePath edges fuel seen root target path := by
  induction h generalizing fuel with
  | refl seen point => exact .refl fuel seen point
  | cons head different member owner fresh rest ih =>
    cases fuel with
    | zero => simp at bound
    | succ fuel =>
      exact .cons head different member owner fresh (ih fuel (Nat.le_of_succ_le_succ bound))

theorem all_simple_paths_covered (edges : List (Step S T))
    (seen : List (CurrentEmissionOwnershipR47.Endpoint (Key S T))) (root target : CurrentEmissionOwnershipR47.Endpoint (Key S T))
    (path : List (Step S T)) (h : SimplePath edges seen root target path) :
    path ∈ walks edges edges.length seen root target := by
  exact complete_finite_path_inventory _ _ _ _ _ _
    (simple_path_to_finite h edges.length ((simple_path_nodup h).length_le_of_subset (simple_path_members h)))

structure Search (S T : Type) where
  edges : List (Step S T)
  fuel : Nat
  completed : Bool

def paths (search : Search S T) (root target : CurrentEmissionOwnershipR47.Endpoint (Key S T)) : List (List (AuthenticatedResidualConsumerR49.Step (Key S T))) :=
  (walks search.edges search.fuel [root] root target).map (List.map step)
def inputs (n : Native S T) (search : Search S T) : AuthenticatedResidualConsumerR49.Inputs Nat (Key S T) Fact :=
  ⟨arrival n, (fun key => match key with
      | .effectAtom state (.support index) => if state = n.state then
          ((unique (fun v => decide (v.state = state ∧ v.index = index)) n.views).map (fun _ => index)) else none
      | _ => none), paths search, providers n⟩

theorem constructed_path_coverage (n : Native S T) (search : Search S T)
    (root target : CurrentEmissionOwnershipR47.Endpoint (Key S T)) (path : List (Step S T))
    (represented : FinitePath search.edges search.fuel [root] root target path) :
    path.map step ∈ (inputs n search).pathCandidates root target :=
  List.mem_map.mpr ⟨path, complete_finite_path_inventory _ _ _ _ _ _ represented, rfl⟩

structure Entry (S T : Type) where
  useOccurrence : S
  internalFact : Fact
  rawEntry : Nat
  rootRelation : Nat
  probe : Physical T
structure Provider (S T : Type) where
  catchOccurrence : S
  catchFact : Fact
  catchInput : Endpoint T
  catchOutput : Endpoint T
  provider : S
  declaration : S
  family : S
  view : View S
  member : Nat
  atom : EffectEndpoint
  entryTail : List (Step S T)
  catchPath : List (Step S T)

def entryQuery (n : Native S T) (e : Entry S T) : CurrentEmissionOwnershipR47.Query Nat (Key S T) Fact :=
  ⟨⟨n.artifact, .source e.useOccurrence⟩, e.internalFact, .effectRow n.state e.rawEntry, e.rootRelation⟩
def providerQuery (n : Native S T) (p : Provider S T) : ProviderEntryArrivalR48.Query (Key S T) Fact :=
  ⟨.source p.catchOccurrence, p.catchFact, endpoint n.state p.catchInput, endpoint n.state p.catchOutput,
    .source p.provider, .source p.declaration, .source p.family⟩
def terminal (n : Native S T) (p : Provider S T) : ProviderEntryArrivalR48.Probe (Key S T) :=
  ⟨[], [], .effectAtom n.state p.atom, p.view.index, p.member, view p.view⟩

/-- Build exactly the existing R49/R50 Context, including R55 construction.
No existing Context or unexplained model Inputs is supplied. -/
def context (n : Native S T) (search : Search S T)
    (source : SourceInternalContextR55.Native Nat (Key S T) T Fact)
    (q : SourceInternalContextR55.Query Nat (Key S T)) (p : SourceInternalContextR55.Probe Nat (Key S T) T Fact)
    (catches : List (SourceInternalContextR55.Catch (Key S T))) (operations : List (SourceInternalContextR55.Operation (Key S T)))
    (selection : SourceInternalContextR55.Selection (Key S T)) (e : Entry S T) (provider : Provider S T) :
    AuthenticatedResidualConsumerR49.Context Nat (Key S T) T Fact :=
  ⟨SourceInternalContextR55.internalInputs source, SourceInternalContextR55.query q, SourceInternalContextR55.probe p,
    InternalPermissionIncidenceR45.certificate (SourceInternalContextR55.query q) (SourceInternalContextR55.probe p),
    inputs n search, SourceInternalContextR55.catchInputs catches operations, entryQuery n e, physical e.probe,
    providerQuery n provider, ⟨provider.entryTail.map step, provider.catchPath.map step, terminal n provider, SourceInternalContextR55.selection selection⟩⟩

def factOwned (store batch : Nat) : Fact → Prop
  | .semantic owner _ => owner = store | .collected owner _ => owner = batch
instance (store batch : Nat) (id : Fact) : Decidable (factOwned store batch id) := by
  cases id <;> unfold factOwned <;> infer_instance
def Owned (n : Native S T) : Prop :=
  (∀ a ∈ n.admissions, a.state = n.state) ∧
  (∀ e ∈ n.emissions, e.state = n.state) ∧
  (∀ r ∈ n.valueRows, r.state = n.state) ∧
  (∀ r ∈ n.effectRows, r.state = n.state) ∧
  (∀ r ∈ n.relations, r.state = n.state) ∧
  (∀ d ∈ n.dependencies, d.state = n.state) ∧
  (∀ o ∈ n.origins, o.state = n.state) ∧
  (∀ v ∈ n.views, v.state = n.state) ∧
  (n.valueRows.map ValueRow.index).Nodup ∧ (n.effectRows.map EffectRow.index).Nodup ∧
  (n.relations.map Relation.index).Nodup ∧ (n.views.map View.index).Nodup ∧
  (n.facts.map SourceFact.identity).Nodup ∧
  (∀ f ∈ n.facts, factOwned n.store n.batch f.identity)
instance (n : Native S T) : Decidable (Owned n) := by unfold Owned; infer_instance

/-- Only primitive ownership checks and the complete enumerators above occur
here. In particular, this does not call authenticate/Authenticated. -/
def Ready (n : Native S T) (search : Search S T)
    (source : SourceInternalContextR55.Native Nat (Key S T) T Fact)
    (e : Entry S T) (p : Provider S T) : Prop :=
  search.completed = true ∧ Owned n ∧ derivedEdges n = some search.edges ∧
  search.fuel = search.edges.length ∧ source.artifact = n.artifact ∧
  (source.formals.map (fun f => (f.owner, f.lambdaIndex))).Nodup ∧
  e.rawEntry = n.entryRow ∧ e.rootRelation = n.entryRoot ∧
  Step.physical e.probe ∈ search.edges ∧
  providers n (.source p.provider) (.source p.declaration) (.source p.family) = [.effectAtom n.state p.atom] ∧
  paths search (.effectRow (.effectRow n.state e.rawEntry)) (.effectAtom (.effectAtom n.state p.atom)) =
    [(Step.physical e.probe :: p.entryTail).map step] ∧
  paths search (endpoint n.state p.catchInput) (.effectAtom (.effectAtom n.state p.atom)) = [p.catchPath.map step]
instance (n : Native S T) (search : Search S T)
    (source : SourceInternalContextR55.Native Nat (Key S T) T Fact) (e : Entry S T) (p : Provider S T) :
    Decidable (Ready n search source e p) := by unfold Ready; infer_instance

/-- Search/work-limit failure is external to the list-valued legacy tables:
do not manufacture a context with authenticated empty candidates on failure. -/
def availableContext (n : Native S T) (search : Search S T)
    (source : SourceInternalContextR55.Native Nat (Key S T) T Fact)
    (q : SourceInternalContextR55.Query Nat (Key S T)) (p : SourceInternalContextR55.Probe Nat (Key S T) T Fact)
    (catches : List (SourceInternalContextR55.Catch (Key S T))) (operations : List (SourceInternalContextR55.Operation (Key S T)))
    (selection : SourceInternalContextR55.Selection (Key S T)) (e : Entry S T) (provider : Provider S T) :
    Option (AuthenticatedResidualConsumerR49.Context Nat (Key S T) T Fact) :=
  if Ready n search source e provider then some (context n search source q p catches operations selection e provider) else none

theorem search_failure_unavailable (n : Native S T) (search : Search S T)
    (source : SourceInternalContextR55.Native Nat (Key S T) T Fact)
    (q : SourceInternalContextR55.Query Nat (Key S T)) (p : SourceInternalContextR55.Probe Nat (Key S T) T Fact)
    (catches : List (SourceInternalContextR55.Catch (Key S T))) (operations : List (SourceInternalContextR55.Operation (Key S T)))
    (selection : SourceInternalContextR55.Selection (Key S T)) (e : Entry S T) (provider : Provider S T)
    (failed : search.completed = false) :
    availableContext n search source q p catches operations selection e provider = none := by
  simp [availableContext, Ready, failed]

theorem available_context_iff (n : Native S T) (search : Search S T)
    (source : SourceInternalContextR55.Native Nat (Key S T) T Fact)
    (q : SourceInternalContextR55.Query Nat (Key S T)) (p : SourceInternalContextR55.Probe Nat (Key S T) T Fact)
    (catches : List (SourceInternalContextR55.Catch (Key S T))) (operations : List (SourceInternalContextR55.Operation (Key S T)))
    (selection : SourceInternalContextR55.Selection (Key S T)) (e : Entry S T) (provider : Provider S T)
    (out : AuthenticatedResidualConsumerR49.Context Nat (Key S T) T Fact) :
    availableContext n search source q p catches operations selection e provider = some out ↔
    Ready n search source e provider ∧ out = context n search source q p catches operations selection e provider := by
  unfold availableContext
  split <;> simp_all [eq_comm]

theorem current_inventory_reader_equations (n : Native S T) (index : Nat) :
    (current n).admissions = n.admissions.map admission ∧
    (current n).emissions = n.emissions.map emission ∧
    (current n).dependencies = dependencies n ∧
    (current n).relationPair index = (relationRead n index).map (fun r => (endpoint n.state r.lower, endpoint n.state r.upper)) ∧
    (current n).rootSource index = (originRead n index).map (fun o => (.source o.occurrence, o.slot)) ∧
    (current n).rootCause index = (rootDrain n index).map (fun d => (.source d.cause, d.slot)) ∧
    (current n).rootTask index = rootTask n index ∧ (current n).rootCompleted index = completed n index :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem view_reader_equation (n : Native S T) (v : View S)
    (read : unique (fun v' => decide (v'.state = n.state ∧ v'.index = v.index)) n.views = some v) :
    (arrival n).views v.index = some (view v) := by
  change (unique (fun v' => decide (v'.state = n.state ∧ v'.index = v.index)) n.views).map view = some (view v)
  rw [read]
  rfl

theorem fact_reader_equations (n : Native S T) (id : Fact) :
    (arrival n).factOrigin id = (factRead n id).map (fun f => (.source f.occurrence, f.slot)) ∧
    (arrival n).factPair id = (factRead n id).map (fun f => (endpoint n.state f.canonicalLower, endpoint n.state f.canonicalUpper)) := ⟨rfl, rfl⟩

theorem effect_row_reader (n : Native S T) (index : Nat) (r : EffectRow)
    (read : unique (fun r' => decide (r'.state = n.state ∧ n.state = n.state ∧ r'.index = index)) n.effectRows = some r) :
    (current n).effectRows (.effectRow n.state index) = some (effectBounds r.state r.bounds) := by
  change (unique (fun r' => decide (r'.state = n.state ∧ n.state = n.state ∧ r'.index = index)) n.effectRows).map
    (fun r => effectBounds r.state r.bounds) = _
  rw [read]
  rfl

theorem value_row_reader (n : Native S T) (index : Nat) (r : ValueRow T)
    (read : unique (fun r' => decide (r'.state = n.state ∧ n.state = n.state ∧ r'.index = index)) n.valueRows = some r) :
    (current n).valueRows (.valueRow n.state index) = some (valueBounds r.state r.bounds) := by
  change (unique (fun r' => decide (r'.state = n.state ∧ n.state = n.state ∧ r'.index = index)) n.valueRows).map
    (fun r => valueBounds r.state r.bounds) = _
  rw [read]
  rfl

theorem native_member_reader (n : Native S T) (index ordinal : Nat) (v : View S) (family : S)
    (read : unique (fun v' => decide (v'.state = n.state ∧ v'.index = index)) n.views = some v)
    (member : v.allowed[ordinal]? = some family) :
    (arrival n).nativeAtom (.effectAtom n.state (.annotationMember index ordinal)) =
      some (.annotationMember index ordinal) := by
  change (if n.state = n.state then
    ((unique (fun v' => decide (v'.state = n.state ∧ v'.index = index)) n.views).bind
      (fun v => v.allowed[ordinal]?)).map (fun _ => ProviderEntryArrivalR48.NativeAtom.annotationMember index ordinal)
    else none) = _
  rw [ite_eq_left rfl, read]
  simp only [Option.bind_some, member, Option.map_some]

theorem complete_origin_candidate_reader (n : Native S T) (occurrence : S) (id : Fact) (f : SourceFact S T)
    (read : factRead n id = some f) :
    (current n).rootCandidates ⟨n.artifact, .source occurrence⟩ id =
      (n.origins.filter (fun o => decide (o.state = n.state ∧ o.occurrence = occurrence ∧ o.slot = 0) &&
        match relationRead n o.relation with
        | some r => decide (r.lower = f.canonicalLower ∧ r.upper = f.canonicalUpper)
        | none => false)).map Origin.relation := by
  simp [current, rootCandidates, read]

theorem source_operation_reader (n : Native S T) (o : Operation S)
    (read : unique (fun found => decide (found.occurrence = o.occurrence)) n.operations = some o) :
    (arrival n).sourceOperation (.source o.occurrence) = some (.source o.declaration, .source o.family) := by
  simp [arrival, read]

theorem context_reader_equations (n : Native S T) (search : Search S T)
    (source : SourceInternalContextR55.Native Nat (Key S T) T Fact)
    (q : SourceInternalContextR55.Query Nat (Key S T)) (p : SourceInternalContextR55.Probe Nat (Key S T) T Fact)
    (catches : List (SourceInternalContextR55.Catch (Key S T))) (operations : List (SourceInternalContextR55.Operation (Key S T)))
    (selection : SourceInternalContextR55.Selection (Key S T)) (e : Entry S T) (provider : Provider S T) :
    (context n search source q p catches operations selection e provider).internalInputs = SourceInternalContextR55.internalInputs source ∧
    (context n search source q p catches operations selection e provider).inputs = inputs n search ∧
    (context n search source q p catches operations selection e provider).source = SourceInternalContextR55.catchInputs catches operations ∧
    (context n search source q p catches operations selection e provider).entryProbe = physical e.probe ∧
    (context n search source q p catches operations selection e provider).query = providerQuery n provider := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem available_context_covers_all_simple_paths (n : Native S T) (search : Search S T)
    (source : SourceInternalContextR55.Native Nat (Key S T) T Fact)
    (q : SourceInternalContextR55.Query Nat (Key S T)) (p : SourceInternalContextR55.Probe Nat (Key S T) T Fact)
    (catches : List (SourceInternalContextR55.Catch (Key S T))) (operations : List (SourceInternalContextR55.Operation (Key S T)))
    (selection : SourceInternalContextR55.Selection (Key S T)) (e : Entry S T) (provider : Provider S T)
    (out : AuthenticatedResidualConsumerR49.Context Nat (Key S T) T Fact)
    (accepted : availableContext n search source q p catches operations selection e provider = some out)
    (root target : CurrentEmissionOwnershipR47.Endpoint (Key S T)) (path : List (Step S T))
    (simple : SimplePath search.edges [root] root target path) :
    path.map step ∈ out.inputs.pathCandidates root target := by
  obtain ⟨ready, rfl⟩ := (available_context_iff _ _ _ _ _ _ _ _ _ _ _).mp accepted
  have fuel : search.fuel = search.edges.length := ready.2.2.2.1
  have represented := all_simple_paths_covered search.edges [root] root target path simple
  exact List.mem_map.mpr ⟨path, by simpa only [fuel] using represented, rfl⟩

theorem available_context_uses_r55_fragment (n : Native S T) (search : Search S T)
    (source : SourceInternalContextR55.Native Nat (Key S T) T Fact)
    (q : SourceInternalContextR55.Query Nat (Key S T)) (p : SourceInternalContextR55.Probe Nat (Key S T) T Fact)
    (catches : List (SourceInternalContextR55.Catch (Key S T))) (operations : List (SourceInternalContextR55.Operation (Key S T)))
    (selection : SourceInternalContextR55.Selection (Key S T)) (e : Entry S T) (provider : Provider S T)
    (out : AuthenticatedResidualConsumerR49.Context Nat (Key S T) T Fact)
    (accepted : availableContext n search source q p catches operations selection e provider = some out) :
    SourceInternalContextR55.internalFragment source = some out.internalInputs := by
  obtain ⟨ready, rfl⟩ := (available_context_iff _ _ _ _ _ _ _ _ _ _ _).mp accepted
  rcases ready with ⟨_, _, _, _, _, unique, _⟩
  simp [SourceInternalContextR55.internalFragment, unique, context]

theorem constructed_consumer_authorization (n : Native S T) (search : Search S T)
    (source : SourceInternalContextR55.Native Nat (Key S T) T Fact)
    (q : SourceInternalContextR55.Query Nat (Key S T)) (p : SourceInternalContextR55.Probe Nat (Key S T) T Fact)
    (catches : List (SourceInternalContextR55.Catch (Key S T))) (operations : List (SourceInternalContextR55.Operation (Key S T)))
    (selection : SourceInternalContextR55.Selection (Key S T)) (e : Entry S T) (provider : Provider S T)
    (endpoint : CurrentEmissionOwnershipR47.Endpoint (Key S T)) :
    AuthenticatedResidualConsumerR49.decideEndpoint (context n search source q p catches operations selection e provider) endpoint = some .suppress ↔
    endpoint = AuthenticatedResidualConsumerR49.target (context n search source q p catches operations selection e provider) ∧
      AuthenticatedResidualConsumerR49.authenticate (context n search source q p catches operations selection e provider) = true :=
  AuthenticatedResidualConsumerR49.suppression_iff _ _

theorem constructed_known_unmatched_forward (n : Native S T) (search : Search S T)
    (source : SourceInternalContextR55.Native Nat (Key S T) T Fact)
    (q : SourceInternalContextR55.Query Nat (Key S T)) (p : SourceInternalContextR55.Probe Nat (Key S T) T Fact)
    (catches : List (SourceInternalContextR55.Catch (Key S T))) (operations : List (SourceInternalContextR55.Operation (Key S T)))
    (selection : SourceInternalContextR55.Selection (Key S T)) (e : Entry S T) (provider : Provider S T)
    (endpoint : CurrentEmissionOwnershipR47.Endpoint (Key S T)) (candidate : Bool)
    (selected : AuthenticatedResidualConsumerR49.SelectedArmReads (SourceInternalContextR55.catchInputs catches operations)
      (providerQuery n provider) (SourceInternalContextR55.selection selection))
    (operation : (arrival n).sourceOperation (.source provider.provider) = some (.source provider.declaration, .source provider.family))
    (different : selection.declaration ≠ .source provider.declaration)
    (native : AuthenticatedResidualConsumerR49.providerCandidate (context n search source q p catches operations selection e provider) endpoint = some candidate) :
    AuthenticatedResidualConsumerR49.decideEndpoint (context n search source q p catches operations selection e provider) endpoint = some .forward := by
  apply AuthenticatedResidualConsumerR49.known_unmatched_decision _ _ _ candidate native
  apply (AuthenticatedResidualConsumerR49.classification_known_unmatched_iff _).mpr
  exact ⟨⟨selected, operation⟩, different⟩

def fixtureBound (row : Nat) : Bound Nat := ⟨.effect row, .positive, .effect (.annotationMember 0 0)⟩
def fixtureSlot (row : Nat) : Slot := ⟨.effect row, .effectLowerAtom, 0⟩
def fixtureAdmission (row relation : Nat) : Admission Nat := ⟨1, fixtureBound row, some relation⟩
def fixtureEmission (row index : Nat) : Emission Nat :=
  ⟨1, index, fixtureBound row, fixtureSlot row, fixtureSlot row, fixtureBound row⟩
def fixturePhysical (row index relation : Nat) (ancestry : List Nat) : Physical Nat :=
  ⟨index, index, fixtureAdmission row relation, fixtureEmission row index, relation, ancestry⟩
def fixtureView : View Nat := ⟨1, 0, .operation 300 301, 302, [7], none⟩
def fixtureNative : Native Nat Nat :=
  { artifact := 99, state := 1, store := 2, batch := 3, entryRow := 4, entryRoot := 2
    admissions := [fixtureAdmission 4 0, fixtureAdmission 6 1]
    emissions := [fixtureEmission 4 0, fixtureEmission 6 1]
    valueRows := []
    effectRows := [⟨1, 4, 40, ⟨[], [], [.annotationMember 0 0], []⟩⟩,
      ⟨1, 6, 60, ⟨[], [], [.annotationMember 0 0], []⟩⟩]
    relations := [⟨1, 0, .effect (.annotationMember 0 0), .effect (.row 4)⟩,
      ⟨1, 1, .effect (.annotationMember 0 0), .effect (.row 6)⟩,
      ⟨1, 2, .value (.positiveFunction 300), .value (.negativeFunction 400)⟩]
    dependencies := [⟨1, 2, 0⟩]
    origins := [⟨1, 2, 100, 0, some ⟨1, 0, 2, 2, 100, 0,
      .value (.positiveFunction 300), .value (.negativeFunction 400), none, false, true⟩⟩]
    facts := [⟨.semantic 2 88, 100, 0, .value (.positiveFunction 300), .value (.negativeFunction 400),
      .value (.positiveFunction 300), .value (.negativeFunction 400)⟩,
      ⟨.collected 3 88, 200, 51, .effect (.row 6), .effect (.row 7), .effect (.row 6), .effect (.row 7)⟩]
    views := [fixtureView]
    operations := [⟨300, 301, 7⟩] }
def fixtureEdges : List (Step Nat Nat) :=
  [.physical (fixturePhysical 4 0 0 [0]), .physical (fixturePhysical 6 1 1 []),
    .support ⟨1, 0, 0, 7, fixtureView⟩]
def fixtureSearch : Search Nat Nat := ⟨fixtureEdges, 3, true⟩
def fixtureEntry : Entry Nat Nat := ⟨100, .semantic 2 88, 4, 2, fixturePhysical 4 0 0 [0]⟩
def fixtureProvider : Provider Nat Nat :=
  ⟨200, .collected 3 88, .effect (.row 6), .effect (.row 7), 300, 301, 7,
    fixtureView, 0, .annotationMember 0 0, [], [.physical (fixturePhysical 6 1 1 [])]⟩

def fixtureFormal : SourceInternalContextR55.Formal (Key Nat Nat) Nat :=
  ⟨.source 1, 0, .source 2, 0, .source 3, .computation, some (.effectRow 1 4), some 700⟩
def fixtureConstruction : SourceInternalContextR55.Construction (Key Nat Nat) Nat :=
  ⟨0, .source 17, 200, .effectRow 1 4⟩
def fixturePermission : SourceInternalContextR55.Permission (Key Nat Nat) :=
  ⟨0, 0, .source 2, .source 17, .source 1, .source 3, .source 6, .source 5, .effectRow 1 4,
    [.source 7, .source 7, .source 11]⟩
def fixtureUse : SourceInternalContextR55.Use Nat (Key Nat Nat) := ⟨99, .source 100⟩
def fixtureReceipt : SourceInternalContextR55.Receipt Nat (Key Nat Nat) Fact := ⟨fixtureUse, .internal, some (.semantic 2 88)⟩
def fixturePlan : SourceInternalContextR55.Plan Nat (Key Nat Nat) Nat :=
  ⟨fixtureUse, .source 10, .source 1, 20, 21, 300, 400⟩
def fixtureInternal : SourceInternalContextR55.Native Nat (Key Nat Nat) Nat Fact :=
  ⟨99, [fixtureFormal], [.source 2], [.source 999], [⟨.source 1, [.lambda (.source 17) (.source 2)]⟩],
    [(.source 17, .source 1)], [], [], [fixtureConstruction], [fixturePermission], [fixtureReceipt],
    [fixturePlan], [⟨.source 17, some 0, 20⟩],
    [⟨.semantic 2 88, .source 100, 0, 300, 400⟩, ⟨.semantic 2 89, .source 17, 2, 200, 300⟩],
    [(20, 300), (21, 400)], [(200, .positiveFunction 201), (201, .negativeEffectVariable (.effectRow 1 4))]⟩
def fixtureQuery : SourceInternalContextR55.Query Nat (Key Nat Nat) :=
  ⟨fixtureUse, .source 10, .source 1, 0, .source 17, .source 6, .source 5⟩
def fixtureProbe : SourceInternalContextR55.Probe Nat (Key Nat Nat) Nat Fact :=
  ⟨fixtureFormal, 300, 20, fixtureConstruction, fixturePermission, fixturePlan, fixtureReceipt, .semantic 2 88, 201⟩
def fixtureCatch : SourceInternalContextR55.Catch (Key Nat Nat) :=
  ⟨.source 1, .source 400, .source 200,
    [⟨.source 401, (10, 20), .operation (.source 402) (some (.source 301, .source 7))
      [.unitSyntax (.source 403) (12, 14)] .wildcard, 8⟩]⟩
def fixtureOperation : SourceInternalContextR55.Operation (Key Nat Nat) := ⟨.source 402, .source 301, .source 7⟩
def fixtureSelection : SourceInternalContextR55.Selection (Key Nat Nat) :=
  ⟨.source 400, 0, .source 401, (10, 20), .source 402, .source 403, .source 301, .source 7⟩
def fixtureContext : AuthenticatedResidualConsumerR49.Context Nat (Key Nat Nat) Nat Fact :=
  context fixtureNative fixtureSearch fixtureInternal fixtureQuery fixtureProbe
    [fixtureCatch] [fixtureOperation] fixtureSelection fixtureEntry fixtureProvider

theorem concrete_complete_owner_and_candidates :
    derivedEdges fixtureNative = some fixtureEdges ∧
    Ready fixtureNative fixtureSearch fixtureInternal fixtureEntry fixtureProvider ∧
    (arrival fixtureNative).catchCandidates (.source 200) = [.collected 3 88] ∧
    (current fixtureNative).sourceFact (.source 100, 0) = some (.semantic 2 88) := by decide

theorem concrete_constructed_context_authenticates :
    AuthenticatedResidualConsumerR49.authenticate fixtureContext = true := by decide

theorem concrete_available_constructed_context :
    availableContext fixtureNative fixtureSearch fixtureInternal fixtureQuery fixtureProbe
      [fixtureCatch] [fixtureOperation] fixtureSelection fixtureEntry fixtureProvider = some fixtureContext :=
  (available_context_iff _ _ _ _ _ _ _ _ _ _ _).mpr ⟨concrete_complete_owner_and_candidates.2.1, rfl⟩

theorem concrete_consumer_suppression :
    AuthenticatedResidualConsumerR49.decideEndpoint fixtureContext
      (.effectAtom (.effectAtom 1 (.annotationMember 0 0))) = some .suppress :=
  (AuthenticatedResidualConsumerR49.suppression_iff _ _).mpr ⟨rfl, concrete_constructed_context_authenticates⟩

def competingViewNative : Native Nat Nat :=
  { fixtureNative with views := [fixtureView, { fixtureView with index := 1 }] }
def alternateBound : Bound Nat := ⟨.effect 4, .positive, .effect (.row 6)⟩
def alternateSlot : Slot := ⟨.effect 4, .effectLowerRow, 0⟩
def alternateAdmission : Admission Nat := ⟨1, alternateBound, some 3⟩
def alternateEmission : Emission Nat := ⟨1, 2, alternateBound, alternateSlot, alternateSlot, alternateBound⟩
def alternatePhysical : Physical Nat := ⟨2, 2, alternateAdmission, alternateEmission, 3, [3]⟩
def competingPathNative : Native Nat Nat :=
  { fixtureNative with
    admissions := fixtureNative.admissions ++ [alternateAdmission]
    emissions := fixtureNative.emissions ++ [alternateEmission]
    effectRows := [⟨1, 4, 40, ⟨[6], [], [.annotationMember 0 0], []⟩⟩,
      ⟨1, 6, 60, ⟨[], [], [.annotationMember 0 0], []⟩⟩]
    relations := fixtureNative.relations ++ [⟨1, 3, .effect (.row 6), .effect (.row 4)⟩]
    dependencies := fixtureNative.dependencies ++ [⟨1, 2, 3⟩] }
def competingPathEdges : List (Step Nat Nat) := .physical alternatePhysical :: fixtureEdges
def competingPathSearch : Search Nat Nat := ⟨competingPathEdges, 4, true⟩

theorem concrete_competitors_cannot_be_omitted :
    providers competingViewNative (.source 300) (.source 301) (.source 7) =
      [.effectAtom 1 (.annotationMember 0 0), .effectAtom 1 (.annotationMember 1 0)] ∧
    ¬ Ready competingViewNative fixtureSearch fixtureInternal fixtureEntry fixtureProvider ∧
    ¬ Ready fixtureNative { fixtureSearch with edges := fixtureEdges.tail } fixtureInternal fixtureEntry fixtureProvider ∧
    derivedEdges competingPathNative = some competingPathEdges ∧
    (paths competingPathSearch (.effectRow (.effectRow 1 4))
      (.effectAtom (.effectAtom 1 (.annotationMember 0 0)))).length = 2 ∧
    ¬ Ready competingPathNative competingPathSearch fixtureInternal fixtureEntry fixtureProvider := by decide

theorem concrete_foreign_stale_and_reversed_owners_rejected :
    ¬ Ready { fixtureNative with effectRows := [⟨2, 4, 40, ⟨[], [], [.annotationMember 0 0], []⟩⟩] }
      fixtureSearch fixtureInternal fixtureEntry fixtureProvider ∧
    derivedEdges { fixtureNative with dependencies := [⟨1, 0, 2⟩] } = none ∧
    derivedEdges { fixtureNative with dependencies := [⟨2, 2, 0⟩] } = none ∧
    derivedEdges { fixtureNative with emissions :=
      [{ fixtureEmission 4 0 with readbackSlot := fixtureSlot 5 }, fixtureEmission 6 1] } = none ∧
    ¬ Ready fixtureNative fixtureSearch fixtureInternal { fixtureEntry with rawEntry := 40 } fixtureProvider := by decide

theorem concrete_support_order_and_canonical_substitution_rejected :
    ¬ AuthenticatedResidualConsumerR49.SupportReads
      (inputs { fixtureNative with views := [{ fixtureView with allowed := [11, 7] }] } fixtureSearch)
      (support (S := Nat) (T := Nat) ⟨1, 0, 0, 7, fixtureView⟩) ∧
    AuthenticatedResidualConsumerR49.authenticate
      (context fixtureNative fixtureSearch fixtureInternal fixtureQuery fixtureProbe
        [fixtureCatch] [fixtureOperation] fixtureSelection { fixtureEntry with rawEntry := 40 } fixtureProvider) = false ∧
    (fixtureNative.effectRows[0]?).map EffectRow.canonical = some 40 ∧
    ((endpoint 1 (.effect (.row 4)) : CurrentEmissionOwnershipR47.Endpoint (Key Nat Nat)) ≠ endpoint 1 (.effect (.row 40))) := by decide

theorem concrete_same_numeric_namespaces_stay_separate :
    (arrival fixtureNative).factOrigin (.collected 3 88) = some (.source 200, 51) ∧
    (arrival fixtureNative).factOrigin (.semantic 2 88) = some (.source 100, 0) ∧
    (current fixtureNative).sourceFact (.source 200, 51) = some (.collected 3 88) ∧
    ((endpoint 1 (.value (.row 4)) : CurrentEmissionOwnershipR47.Endpoint (Key Nat Nat)) ≠ endpoint 1 (.effect (.row 4))) ∧
    ((endpoint 1 (.effect (.contribution 7)) : CurrentEmissionOwnershipR47.Endpoint (Key Nat Nat)) ≠ endpoint 1 (.effect (.support 7))) ∧
    ((endpoint 1 (.effect (.allowance 7)) : CurrentEmissionOwnershipR47.Endpoint (Key Nat Nat)) ≠ endpoint 1 (.effect (.annotationMember 7 0))) := by decide

def unmatchedCatch : SourceInternalContextR55.Catch (Key Nat Nat) :=
  { fixtureCatch with arms :=
    [⟨.source 401, (10, 20), .operation (.source 402) (some (.source 305, .source 7))
      [.unitSyntax (.source 403) (12, 14)] .wildcard, 8⟩] }
def unmatchedContext : AuthenticatedResidualConsumerR49.Context Nat (Key Nat Nat) Nat Fact :=
  context fixtureNative fixtureSearch fixtureInternal fixtureQuery fixtureProbe
    [unmatchedCatch] [⟨.source 402, .source 305, .source 7⟩]
    { fixtureSelection with declaration := .source 305 } fixtureEntry fixtureProvider
theorem concrete_known_unmatched_still_forwards :
    AuthenticatedResidualConsumerR49.classifyIdentity unmatchedContext = .knownUnmatched ∧
    AuthenticatedResidualConsumerR49.decideEndpoint unmatchedContext
      (.effectAtom (.effectAtom 1 (.annotationMember 0 0))) = some .forward := by decide

theorem concrete_source_failure_and_work_limit_unavailable :
    ¬ Ready fixtureNative { fixtureSearch with completed := false } fixtureInternal fixtureEntry fixtureProvider ∧
    ¬ Ready fixtureNative { fixtureSearch with fuel := 0 } fixtureInternal fixtureEntry fixtureProvider ∧
    ¬ Ready { fixtureNative with views := [] } fixtureSearch fixtureInternal fixtureEntry fixtureProvider := by decide

theorem concrete_observer_unavailable_with_forward :
    availableContext fixtureNative { fixtureSearch with completed := false } fixtureInternal fixtureQuery fixtureProbe
      [fixtureCatch] [fixtureOperation] fixtureSelection fixtureEntry fixtureProvider = none ∧
    AuthenticatedResidualConsumerR49.decideEndpoint unmatchedContext
      (.effectAtom (.effectAtom 1 (.annotationMember 0 0))) = some .forward :=
  ⟨search_failure_unavailable _ _ _ _ _ _ _ _ _ _ rfl, concrete_known_unmatched_still_forwards.2⟩

theorem distinct_fact_namespaces (owner index : Nat) : Fact.semantic owner index ≠ Fact.collected owner index := by
  intro impossible; cases impossible

theorem foreign_effect_row_unavailable (n : Native S T) (foreign index : Nat) (different : foreign ≠ n.state) :
    (current n).effectRows (.effectRow foreign index) = none := by
  have empty : n.effectRows.filter (fun _ => false) = [] := by
    induction n.effectRows with
    | nil => rfl
    | cons head rest ih => change rest.filter (fun _ => false) = []; exact ih
  simp [current, unique, SourceInternalContextR55.unique, different, empty]

end YulangClosure.ProviderNativeContextR57
