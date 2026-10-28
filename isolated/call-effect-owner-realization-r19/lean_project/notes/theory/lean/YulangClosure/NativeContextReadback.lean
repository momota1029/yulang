import YulangClosure.NativeContextExpansion
import YulangClosure.NativeDrainOwnership
import YulangClosure.NativeExecutionHistory

/-!
Construction of the early Context publication / later Dispatch boundary.
Memo entries retain their actual active occurrence, not a completed-body claim.
The common driver below refines the immutable-occurrence drain history.
-/
namespace YulangClosure.NativeContextReadback

open NativeMergeExpansion
open NativeContextExpansion
open NativeReplayCurrent (currentPair Pair)

structure Prefix where
  parsed : Parsed
  checks : List Check
  postContext : Nat
  consumed : Bool
  deriving DecidableEq, Repr

def prepareParsed (t : Tables) (a : Availability) (levels q : Nat → Nat)
    (key : Key) (p : Parsed) : Option Prefix := do
  if relationGuard ⟨(currentPair q key).1, (currentPair q key).2,
      key.context, key.sources, key.transformer⟩ then
    let checks ← collect (checkFilter t a levels q key) p.filters
    pure ⟨p, checks, if p.filters = [] then key.context else p.residual,
      consumed (currentPair q key).2 checks⟩
  else none

def prepare (t : Tables) (a : Availability) (levels q : Nat → Nat)
    (fuel : Nat) (key : Key) : Option Prefix :=
  if a.enter && decide (key.lower = (currentPair q key).1 ∧
      key.upper = (currentPair q key).2) then
    (if key.context = 0 then some (⟨[], 0, false, false, false⟩ : Parsed)
      else if a.parser then parse t fuel key.context else none).bind
      (prepareParsed t a levels q key)
  else none

def finishPrefix (t : Tables) (a : Availability) (levels q : Nat → Nat)
    (key : Key) (p : Prefix) : Option Body :=
  if p.consumed then some ⟨p.parsed, p.checks, p.postContext, true, none⟩
  else (applyEffect t a levels q key p.postContext (currentPair q key)).map
    fun leaf => ⟨p.parsed, p.checks, p.postContext, false, some leaf⟩

theorem staged_decompose (t : Tables) (a : Availability) (levels q : Nat → Nat)
    (key : Key) (p : Parsed) (published : a.publish = true) :
    (prepareParsed t a levels q key p).bind (finishPrefix t a levels q key) =
      decompose t a levels q key p := by
  simp only [prepareParsed, decompose, published, Bool.true_eq_false, and_false, ↓reduceIte]
  split
  · cases collect (checkFilter t a levels q key) p.filters <;>
      simp [Option.bind, finishPrefix, Option.map]
    all_goals first | rfl | (split <;> first | rfl | (split <;> simp_all))
  · rfl

theorem staged_expand (t : Tables) (a : Availability) (levels q : Nat → Nat)
    (fuel : Nat) (key : Key) (published : a.publish = true) :
    (prepare t a levels q fuel key).bind (finishPrefix t a levels q key) =
      expand t a levels q fuel key := by
  simp only [prepare, expand]
  split
  · rw [Option.bind_assoc]
    congr 1
    funext p
    exact staged_decompose t a levels q key p published
  · rfl

def Prefix.transport (q : Nat → Nat) (post : Key → Nat) (p : Prefix) : Prefix :=
  { p with checks := p.checks.map fun c => { c with leaf := c.leaf.transport q post } }

/-- A recipe has only actual checked callbacks and explicit carrier transport.
No constructor takes a completed Context property or an arbitrary body. -/
inductive PrefixRecipe (t : Tables) (key : Key) : Prefix → Prop
  | checked (a : Availability) (levels q : Nat → Nat) (fuel : Nat) (p : Prefix)
      (result : prepare t a levels q fuel key = some p) : PrefixRecipe t key p
  | transported {p : Prefix} (prior : PrefixRecipe t key p)
      (q : Nat → Nat) (post : Key → Nat) :
      PrefixRecipe t key (p.transport q post)

structure PrefixPacket (t : Tables) where
  key : Key
  segment : Prefix
  construction : PrefixRecipe t key segment

inductive BodyRecipe (t : Tables) (key : Key) : Body → Prop
  | finished {p : Prefix} (origin : PrefixRecipe t key p)
      (a : Availability) (levels q : Nat → Nat) (body : Body)
      (result : finishPrefix t a levels q key p = some body) : BodyRecipe t key body
  | transported {body : Body} (prior : BodyRecipe t key body)
      (q : Nat → Nat) (post : Key → Nat) :
      BodyRecipe t key (body.transport q post)

structure BodyPacket (t : Tables) where
  key : Key
  body : Body
  construction : BodyRecipe t key body

def PrefixPacket.move {t : Tables} (p : PrefixPacket t)
    (q : Nat → Nat) (post : Key → Nat) : PrefixPacket t :=
  ⟨p.key, p.segment.transport q post, .transported p.construction q post⟩

def BodyPacket.move {t : Tables} (b : BodyPacket t)
    (q : Nat → Nat) (post : Key → Nat) : BodyPacket t :=
  ⟨b.key, b.body.transport q post, .transported b.construction q post⟩

theorem finish_keeps_all_checks {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {key : Key} {p : Prefix} {body : Body}
    (result : finishPrefix t a levels q key p = some body) :
    body.parsed = p.parsed ∧ body.checks = p.checks ∧
      body.postContext = p.postContext ∧ body.consumed = p.consumed := by
  unfold finishPrefix at result
  split at result
  · rename_i yes
    cases result
    simp [yes]
  · rename_i no
    cases applied : applyEffect t a levels q key p.postContext (currentPair q key) <;>
      simp [applied] at result
    cases result
    simp_all

theorem fresh_body_is_frozen_built {t : Tables} {a : Availability}
    {levels q : Nat → Nat} {fuel : Nat} {key : Key} {p : Prefix} {body : Body}
    (checks : prepare t a levels q fuel key = some p)
    (dispatch : finishPrefix t a levels q key p = some body)
    (published : a.publish = true) : Built t q key body := by
  apply Built.computed a levels q fuel key body
  rw [← staged_expand t a levels q fuel key published, checks]
  exact dispatch

inductive Relation where
  | effect (key : Key)
  | value (request : ValueRequest Nat)
  deriving DecidableEq, Repr

inductive Task where
  | effect (lower upper : Endpoint)
  | value (lower upper : Nat)
  deriving DecidableEq, Repr

def Relation.task : Relation → Task
  | .effect k => .effect k.lower k.upper
  | .value r => .value r.lower r.upper

def Relation.context : Relation → Nat
  | .effect k => k.context
  | .value r => r.context

def Relation.sources : Relation → Option Nat
  | .effect k => k.sources
  | .value r => r.sources

def Relation.transformer : Relation → Nat
  | .effect k => k.transformer
  | .value r => r.transformer

def Relation.demand : Relation → Option ScopedDemand
  | .effect _ => none
  | .value r => r.demand

def Relation.valid : Relation → Bool
  | .effect k => relationGuard k
  | .value r => decide (r.transformer = 0)

def Task.canonical (effect value : Nat → Nat) : Task → Task
  | .effect lower upper => .effect (renameEndpoint effect lower) (renameEndpoint effect upper)
  | .value lower upper => .value (value lower) (value upper)

def Relation.transported (effect value : Nat → Nat) (post : Nat) (r : Relation) : Relation :=
  if r.task.canonical effect value = r.task then r
  else match r with
    | .effect k => .effect { k with
        lower := renameEndpoint effect k.lower
        upper := renameEndpoint effect k.upper
        context := post }
    | .value v => .value { v with lower := value v.lower, upper := value v.upper, context := post }

theorem transport_whole_payload (effect value : Nat → Nat) (post : Nat) (r : Relation) :
    (r.transported effect value post).sources = r.sources ∧
    (r.transported effect value post).transformer = r.transformer ∧
    (r.transported effect value post).demand = r.demand := by
  unfold Relation.transported
  split
  · exact ⟨rfl, rfl, rfl⟩
  · cases r <;> exact ⟨rfl, rfl, rfl⟩

theorem transport_pair (effect value : Nat → Nat) (post : Nat) (r : Relation) :
    (r.transported effect value post).task = r.task.canonical effect value := by
  unfold Relation.transported
  split
  · rename_i same; exact same.symm
  · cases r <;> rfl

theorem transport_stored_or_post (effect value : Nat → Nat) (post : Nat) (r : Relation) :
    (r.transported effect value post).context =
      if r.task.canonical effect value = r.task then r.context else post := by
  unfold Relation.transported
  split
  · rfl
  · cases r <;> rfl

def LiveWork (s : NativeDrainOwnership.State) (w : NativeDrainOwnership.Work) : Prop :=
  ∃ f ∈ s.frames, f.current = some w

def ProcessedWork (s : NativeDrainOwnership.State) (w : NativeDrainOwnership.Work) : Prop :=
  (∃ f ∈ s.frames, w ∈ f.processed) ∨ NativeDrainOwnership.returnedWork w s.returns

/-- A raw counter guard excludes clearing Dispatch; it is not a coverage premise.
Every native constructor is examined in the two preservation proofs below. -/
def processedCount (s : NativeDrainOwnership.State) : Nat :=
  (s.frames.map fun f => f.processed.length).sum +
    (s.returns.map fun r => r.frame.processed.length).sum

def Administrative (s u : NativeDrainOwnership.State) : Prop :=
  processedCount u = processedCount s

theorem administrative_live {s u : NativeDrainOwnership.State}
    (step : NativeDrainOwnership.Step s u) (allowed : Administrative s u)
    {w : NativeDrainOwnership.Work} (live : LiveWork s w) : LiveWork u w := by
  cases step <;> simp_all [Administrative, processedCount, LiveWork,
    NativeDrainOwnership.pushWork, NativeDrainOwnership.newFrame,
    NativeDrainOwnership.consumedFrame, List.map_map, List.sum_append]
  all_goals grind

theorem administrative_processed {s u : NativeDrainOwnership.State}
    (step : NativeDrainOwnership.Step s u) (allowed : Administrative s u)
    {w : NativeDrainOwnership.Work} (done : ProcessedWork u w) : ProcessedWork s w := by
  cases step <;> simp_all [Administrative, processedCount, ProcessedWork,
    NativeDrainOwnership.returnedWork, NativeDrainOwnership.pushWork,
    NativeDrainOwnership.newFrame, NativeDrainOwnership.consumedFrame,
    List.map_map, List.sum_append]
  all_goals grind

theorem transport_live {s : NativeDrainOwnership.State} {f : NativeDrainOwnership.Frame} {fs : List NativeDrainOwnership.Frame}
    {other : NativeDrainOwnership.Work} {relation : Nat} (top : s.frames = f :: fs)
    (live : LiveWork s other) :
    LiveWork { s with frames := { f with processing := some relation } :: fs } other := by
  simpa [LiveWork, top] using live

theorem transport_processed {s : NativeDrainOwnership.State} {f : NativeDrainOwnership.Frame} {fs : List NativeDrainOwnership.Frame}
    {w : NativeDrainOwnership.Work} {relation : Nat} (top : s.frames = f :: fs) :
    ProcessedWork { s with frames := { f with processing := some relation } :: fs } w ↔
      ProcessedWork s w := by
  simp [ProcessedWork, NativeDrainOwnership.returnedWork, top]

def dispatchControl (s : NativeDrainOwnership.State) (f : NativeDrainOwnership.Frame) (fs : List NativeDrainOwnership.Frame)
    (w : NativeDrainOwnership.Work) (transitions : Nat) : NativeDrainOwnership.State :=
  { s with frames := { f with
      current := none
      processing := none
      processed := f.processed ++ [w]
      transitions := transitions } :: fs }

theorem dispatch_other_live {s : NativeDrainOwnership.State} {f : NativeDrainOwnership.Frame} {fs : List NativeDrainOwnership.Frame}
    {w other : NativeDrainOwnership.Work} {transitions : Nat} (top : s.frames = f :: fs)
    (current : f.current = some w) (different : other ≠ w) (live : LiveWork s other) :
    LiveWork (dispatchControl s f fs w transitions) other := by
  simp [LiveWork, top, current] at live
  rcases live with same | rest
  · exact (different same.symm).elim
  · exact ⟨rest.choose, by simp [dispatchControl, rest.choose_spec.1], rest.choose_spec.2⟩

theorem dispatch_processed {s : NativeDrainOwnership.State} {f : NativeDrainOwnership.Frame} {fs : List NativeDrainOwnership.Frame}
    {w other : NativeDrainOwnership.Work} {transitions : Nat} (top : s.frames = f :: fs) :
    ProcessedWork (dispatchControl s f fs w transitions) other →
      other = w ∨ ProcessedWork s other := by
  simp [ProcessedWork, NativeDrainOwnership.returnedWork, dispatchControl, top]
  grind

abbrev Work := NativeDrainOwnership.Work
abbrev Frame := NativeDrainOwnership.Frame
abbrev Control := NativeDrainOwnership.State

structure Route (t : Tables) where
  work : Work
  processing : Nat
  source : Relation
  effectMap : Nat → Nat
  valueMap : Nat → Nat
  previous : Option (PrefixPacket t)

def Route.post {t : Tables} (r : Route t) : Nat :=
  match r.previous with
  | none => r.source.context
  | some p => p.segment.postContext

def Route.target {t : Tables} (r : Route t) : Relation :=
  r.source.transported r.effectMap r.valueMap r.post

def Route.derived {t : Tables} (r : Route t) : List (Nat × Nat) :=
  if r.source.task.canonical r.effectMap r.valueMap = r.source.task then []
  else [(r.work.relation, r.processing)]

structure Ready (t : Tables) where
  route : Route t
  packet : PrefixPacket t
  exactKey : route.target = .effect packet.key

structure ValueReady (t : Tables) where
  route : Route t
  request : ValueRequest Nat
  exactKey : route.target = .value request
  availability : Availability
  levels : Nat → Nat
  q : Nat → Nat
  fuel : Nat
  result : executeInput t availability levels q fuel (.value request) =
    some (.value request)

structure Owner (t : Tables) where
  ready : Ready t

def Owner.work {t : Tables} (o : Owner t) : Work := o.ready.route.work
def Owner.key {t : Tables} (o : Owner t) : Key := o.ready.packet.key
def Owner.relation {t : Tables} (o : Owner t) : Nat := o.ready.route.processing

structure Memo (t : Tables) where
  generation : Nat
  owner : Owner t

inductive Receipt (t : Tables) where
  | effect (current : Ready t) (owner : Owner t)
  | value (current : ValueReady t)

def Receipt.work {t : Tables} : Receipt t → Work
  | .effect current _ => current.route.work
  | .value current => current.route.work

structure State (t : Tables) where
  control : Control := NativeDrainOwnership.initial
  effectMap : Nat → Nat := id
  valueMap : Nat → Nat := id
  generation : Nat := 0
  relations : Nat → Option Relation := fun _ => none
  tasks : Nat → Option Task := fun _ => none
  routes : Work → Option (Route t) := fun _ => none
  checked : Work → Option (Ready t) := fun _ => none
  published : Work → Option (Ready t) := fun _ => none
  ready : Work → Option (Ready t) := fun _ => none
  valueReady : Work → Option (ValueReady t) := fun _ => none
  publications : Nat × Key → Option (PrefixPacket t) := fun _ => none
  postContexts : Key → Nat := fun key => key.context
  owners : Work → Option (Owner t) := fun _ => none
  memo : Nat × Key → Option (Memo t) := fun _ => none
  typed : List Task := []
  seals : List (Owner t × BodyPacket t) := []
  receipts : List (Receipt t) := []
  edges : List (Nat × Nat) := []
  settling : Bool := false

def initial (t : Tables) : State t := {}

def put {I A : Type} [DecidableEq I] (table : I → Option A) (id : I) (a : A) : I → Option A :=
  fun other => if other = id then some a else table other

theorem put_old {I A : Type} [DecidableEq I] {table : I → Option A} {id old : I}
    {value before : A} (fresh : table id = none) (found : table old = some before) :
    put table id value old = some before := by
  have ne : old ≠ id := by intro eq; subst old; rw [fresh] at found; cases found
  simp [put, ne, found]

def previous {t : Tables} (s : State t) (id : Nat) : Relation → Option (PrefixPacket t)
  | .effect key => s.publications (id, key)
  | .value _ => none

def makeRoute {t : Tables} (s : State t) (w : Work) (processing : Nat)
    (source : Relation) : Route t :=
  ⟨w, processing, source, s.effectMap, s.valueMap, previous s w.relation source⟩

def postAt {t : Tables} (s : State t) (key : Key) : Nat :=
  s.postContexts key

def HasSeal {t : Tables} (s : State t) (o : Owner t) : Prop :=
  ∃ body, (o, body) ∈ s.seals ∧ body.key = o.key

def ReceiptLinked {t : Tables} (s : State t) : Receipt t → Prop
  | .effect current owner => s.owners owner.work = some owner ∧
      current.route.processing = owner.relation ∧ current.packet.key = owner.key
  | .value _ => True

structure Invariant {t : Tables} (s : State t) : Prop where
  owners : ∀ w o, s.owners w = some o → o.work = w ∧
    (LiveWork s.control w ∨ HasSeal s o)
  memo : ∀ index m, s.memo index = some m →
    s.owners m.owner.work = some m.owner ∧ index = (m.owner.relation, m.owner.key)
  receipts : ∀ r ∈ s.receipts, ReceiptLinked s r
  processed : ∀ w, ProcessedWork s.control w → ∃ r ∈ s.receipts, r.work = w

def controlOnly {t : Tables} (s : State t) (control : Control) : State t :=
  { s with control := control }

def admitOwner {t : Tables} (s : State t) (ready : Ready t) (raw : Task) : State t :=
  let owner : Owner t := ⟨ready⟩
  { s with
    owners := put s.owners owner.work owner
    memo := if raw = ready.route.target.task then
      put s.memo (owner.relation, owner.key) ⟨s.generation, owner⟩ else s.memo
    typed := attach raw s.typed }

def pairCurrent {t : Tables} (s : State t) (ready : Ready t) (raw : Task) : Bool :=
  decide (raw ∈ s.typed) && match s.memo (ready.route.processing, ready.packet.key) with
    | none => false
    | some memo => decide (memo.generation = s.generation)

def finishOwner {t : Tables} (s : State t) (f : Frame) (fs : List Frame)
    (owner : Owner t) (body : BodyPacket t) (transitions : Nat) : State t :=
  { s with
    control := dispatchControl s.control f fs owner.work transitions
    seals := s.seals ++ [(owner, body)]
    receipts := s.receipts ++ [.effect owner.ready owner] }

def finishReuse {t : Tables} (s : State t) (f : Frame) (fs : List Frame)
    (ready : Ready t) (owner : Owner t) (transitions : Nat) : State t :=
  { s with
    control := dispatchControl s.control f fs ready.route.work transitions
    receipts := s.receipts ++ [.effect ready owner] }

def finishValue {t : Tables} (s : State t) (f : Frame) (fs : List Frame)
    (ready : ValueReady t) (transitions : Nat) : State t :=
  { s with
    control := dispatchControl s.control f fs ready.route.work transitions
    receipts := s.receipts ++ [.value ready] }

/-- The successful event cuts are deliberately separated at publication,
sampling, memo admission, and completed clearing Dispatch. -/
inductive Step (t : Tables) : State t → State t → Prop
  | control (s : State t) (next : Control)
      (event : NativeDrainOwnership.Step s.control next)
      (administrative : Administrative s.control next)
      (settlement : s.settling = true → next.frames = s.control.frames) :
      Step t s (controlOnly s next)
  | intern (s : State t) (id : Nat) (relation : Relation)
      (fresh : s.relations id = none) (unique : ∀ old, s.relations old ≠ some relation)
      (valid : relation.valid = true) :
      Step t s { s with relations := put s.relations id relation }
  | task (s : State t) (id : Nat) (task : Task) (fresh : s.tasks id = none) :
      Step t s { s with tasks := put s.tasks id task }
  | transport (s : State t) (f : Frame) (fs : List Frame) (w : Work)
      (processing : Nat) (source : Relation) (raw : Task)
      (top : s.control.frames = f :: fs) (phase : f.phase = .working)
      (current : f.current = some w) (before : f.processing = some w.relation)
      (relation : s.relations w.relation = some source) (task : s.tasks w.task = some raw)
      (pair : source.task.canonical s.effectMap s.valueMap = raw.canonical s.effectMap s.valueMap)
      (interned : s.relations processing = some (makeRoute s w processing source).target)
      (valid : (makeRoute s w processing source).target.valid = true)
      (unchanged : source.task.canonical s.effectMap s.valueMap = source.task → processing = w.relation) :
      Step t s { s with
        control := { s.control with frames := { f with processing := some processing } :: fs }
        routes := put s.routes w (makeRoute s w processing source)
        edges := s.edges ++ (makeRoute s w processing source).derived }
  | contextEmpty (s : State t) (f : Frame) (fs : List Frame) (r : Route t)
      (key : Key) (a : Availability) (levels : Nat → Nat) (fuel : Nat) (p : Prefix)
      (top : s.control.frames = f :: fs) (current : f.current = some r.work)
      (processing : f.processing = some r.processing) (routed : s.routes r.work = some r)
      (keyIs : r.target = .effect key)
      (result : prepare t a levels s.effectMap fuel key = some p) (empty : p.parsed.filters = []) :
      Step t s { s with
        ready := put s.ready r.work
          ⟨r, ⟨key, p, .checked a levels s.effectMap fuel p result⟩, keyIs⟩ }
  | contextCheck (s : State t) (f : Frame) (fs : List Frame) (r : Route t)
      (key : Key) (a : Availability) (levels : Nat → Nat) (fuel : Nat) (p : Prefix)
      (top : s.control.frames = f :: fs) (current : f.current = some r.work)
      (processing : f.processing = some r.processing) (routed : s.routes r.work = some r)
      (keyIs : r.target = .effect key) (undischarged : s.publications (r.processing, key) = none)
      (result : prepare t a levels s.effectMap fuel key = some p) (nonempty : p.parsed.filters ≠ []) :
      Step t s { s with
        checked := put s.checked r.work
          ⟨r, ⟨key, p, .checked a levels s.effectMap fuel p result⟩, keyIs⟩ }
  | publish (s : State t) (ready : Ready t) (checked : s.checked ready.route.work = some ready)
      (reserved : Bool) (success : reserved = true) :
      Step t s { s with
        publications := put s.publications (ready.route.processing, ready.packet.key) ready.packet
        published := put s.published ready.route.work ready
        postContexts := fun key => if key = ready.packet.key then ready.packet.segment.postContext
          else s.postContexts key }
  | sample (s : State t) (ready : Ready t)
      (published : s.published ready.route.work = some ready)
      (sampled : Bool) (success : sampled = true) :
      Step t s { s with ready := put s.ready ready.route.work ready }
  | contextCached (s : State t) (f : Frame) (fs : List Frame) (r : Route t)
      (packet : PrefixPacket t) (fuel : Nat)
      (top : s.control.frames = f :: fs) (current : f.current = some r.work)
      (processing : f.processing = some r.processing) (routed : s.routes r.work = some r)
      (keyIs : r.target = .effect packet.key)
      (discharged : s.publications (r.processing, packet.key) = some packet)
      (parsed : parse t fuel packet.key.context = some packet.segment.parsed)
      (nonempty : packet.segment.parsed.filters ≠ [])
      (guard : relationGuard packet.key = true)
      (canonical : packet.key.lower = (currentPair s.effectMap packet.key).1 ∧
        packet.key.upper = (currentPair s.effectMap packet.key).2) :
      Step t s { s with
        ready := put s.ready r.work
          ⟨r, packet.move s.effectMap (postAt s), keyIs⟩ }
  | contextValue (s : State t) (f : Frame) (fs : List Frame) (ready : ValueReady t)
      (top : s.control.frames = f :: fs) (current : f.current = some ready.route.work)
      (processing : f.processing = some ready.route.processing)
      (routed : s.routes ready.route.work = some ready.route) :
      Step t s { s with valueReady := put s.valueReady ready.route.work ready }
  | admit (s : State t) (f : Frame) (fs : List Frame) (ready : Ready t) (raw : Task)
      (top : s.control.frames = f :: fs) (phase : f.phase = .working)
      (current : f.current = some ready.route.work) (processing : f.processing = some ready.route.processing)
      (context : s.ready ready.route.work = some ready) (task : s.tasks ready.route.work.task = some raw)
      (fresh : s.owners ready.route.work = none) (notCurrent : pairCurrent s ready raw = false) :
      Step t s (admitOwner s ready raw)
  | finish (s : State t) (f : Frame) (fs : List Frame) (owner : Owner t)
      (a : Availability) (levels : Nat → Nat) (body : Body) (transitions : Nat)
      (top : s.control.frames = f :: fs) (phase : f.phase = .working)
      (current : f.current = some owner.work) (processing : f.processing = some owner.relation)
      (owned : s.owners owner.work = some owner)
      (result : finishPrefix t a levels s.effectMap owner.key owner.ready.packet.segment = some body) :
      Step t s (finishOwner s f fs owner
        ⟨owner.key, body, .finished owner.ready.packet.construction a levels s.effectMap body result⟩ transitions)
  | duplicate (s : State t) (f : Frame) (fs : List Frame) (ready : Ready t)
      (memo : Memo t) (raw : Task) (transitions : Nat)
      (top : s.control.frames = f :: fs) (phase : f.phase = .working)
      (current : f.current = some ready.route.work) (processing : f.processing = some ready.route.processing)
      (context : s.ready ready.route.work = some ready) (task : s.tasks ready.route.work.task = some raw)
      (typed : raw ∈ s.typed) (found : s.memo (ready.route.processing, ready.packet.key) = some memo)
      (generation : memo.generation = s.generation) (notOwner : s.owners ready.route.work = none) :
      Step t s (finishReuse s f fs ready memo.owner transitions)
  | valueExit (s : State t) (f : Frame) (fs : List Frame) (ready : ValueReady t) (transitions : Nat)
      (top : s.control.frames = f :: fs) (phase : f.phase = .working)
      (current : f.current = some ready.route.work) (processing : f.processing = some ready.route.processing)
      (context : s.valueReady ready.route.work = some ready) (notOwner : s.owners ready.route.work = none) :
      Step t s (finishValue s f fs ready transitions)
  | beginSettlement (s : State t) (f : Frame) (fs : List Frame)
      (top : s.control.frames = f :: fs) (phase : f.phase = .working)
      (current : f.current = none) (queue : s.control.queue = []) (notSettling : s.settling = false) :
      Step t s { s with settling := true }
  | merge (s : State t) (effect value : Nat → Nat) (settling : s.settling = true)
      (absorbsEffect : ∀ row, effect (s.effectMap row) = effect row)
      (absorbsValue : ∀ row, value (s.valueMap row) = value row) :
      Step t s { s with effectMap := effect, valueMap := value, generation := s.generation + 1 }
  | endSettlement (s : State t) (settling : s.settling = true) :
      Step t s { s with settling := false }

theorem initial_invariant (t : Tables) : Invariant (initial t) := by
  constructor <;> simp [initial, ProcessedWork, NativeDrainOwnership.initial,
    NativeDrainOwnership.returnedWork]

theorem invariant_control {t : Tables} {s : State t} {next : Control}
    (inv : Invariant s) (event : NativeDrainOwnership.Step s.control next)
    (administrative : Administrative s.control next) : Invariant (controlOnly s next) := by
  constructor
  · intro w o found
    obtain ⟨same, held⟩ := inv.owners w o found
    refine ⟨same, ?_⟩
    exact held.elim (fun live => .inl (administrative_live event administrative live)) Or.inr
  · exact inv.memo
  · exact inv.receipts
  · intro w done
    exact inv.processed w (administrative_processed event administrative done)

theorem invariant_admit {t : Tables} {s : State t} {ready : Ready t} {raw : Task}
    (inv : Invariant s) (live : LiveWork s.control ready.route.work)
    (fresh : s.owners ready.route.work = none) : Invariant (admitOwner s ready raw) := by
  have old : ∀ w o, s.owners w = some o → (admitOwner s ready raw).owners w = some o := by
    intro w o found
    exact put_old fresh found
  constructor
  · intro w o found
    by_cases same : w = ready.route.work
    · subst w
      have eq : o = (⟨ready⟩ : Owner t) := by
        simpa [admitOwner, put, Owner.work] using found.symm
      subst o
      exact ⟨rfl, .inl live⟩
    · have before : s.owners w = some o := by
        simpa [admitOwner, put, Owner.work, same] using found
      exact inv.owners w o before
  · intro index m found
    by_cases canonical : raw = ready.route.target.task
    · by_cases same : index = (ready.route.processing, ready.packet.key)
      · subst index
        have eq : m = (⟨s.generation, ⟨ready⟩⟩ : Memo t) := by
          simpa [admitOwner, canonical, put, Owner.relation, Owner.key] using found.symm
        subst m
        exact ⟨by simp [admitOwner, put, Owner.work], rfl⟩
      · have before : s.memo index = some m := by
          simpa [admitOwner, canonical, put, Owner.relation, Owner.key, same] using found
        obtain ⟨owned, key⟩ := inv.memo index m before
        exact ⟨old _ _ owned, key⟩
    · have before : s.memo index = some m := by simpa [admitOwner, canonical] using found
      obtain ⟨owned, key⟩ := inv.memo index m before
      exact ⟨old _ _ owned, key⟩
  · intro receipt member
    have linked := inv.receipts receipt member
    cases receipt with
    | value => trivial
    | effect current owner => exact ⟨old _ _ linked.1, linked.2⟩
  · exact inv.processed

theorem invariant_finish {t : Tables} {s : State t} {f : Frame} {fs : List Frame}
    {owner : Owner t} {body : BodyPacket t} {transitions : Nat}
    (inv : Invariant s) (top : s.control.frames = f :: fs)
    (current : f.current = some owner.work) (owned : s.owners owner.work = some owner)
    (key : body.key = owner.key) : Invariant (finishOwner s f fs owner body transitions) := by
  constructor
  · intro w o found
    obtain ⟨same, held⟩ := inv.owners w o found
    refine ⟨same, ?_⟩
    by_cases target : w = owner.work
    · have atOwner : s.owners owner.work = some o := by
        simpa only [finishOwner, target] using found
      have eq : o = owner := Option.some.inj (atOwner.symm.trans owned)
      subst o
      exact .inr ⟨body, by simp [finishOwner], key⟩
    · rcases held with live | sealed
      · exact .inl (dispatch_other_live top current target live)
      · obtain ⟨b, member, key⟩ := sealed
        exact .inr ⟨b, List.mem_append_left _ member, key⟩
  · exact inv.memo
  · intro receipt member
    rcases List.mem_append.mp member with old | new
    · exact inv.receipts receipt old
    · have eq : receipt = .effect owner.ready owner := by simpa using new
      subst receipt
      exact ⟨owned, rfl, rfl⟩
  · intro w done
    rcases dispatch_processed top done with same | before
    · subst w
      exact ⟨.effect owner.ready owner, by simp [finishOwner], rfl⟩
    · obtain ⟨r, member, same⟩ := inv.processed w before
      exact ⟨r, List.mem_append_left _ member, same⟩

theorem invariant_reuse {t : Tables} {s : State t} {f : Frame} {fs : List Frame}
    {ready : Ready t} {owner : Owner t} {transitions : Nat}
    (inv : Invariant s) (top : s.control.frames = f :: fs)
    (current : f.current = some ready.route.work) (unowned : s.owners ready.route.work = none)
    (owned : s.owners owner.work = some owner)
    (relation : ready.route.processing = owner.relation) (key : ready.packet.key = owner.key) :
    Invariant (finishReuse s f fs ready owner transitions) := by
  constructor
  · intro w o found
    obtain ⟨same, held⟩ := inv.owners w o found
    refine ⟨same, ?_⟩
    have different : w ≠ ready.route.work := by
      intro eq
      have before : s.owners w = some o := found
      rw [eq, unowned] at before
      cases before
    exact held.elim (fun live => .inl (dispatch_other_live top current different live)) Or.inr
  · exact inv.memo
  · intro receipt member
    rcases List.mem_append.mp member with old | new
    · exact inv.receipts receipt old
    · have eq : receipt = .effect ready owner := by simpa using new
      subst receipt
      exact ⟨owned, relation, key⟩
  · intro w done
    rcases dispatch_processed top done with same | before
    · subst w
      exact ⟨.effect ready owner, by simp [finishReuse], rfl⟩
    · obtain ⟨r, member, same⟩ := inv.processed w before
      exact ⟨r, List.mem_append_left _ member, same⟩

theorem invariant_value {t : Tables} {s : State t} {f : Frame} {fs : List Frame}
    {ready : ValueReady t} {transitions : Nat}
    (inv : Invariant s) (top : s.control.frames = f :: fs)
    (current : f.current = some ready.route.work) (unowned : s.owners ready.route.work = none) :
    Invariant (finishValue s f fs ready transitions) := by
  constructor
  · intro w o found
    obtain ⟨same, held⟩ := inv.owners w o found
    refine ⟨same, ?_⟩
    have different : w ≠ ready.route.work := by
      intro eq
      have before : s.owners w = some o := found
      rw [eq, unowned] at before
      cases before
    exact held.elim (fun live => .inl (dispatch_other_live top current different live)) Or.inr
  · exact inv.memo
  · intro receipt member
    rcases List.mem_append.mp member with old | new
    · exact inv.receipts receipt old
    · have eq : receipt = .value ready := by simpa using new
      subst receipt; trivial
  · intro w done
    rcases dispatch_processed top done with same | before
    · subst w
      exact ⟨.value ready, by simp [finishValue], rfl⟩
    · obtain ⟨r, member, same⟩ := inv.processed w before
      exact ⟨r, List.mem_append_left _ member, same⟩

theorem step_invariant {t : Tables} {s u : State t} (event : Step t s u)
    (inv : Invariant s) : Invariant u := by
  cases event with
  | control next event administrative settlement => exact invariant_control inv event administrative
  | transport f fs w processing source raw top phase current before relation task pair interned valid unchanged =>
      constructor
      · intro other o found
        obtain ⟨same, held⟩ := inv.owners other o found
        refine ⟨same, ?_⟩
        exact held.elim (fun live => .inl (transport_live top live)) Or.inr
      · exact inv.memo
      · exact inv.receipts
      · intro other done
        exact inv.processed other ((transport_processed top).mp done)
  | admit f fs ready raw top phase current processing context task fresh notCurrent =>
      exact invariant_admit inv ⟨f, by simp [top], current⟩ fresh
  | finish f fs owner a levels body transitions top phase current processing owned result =>
      exact invariant_finish inv top current owned rfl
  | duplicate f fs ready memo raw transitions top phase current processing context task typed found generation notOwner =>
      obtain ⟨owned, same⟩ := inv.memo _ _ found
      have parts := Prod.mk.inj same
      exact invariant_reuse inv top current notOwner owned parts.1 parts.2
  | valueExit f fs ready transitions top phase current processing context notOwner =>
      exact invariant_value inv top current notOwner
  | intern | task | contextEmpty | contextCheck | publish | sample | contextCached |
      contextValue | beginSettlement | merge | endSettlement =>
        exact ⟨inv.owners, inv.memo, inv.receipts, inv.processed⟩

inductive Run (t : Tables) : State t → State t → Prop
  | nil (s : State t) : Run t s s
  | snoc {s u v : State t} : Run t s u → Step t u v → Run t s v

theorem run_invariant {t : Tables} {s u : State t} (run : Run t s u)
    (inv : Invariant s) : Invariant u := by
  induction run with
  | nil => exact inv
  | snoc _ event ih => exact step_invariant event ih

theorem reachable_invariant {t : Tables} {s : State t} (run : Run t (initial t) s) : Invariant s :=
  run_invariant run (initial_invariant t)

theorem step_control {t : Tables} {s u : State t} (event : Step t s u) :
    NativeDrainOwnership.Run s.control u.control := by
  cases event with
  | control next event administrative settlement => exact .snoc (.nil _) event
  | transport f fs w processing source raw top phase current before relation task pair interned valid unchanged =>
      exact .snoc (.nil _) (.transport _ f fs w processing top phase current)
  | finish f fs owner a levels body transitions top phase current processing owned result =>
      exact .snoc (.nil _) (.dispatch _ f fs owner.work transitions top phase current)
  | duplicate f fs ready memo raw transitions top phase current processing context task typed found generation notOwner =>
      exact .snoc (.nil _) (.dispatch _ f fs ready.route.work transitions top phase current)
  | valueExit f fs ready transitions top phase current processing context notOwner =>
      exact .snoc (.nil _) (.dispatch _ f fs ready.route.work transitions top phase current)
  | intern | task | contextEmpty | contextCheck | publish | sample | contextCached |
      contextValue | admit | beginSettlement | merge | endSettlement => exact .nil _

theorem control_run_trans {s u v : Control} (first : NativeDrainOwnership.Run s u)
    (last : NativeDrainOwnership.Run u v) : NativeDrainOwnership.Run s v := by
  induction last with
  | nil => exact first
  | snoc _ event ih => exact .snoc ih event

theorem run_control {t : Tables} {s u : State t} (run : Run t s u) :
    NativeDrainOwnership.Run s.control u.control := by
  induction run with
  | nil => exact .nil _
  | snoc _ event ih => exact control_run_trans ih (step_control event)

def NoCurrent {t : Tables} (s : State t) : Prop :=
  ∀ f ∈ s.control.frames, f.current = none

theorem no_current_not_live {t : Tables} {s : State t} (cut : NoCurrent s) (w : Work) :
    ¬ LiveWork s.control w := by
  rintro ⟨f, member, current⟩
  rw [cut f member] at current
  cases current

theorem memo_has_actual_owner {t : Tables} {s : State t}
    (run : Run t (initial t) s) {index : Nat × Key} {memo : Memo t}
    (found : s.memo index = some memo) :
    s.owners memo.owner.work = some memo.owner ∧
    index = (memo.owner.relation, memo.owner.key) ∧
    (LiveWork s.control memo.owner.work ∨ HasSeal s memo.owner) := by
  have inv := reachable_invariant run
  obtain ⟨owned, same⟩ := inv.memo index memo found
  exact ⟨owned, same, (inv.owners memo.owner.work memo.owner owned).2⟩

theorem owned_body_at_cut {t : Tables} {s : State t}
    (run : Run t (initial t) s) (cut : NoCurrent s)
    {w : Work} {owner : Owner t} (owned : s.owners w = some owner) : HasSeal s owner := by
  have held := (reachable_invariant run).owners w owner owned
  exact held.2.elim (fun live => (no_current_not_live cut w live).elim) id

theorem memo_body_at_cut {t : Tables} {s : State t}
    (run : Run t (initial t) s) (cut : NoCurrent s)
    {index : Nat × Key} {memo : Memo t} (found : s.memo index = some memo) :
    ∃ body, (memo.owner, body) ∈ s.seals ∧ body.key = index.2 ∧
      BodyRecipe t body.key body.body := by
  obtain ⟨owned, same, _⟩ := memo_has_actual_owner run found
  obtain ⟨body, member, key⟩ := owned_body_at_cut run cut owned
  exact ⟨body, member, by simpa [same] using key, body.construction⟩

/-- The native inner settlement cut can retain an outer synchronous owner.
The alternative is its actual live frame, never a pending-coverage assertion. -/
theorem settlement_owner_readback {t : Tables} {s : State t}
    (run : Run t (initial t) s) {f : Frame} {fs : List Frame}
    (top : s.control.frames = f :: fs) (current : f.current = none)
    (_queue : s.control.queue = []) {index : Nat × Key} {memo : Memo t}
    (found : s.memo index = some memo) :
    HasSeal s memo.owner ∨ ∃ outer ∈ fs, outer.current = some memo.owner.work := by
  obtain ⟨_, _, held⟩ := memo_has_actual_owner run found
  rcases held with live | sealed
  · rcases live with ⟨outer, member, active⟩
    rw [top] at member
    rcases List.mem_cons.mp member with same | old
    · subst outer; rw [current] at active; cases active
    · exact .inr ⟨outer, old, active⟩
  · exact .inl sealed

def Resolved {t : Tables} (s : State t) : Receipt t → Prop
  | .effect current owner => ∃ body, (owner, body) ∈ s.seals ∧
      current.route.processing = owner.relation ∧
      current.route.target = .effect body.key ∧ BodyRecipe t body.key body.body
  | .value current => executeInput t current.availability current.levels current.q current.fuel
      (.value current.request) = some (.value current.request)

theorem receipt_resolved_at_cut {t : Tables} {s : State t}
    (run : Run t (initial t) s) (cut : NoCurrent s)
    {receipt : Receipt t} (member : receipt ∈ s.receipts) : Resolved s receipt := by
  have linked := (reachable_invariant run).receipts receipt member
  cases receipt with
  | value current => exact current.result
  | effect current owner =>
      obtain ⟨body, stored, same⟩ := owned_body_at_cut run cut linked.1
      refine ⟨body, stored, linked.2.1, ?_, body.construction⟩
      rw [current.exactKey, linked.2.2, same]

/-- Every actual issued occurrence is read back through this same history.
Effect receipts identify a constructed body of the canonical processing owner;
Value receipts retain the exact complete Context forwarding request. -/
theorem quiescent_issued_readback {t : Tables} {s : State t}
    (run : Run t (initial t) s) (queue : s.control.queue = [])
    (stack : s.control.frames = []) :
    ∀ w ∈ s.control.issued, ∃ receipt ∈ s.receipts,
      receipt.work = w ∧ Resolved s receipt := by
  intro w issued
  have control : NativeDrainOwnership.Run NativeDrainOwnership.initial s.control := run_control run
  obtain ⟨r, returned, processed, _⟩ :=
    NativeDrainOwnership.quiescent_work_returned control queue stack w issued
  obtain ⟨receipt, member, same⟩ := (reachable_invariant run).processed w
    (.inr ⟨r, returned, processed⟩)
  have cut : NoCurrent s := by simp [NoCurrent, stack]
  exact ⟨receipt, member, same, receipt_resolved_at_cut run cut member⟩

theorem quiescent_replay_readback {t : Tables} {s : State t}
    (run : Run t (initial t) s) (queue : s.control.queue = [])
    (stack : s.control.frames = []) :
    (∀ w ∈ s.control.issued, ∃ receipt ∈ s.receipts, receipt.work = w ∧ Resolved s receipt) ∧
    (∀ a ∈ s.control.transferred, ∃ r ∈ s.control.acknowledgements,
      r.ticket = a ∧ r.diagnosed = true) := by
  exact ⟨quiescent_issued_readback run queue stack,
    NativeDrainOwnership.quiescent_replay_acknowledged (run_control run) queue stack⟩

theorem readback_whole_payload {t : Tables} (ready : Ready t) :
    (.effect ready.packet.key : Relation).sources = ready.route.source.sources ∧
    (.effect ready.packet.key : Relation).transformer = ready.route.source.transformer ∧
    (.effect ready.packet.key : Relation).demand = ready.route.source.demand := by
  rw [← ready.exactKey]
  exact transport_whole_payload _ _ _ _

theorem readback_value_whole_payload {t : Tables} (ready : ValueReady t) :
    ready.request.sources = ready.route.source.sources ∧
    ready.request.transformer = ready.route.source.transformer ∧
    ready.request.demand = ready.route.source.demand := by
  have payload := transport_whole_payload ready.route.effectMap ready.route.valueMap
    ready.route.post ready.route.source
  change ready.route.target.sources = _ ∧ ready.route.target.transformer = _ ∧
    ready.route.target.demand = _ at payload
  rw [ready.exactKey] at payload
  exact payload

theorem readback_original_context {t : Tables} (ready : Ready t) :
    ready.packet.key.context =
      if ready.route.source.task.canonical ready.route.effectMap ready.route.valueMap =
        ready.route.source.task then ready.route.source.context else ready.route.post := by
  have context := transport_stored_or_post ready.route.effectMap ready.route.valueMap
    ready.route.post ready.route.source
  change ready.route.target.context = _ at context
  rw [ready.exactKey] at context
  exact context

theorem publication_is_early {t : Tables} (s : State t) (ready : Ready t) :
    let next : State t := { s with
      publications := put s.publications (ready.route.processing, ready.packet.key) ready.packet
      published := put s.published ready.route.work ready
      postContexts := fun key => if key = ready.packet.key then ready.packet.segment.postContext
        else s.postContexts key }
    next.publications (ready.route.processing, ready.packet.key) = some ready.packet ∧
      next.postContexts ready.packet.key = ready.packet.segment.postContext ∧
      next.seals = s.seals ∧ next.control = s.control := by
  simp [put]

def FreshChecks {t : Tables} (packet : PrefixPacket t) : Prop :=
  ∃ a levels q fuel, prepare t a levels q fuel packet.key = some packet.segment

structure PublicationInvariant {t : Tables} (s : State t) : Prop where
  checked : ∀ w ready, s.checked w = some ready →
    FreshChecks ready.packet ∧ ready.packet.segment.parsed.filters ≠ []
  published : ∀ w ready, s.published w = some ready →
    FreshChecks ready.packet ∧ ready.packet.segment.parsed.filters ≠ []
  table : ∀ index packet, s.publications index = some packet →
    packet.key = index.2 ∧ FreshChecks packet ∧ packet.segment.parsed.filters ≠ []

theorem initial_publications (t : Tables) : PublicationInvariant (initial t) := by
  constructor <;> simp [initial]

theorem step_publications {t : Tables} {s u : State t} (event : Step t s u)
    (inv : PublicationInvariant s) : PublicationInvariant u := by
  cases event with
  | contextCheck f fs r key a levels fuel p top current processing routed keyIs undischarged result nonempty =>
      constructor
      · intro w ready found
        by_cases same : w = r.work
        · subst w
          have eq : ready = (⟨r, ⟨key, p, .checked a levels s.effectMap fuel p result⟩, keyIs⟩ : Ready t) := by
            simpa [put] using found.symm
          subst ready
          exact ⟨⟨a, levels, s.effectMap, fuel, result⟩, nonempty⟩
        · exact inv.checked w ready (by simpa [put, same] using found)
      · exact inv.published
      · exact inv.table
  | publish ready checked reserved success =>
      have origin := inv.checked ready.route.work ready checked
      constructor
      · exact inv.checked
      · intro w other found
        by_cases same : w = ready.route.work
        · subst w
          have eq : other = ready := by simpa [put] using found.symm
          subst other; exact origin
        · exact inv.published w other (by simpa [put, same] using found)
      · intro index packet found
        by_cases same : index = (ready.route.processing, ready.packet.key)
        · subst index
          have eq : packet = ready.packet := by simpa [put] using found.symm
          subst packet; exact ⟨rfl, origin⟩
        · exact inv.table index packet (by simpa [put, same] using found)
  | control | intern | task | transport | contextEmpty | sample | contextCached | contextValue |
      admit | finish | duplicate | valueExit | beginSettlement | merge | endSettlement =>
      exact ⟨inv.checked, inv.published, inv.table⟩

theorem run_publications {t : Tables} {s u : State t} (run : Run t s u)
    (inv : PublicationInvariant s) : PublicationInvariant u := by
  induction run with
  | nil => exact inv
  | snoc _ event ih => exact step_publications event ih

theorem actual_discharged_prefix {t : Tables} {s : State t}
    (run : Run t (initial t) s) {id : Nat} {key : Key} {packet : PrefixPacket t}
    (found : s.publications (id, key) = some packet) :
    packet.key = key ∧ FreshChecks packet ∧ packet.segment.parsed.filters ≠ [] :=
  (run_publications run (initial_publications t)).table (id, key) packet found

def Receipt.route {t : Tables} : Receipt t → Route t
  | .effect current _ => current.route
  | .value current => current.route

def RouteValid {t : Tables} (s : State t) (r : Route t) : Prop :=
  (∀ packet, r.previous = some packet → r.source = .effect packet.key ∧
    FreshChecks packet ∧ packet.segment.parsed.filters ≠ []) ∧
  (∀ edge ∈ r.derived, edge ∈ s.edges)

structure References {t : Tables} (s : State t) (P : Route t → Prop) : Prop where
  routes : ∀ w r, s.routes w = some r → P r
  checked : ∀ w r, s.checked w = some r → P r.route
  published : ∀ w r, s.published w = some r → P r.route
  ready : ∀ w r, s.ready w = some r → P r.route
  valueReady : ∀ w r, s.valueReady w = some r → P r.route
  owners : ∀ w o, s.owners w = some o → P o.ready.route
  receipts : ∀ r ∈ s.receipts, P r.route

theorem References.map {t : Tables} {s : State t} {P Q : Route t → Prop}
    (refs : References s P) (change : ∀ r, P r → Q r) : References s Q := by
  exact ⟨fun w r h => change r (refs.routes w r h),
    fun w r h => change r.route (refs.checked w r h),
    fun w r h => change r.route (refs.published w r h),
    fun w r h => change r.route (refs.ready w r h),
    fun w r h => change r.route (refs.valueReady w r h),
    fun w r h => change r.ready.route (refs.owners w r h),
    fun r h => change r.route (refs.receipts r h)⟩

theorem put_property {I A : Type} [DecidableEq I] {table : I → Option A} {P : A → Prop}
    {key : I} {value : A} (old : ∀ i a, table i = some a → P a) (new : P value) :
    ∀ i a, put table key value i = some a → P a := by
  intro i a found
  by_cases same : i = key
  · subst i
    have eq : a = value := by simpa [put] using found.symm
    subst a; exact new
  · exact old i a (by simpa [put, same] using found)

theorem initial_references (t : Tables) : References (initial t) (RouteValid (initial t)) := by
  constructor <;> simp [initial]

theorem step_references {t : Tables} {s u : State t} (event : Step t s u)
    (pubs : PublicationInvariant s) (refs : References s (RouteValid s)) :
    References u (RouteValid u) := by
  cases event with
  | transport f fs w processing source raw top phase current before relation task pair interned valid unchanged =>
      have old := refs.map (fun r h =>
        (⟨h.1, fun edge member => List.mem_append_left _ (h.2 edge member)⟩ :
          RouteValid { s with edges := s.edges ++ (makeRoute s w processing source).derived } r))
      have new : RouteValid { s with edges := s.edges ++ (makeRoute s w processing source).derived }
          (makeRoute s w processing source) := by
        constructor
        · intro packet found
          cases source with
          | value request => simp [makeRoute, previous] at found
          | effect key =>
              have actual : s.publications (w.relation, key) = some packet := found
              obtain ⟨same, origin, nonempty⟩ := pubs.table (w.relation, key) packet actual
              exact ⟨by simpa [makeRoute] using congrArg Relation.effect same.symm, origin, nonempty⟩
        · intro edge member; exact List.mem_append_right _ member
      exact ⟨put_property old.routes new, old.checked, old.published, old.ready,
        old.valueReady, old.owners, old.receipts⟩
  | contextEmpty f fs r key a levels fuel p top current processing routed keyIs result empty =>
      exact ⟨refs.routes, refs.checked, refs.published,
        put_property refs.ready (refs.routes r.work r routed), refs.valueReady, refs.owners, refs.receipts⟩
  | contextCheck f fs r key a levels fuel p top current processing routed keyIs undischarged result nonempty =>
      exact ⟨refs.routes, put_property refs.checked (refs.routes r.work r routed),
        refs.published, refs.ready, refs.valueReady, refs.owners, refs.receipts⟩
  | publish ready checked reserved success =>
      exact ⟨refs.routes, refs.checked,
        put_property refs.published (refs.checked ready.route.work ready checked),
        refs.ready, refs.valueReady, refs.owners, refs.receipts⟩
  | sample ready published sampled success =>
      exact ⟨refs.routes, refs.checked, refs.published,
        put_property refs.ready (refs.published ready.route.work ready published),
        refs.valueReady, refs.owners, refs.receipts⟩
  | contextCached f fs r packet fuel top current processing routed keyIs discharged parsed nonempty guard canonical =>
      exact ⟨refs.routes, refs.checked, refs.published,
        put_property refs.ready (refs.routes r.work r routed), refs.valueReady, refs.owners, refs.receipts⟩
  | contextValue f fs ready top current processing routed =>
      exact ⟨refs.routes, refs.checked, refs.published, refs.ready,
        put_property refs.valueReady (refs.routes ready.route.work ready.route routed),
        refs.owners, refs.receipts⟩
  | admit f fs ready raw top phase current processing context task fresh notCurrent =>
      exact ⟨refs.routes, refs.checked, refs.published, refs.ready, refs.valueReady,
        put_property refs.owners (refs.ready ready.route.work ready context), refs.receipts⟩
  | finish f fs owner a levels body transitions top phase current processing owned result =>
      refine ⟨refs.routes, refs.checked, refs.published, refs.ready, refs.valueReady, refs.owners, ?_⟩
      intro receipt member
      rcases List.mem_append.mp member with old | new
      · exact refs.receipts receipt old
      · have eq : receipt = .effect owner.ready owner := by simpa using new
        subst receipt; exact refs.owners owner.work owner owned
  | duplicate f fs ready memo raw transitions top phase current processing context task typed found generation notOwner =>
      refine ⟨refs.routes, refs.checked, refs.published, refs.ready, refs.valueReady, refs.owners, ?_⟩
      intro receipt member
      rcases List.mem_append.mp member with old | new
      · exact refs.receipts receipt old
      · have eq : receipt = .effect ready memo.owner := by simpa using new
        subst receipt; exact refs.ready ready.route.work ready context
  | valueExit f fs ready transitions top phase current processing context notOwner =>
      refine ⟨refs.routes, refs.checked, refs.published, refs.ready, refs.valueReady, refs.owners, ?_⟩
      intro receipt member
      rcases List.mem_append.mp member with old | new
      · exact refs.receipts receipt old
      · have eq : receipt = .value ready := by simpa using new
        subst receipt; exact refs.valueReady ready.route.work ready context
  | control | intern | task | beginSettlement | merge | endSettlement =>
      exact ⟨refs.routes, refs.checked, refs.published, refs.ready, refs.valueReady, refs.owners, refs.receipts⟩

theorem run_references {t : Tables} {s : State t} (run : Run t (initial t) s) :
    References s (RouteValid s) := by
  induction run with
  | nil => exact initial_references t
  | snoc run event ih =>
      exact step_references event (run_publications run (initial_publications t)) ih

/-- Full readback of the original queued occurrence, its actual Derived edge,
all earlier discharged checks, and its canonical processing body's recipe. -/
theorem quiescent_original_context_readback {t : Tables} {s : State t}
    (run : Run t (initial t) s) (queue : s.control.queue = [])
    (stack : s.control.frames = []) :
    ∀ w ∈ s.control.issued, ∃ receipt ∈ s.receipts,
      receipt.work = w ∧ Resolved s receipt ∧ RouteValid s receipt.route := by
  intro w issued
  obtain ⟨receipt, member, same, resolved⟩ := quiescent_issued_readback run queue stack w issued
  exact ⟨receipt, member, same, resolved, (run_references run).receipts receipt member⟩

theorem effect_receipt_original_body {t : Tables} {s : State t}
    (run : Run t (initial t) s) (cut : NoCurrent s) {ready : Ready t} {owner : Owner t}
    (receipt : Receipt.effect ready owner ∈ s.receipts) :
    (∃ body, (owner, body) ∈ s.seals ∧ ready.route.target = .effect body.key ∧
      BodyRecipe t body.key body.body) ∧
    (∀ packet, ready.route.previous = some packet → ready.route.source = .effect packet.key ∧
      FreshChecks packet ∧ packet.segment.parsed.filters ≠ []) ∧
    (∀ edge ∈ ready.route.derived, edge ∈ s.edges) ∧
    (ready.packet.key.sources = ready.route.source.sources ∧
      ready.packet.key.transformer = ready.route.source.transformer ∧
      ready.route.source.demand = none) := by
  obtain ⟨body, stored, _, target, built⟩ := receipt_resolved_at_cut run cut receipt
  have route := (run_references run).receipts _ receipt
  have payload := readback_whole_payload ready
  exact ⟨⟨body, stored, target, built⟩, route.1, route.2,
    payload.1, payload.2.1, payload.2.2.symm⟩

abbrev Journal (t : Tables) := NativeExecutionHistory.State (State t)

def jointAddress : NativeExecutionHistory.Address := ⟨0, 0⟩

def journalSeed (t : Tables) : Journal t :=
  NativeExecutionHistory.commit (NativeExecutionHistory.allocate NativeExecutionHistory.empty 0 (initial t))

theorem journal_seed_cell (t : Tables) :
    (journalSeed t).table jointAddress = some ⟨0, initial t⟩ := by
  simp [journalSeed, jointAddress, NativeExecutionHistory.commit,
    NativeExecutionHistory.allocate, NativeExecutionHistory.empty, NativeExecutionHistory.put]

theorem journal_seed_well (t : Tables) : NativeExecutionHistory.WellFormed (journalSeed t) := by
  exact NativeExecutionHistory.commit_wellFormed
    (NativeExecutionHistory.step_wellFormed NativeExecutionHistory.empty_wellFormed
      (.allocate _ 0 (initial t) rfl))

theorem execution_append {A : Type} {s u v : NativeExecutionHistory.State A}
    {first last : List (NativeExecutionHistory.Event A)}
    (left : NativeExecutionHistory.Exec s first u) (right : NativeExecutionHistory.Exec u last v) :
    NativeExecutionHistory.Exec s (first ++ last) v := by
  induction left with
  | nil => exact right
  | cons event rest ih => exact .cons event (ih right)

/-- One journal update contains the entire shared projection. The old cell is
read by the journal, and the new cell is obtained by a concrete driver step. -/
inductive Transaction (t : Tables) : Journal t → Journal t → Prop
  | nil (s : Journal t) : Transaction t s s
  | snoc {saved current : Journal t} (prior : Transaction t saved current)
      (before : NativeExecutionHistory.Cell (State t)) (next : State t)
      (actual : current.table jointAddress = some before) (event : Step t before.value next) :
      Transaction t saved (NativeExecutionHistory.update current jointAddress before next)

theorem transaction_execution {t : Tables} {saved current : Journal t}
    (transaction : Transaction t saved current) :
    ∃ events, NativeExecutionHistory.Exec saved events current := by
  induction transaction with
  | nil => exact ⟨[], .nil _⟩
  | snoc prior before next actual event ih =>
      obtain ⟨events, execution⟩ := ih
      exact ⟨events ++ [.update jointAddress next],
        execution_append execution (.cons (.update _ jointAddress before next actual) (.nil _))⟩

theorem transaction_readback {t : Tables} {saved current : Journal t}
    (transaction : Transaction t saved current) {cell : NativeExecutionHistory.Cell (State t)}
    (actual : saved.table jointAddress = some cell) (earlier : Run t (initial t) cell.value) :
    ∃ final, current.table jointAddress = some final ∧ Run t (initial t) final.value := by
  induction transaction with
  | nil => exact ⟨cell, actual, earlier⟩
  | snoc prior before next found event ih =>
      obtain ⟨last, lookup, run⟩ := ih
      have same : last = before := Option.some.inj (lookup.symm.trans found)
      subst last
      exact ⟨{ before with value := next }, by simp [NativeExecutionHistory.update,
        NativeExecutionHistory.put], .snoc run event⟩

/-- A route gets a fresh journal birth, even if cancellation later reuses its
numeric allocation frontier. The shared logical payload is updated separately. -/
inductive Attempt (t : Tables) (saved : Journal t) : Journal t → Prop
  | start (before : NativeExecutionHistory.Cell (State t)) (current : Journal t)
      (actual : saved.table jointAddress = some before)
      (fresh : saved.table ⟨1, saved.next⟩ = none)
      (transaction : Transaction t
        (NativeExecutionHistory.allocate (NativeExecutionHistory.begin saved) 1 before.value) current) :
      Attempt t saved current

theorem attempt_execution {t : Tables} {saved current : Journal t}
    (attempt : Attempt t saved current) :
    ∃ events, NativeExecutionHistory.Exec (NativeExecutionHistory.begin saved) events current := by
  cases attempt with
  | start before current actual fresh transaction =>
      obtain ⟨events, execution⟩ := transaction_execution transaction
      exact ⟨.allocate 1 before.value :: events,
        .cons (.allocate _ 1 before.value fresh) execution⟩

theorem attempt_readback {t : Tables} {saved current : Journal t}
    (attempt : Attempt t saved current) {cell : NativeExecutionHistory.Cell (State t)}
    (actual : saved.table jointAddress = some cell) (earlier : Run t (initial t) cell.value) :
    ∃ final, current.table jointAddress = some final ∧ Run t (initial t) final.value := by
  cases attempt with
  | start before current found fresh transaction =>
      have same : cell = before := Option.some.inj (actual.symm.trans found)
      subst cell
      apply transaction_readback transaction _ earlier
      simpa [NativeExecutionHistory.allocate, NativeExecutionHistory.begin,
        NativeExecutionHistory.put, jointAddress] using found

inductive Committed (t : Tables) : Journal t → Prop
  | seed : Committed t (journalSeed t)
  | commit {saved current : Journal t} : Committed t saved → Attempt t saved current →
      Committed t (NativeExecutionHistory.commit current)
  | cancel {saved current : Journal t} : Committed t saved → Attempt t saved current →
      Committed t (NativeExecutionHistory.cancel saved current)

theorem committed_readback {t : Tables} {journal : Journal t} (history : Committed t journal) :
    NativeExecutionHistory.WellFormed journal ∧
    ∃ cell, journal.table jointAddress = some cell ∧ Run t (initial t) cell.value := by
  induction history with
  | seed => exact ⟨journal_seed_well t, ⟨0, initial t⟩, journal_seed_cell t, .nil _⟩
  | commit history attempt ih =>
      obtain ⟨well, cell, actual, run⟩ := ih
      obtain ⟨events, execution⟩ := attempt_execution attempt
      obtain ⟨last, found, final⟩ := attempt_readback attempt actual run
      exact ⟨NativeExecutionHistory.commit_wellFormed
        (NativeExecutionHistory.exec_wellFormed (NativeExecutionHistory.begin_wellFormed well) execution),
        last, found, final⟩
  | cancel history attempt ih =>
      obtain ⟨well, cell, actual, run⟩ := ih
      obtain ⟨events, execution⟩ := attempt_execution attempt
      exact ⟨NativeExecutionHistory.cancel_wellFormed well execution,
        cell, by rw [NativeExecutionHistory.cancel_table_exact well execution]; exact actual, run⟩

theorem committed_quiescent_context {t : Tables} {journal : Journal t}
    (history : Committed t journal) {cell : NativeExecutionHistory.Cell (State t)}
    (actual : journal.table jointAddress = some cell)
    (queue : cell.value.control.queue = []) (stack : cell.value.control.frames = []) :
    ∀ w ∈ cell.value.control.issued, ∃ receipt ∈ cell.value.receipts,
      receipt.work = w ∧ Resolved cell.value receipt ∧ RouteValid cell.value receipt.route := by
  obtain ⟨_, retained, found, run⟩ := committed_readback history
  have same : retained = cell := Option.some.inj (found.symm.trans actual)
  subst retained
  exact quiescent_original_context_readback run queue stack

theorem cancelled_attempt_restores_joint_state {t : Tables} {saved current : Journal t}
    (history : Committed t saved) (attempt : Attempt t saved current)
    {cell : NativeExecutionHistory.Cell (State t)} (actual : saved.table jointAddress = some cell) :
    (NativeExecutionHistory.cancel saved current).table jointAddress = some cell ∧
      (NativeExecutionHistory.cancel saved current).clock = current.clock := by
  have well := (committed_readback history).1
  obtain ⟨events, execution⟩ := attempt_execution attempt
  exact ⟨by rw [NativeExecutionHistory.cancel_table_exact well execution]; exact actual, rfl⟩

theorem cancelled_attempt_birth_not_reused {t : Tables} {saved current : Journal t}
    (attempt : Attempt t saved current) :
    saved.clock < (NativeExecutionHistory.cancel saved current).clock := by
  cases attempt with
  | start before current actual fresh transaction =>
      obtain ⟨events, execution⟩ := transaction_execution transaction
      have later := (NativeExecutionHistory.exec_monotone execution).2
      change saved.clock + 1 ≤ current.clock at later
      change saved.clock < current.clock
      omega

def Settlement {t : Tables} (s : State t) : Prop := s.settling = true →
  ∃ f fs, s.control.frames = f :: fs ∧ f.phase = .working ∧ f.current = none

theorem step_settlement {t : Tables} {s u : State t} (event : Step t s u)
    (inv : Settlement s) : Settlement u := by
  cases event with
  | control next event administrative settlement =>
      intro active
      obtain ⟨f, fs, top, phase, current⟩ := inv active
      exact ⟨f, fs, (settlement active).trans top, phase, current⟩
  | transport f fs w processing source raw top phase current before relation task pair interned valid unchanged =>
      intro active
      obtain ⟨old, outer, frame, _, empty⟩ := inv active
      have same := List.cons.inj (top.symm.trans frame)
      have impossible : f.current = none := by simpa [same.1] using empty
      rw [impossible] at current
      cases current
  | finish f fs owner a levels body transitions top phase current processing owned result =>
      intro active
      exact ⟨_, fs, rfl, phase, rfl⟩
  | duplicate f fs ready memo raw transitions top phase current processing context task typed found generation notOwner =>
      intro active
      exact ⟨_, fs, rfl, phase, rfl⟩
  | valueExit f fs ready transitions top phase current processing context notOwner =>
      intro active
      exact ⟨_, fs, rfl, phase, rfl⟩
  | beginSettlement f fs top phase current queue notSettling =>
      intro active; exact ⟨f, fs, top, phase, current⟩
  | endSettlement => simp [Settlement]
  | intern | task | contextEmpty | contextCheck | publish | sample | contextCached | contextValue |
      admit | merge => exact inv

theorem run_settlement {t : Tables} {s : State t} (run : Run t (initial t) s) : Settlement s := by
  induction run with
  | nil => simp [Settlement, initial]
  | snoc _ event ih => exact step_settlement event ih

theorem merge_session_has_actual_cut {t : Tables} {s : State t}
    (run : Run t (initial t) s) (active : s.settling = true) :
    ∃ f fs, s.control.frames = f :: fs ∧ f.phase = .working ∧ f.current = none :=
  run_settlement run active

def Prefix.children (p : Prefix) : List Key := p.checks.flatMap fun c => c.leaf.childKeys

def ChildPayload (t : Tables) (parent child : Key) : Prop :=
  child.context = NativeReplayCurrent.sourceContext (admissionTables t) child.upper ∧
  child.sources = parent.sources ∧ child.transformer = parent.transformer ∧
  (child.transformer = 0 ∨ child.lower ≠ child.upper)

theorem prepare_parsed_exact {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {key : Key} {parsed : Parsed} {p : Prefix}
    (result : prepareParsed t a levels q key parsed = some p) :
    p.parsed = parsed ∧
    Aligned (fun weight check => checkFilter t a levels q key weight = some check)
      parsed.filters p.checks := by
  unfold prepareParsed at result
  split at result
  · obtain ⟨checks, collected, same⟩ := Option.bind_eq_some_iff.mp result
    have eq : p = (⟨parsed, checks, if parsed.filters = [] then key.context else parsed.residual,
      consumed (currentPair q key).2 checks⟩ : Prefix) := Option.some.inj same.symm
    subst p
    exact ⟨rfl, collect_exact _ collected⟩
  · cases result

theorem prepare_children_payload {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {fuel : Nat} {key : Key} {p : Prefix}
    (result : prepare t a levels q fuel key = some p) :
    ∀ child ∈ p.children, ChildPayload t key child := by
  unfold prepare at result
  split at result
  · obtain ⟨parsed, _, computed⟩ := Option.bind_eq_some_iff.mp result
    have exactChecks := (prepare_parsed_exact computed).2
    intro child member
    obtain ⟨check, selected, contains⟩ := List.mem_flatMap.mp member
    obtain ⟨weight, _, called⟩ := aligned_member_right exactChecks selected
    obtain ⟨_, payload, _, _, _, applied⟩ := check_filter_exact called
    cases leaf : check.leaf with
    | localReturn => simp [leaf, Leaf.childKeys] at contains
    | bound => simp [leaf, Leaf.childKeys] at contains
    | conflict => simp [leaf, Leaf.childKeys] at contains
    | children keys =>
        rw [leaf] at applied
        have contained : child ∈ keys := by simpa [leaf, Leaf.childKeys] using contains
        have provenance := whole_child_payload (filter_children_from_apply applied) child contained
        exact ⟨provenance.1, provenance.2.1, provenance.2.2.1, provenance.2.2.2.1⟩
  · cases result

theorem transported_prefix_children (q : Nat → Nat) (post : Key → Nat) (p : Prefix) :
    (p.transport q post).children = p.children := by
  simp [Prefix.children, Prefix.transport, List.flatMap_map]

theorem recipe_prefix_children {t : Tables} {key : Key} {p : Prefix}
    (recipe : PrefixRecipe t key p) : ∀ child ∈ p.children, ChildPayload t key child := by
  induction recipe with
  | checked a levels q fuel p result => exact prepare_children_payload result
  | transported prior q post ih => simpa [transported_prefix_children] using ih

theorem recipe_body_children {t : Tables} {key : Key} {body : Body}
    (recipe : BodyRecipe t key body) : ∀ child ∈ body.children, ChildPayload t key child := by
  induction recipe with
  | transported prior q post ih => simpa using ih
  | finished origin a levels q body result =>
      rename_i p
      have prefixChildren := recipe_prefix_children origin
      unfold finishPrefix at result
      split at result
      · cases result
        simpa [Body.children, Body.leaves, Prefix.children, List.flatMap_map] using prefixChildren
      · cases applied : applyEffect t a levels q key p.postContext (currentPair q key) with
        | none => simp [applied] at result
        | some leaf =>
            simp only [applied, Option.map_some, Option.some.injEq] at result
            subst body
            intro child member
            have split : child ∈ p.children ∨ child ∈ leaf.childKeys := by
              simpa [Body.children, Body.leaves, Prefix.children, List.flatMap_append,
                List.flatMap_map] using member
            rcases split with checked | residual
            · exact prefixChildren child checked
            · cases leaf with
              | localReturn => cases residual
              | bound => cases residual
              | conflict => cases residual
              | children keys =>
                  have provenance := whole_child_payload applied child residual
                  exact ⟨provenance.1, provenance.2.1, provenance.2.2.1, provenance.2.2.2.1⟩

theorem resolved_body_whole_child_provenance {t : Tables} {s : State t}
    (run : Run t (initial t) s) (cut : NoCurrent s) {ready : Ready t} {owner : Owner t}
    (receipt : Receipt.effect ready owner ∈ s.receipts) :
    ∃ body, (owner, body) ∈ s.seals ∧ ready.route.target = .effect body.key ∧
      ∀ child ∈ body.body.children, ChildPayload t body.key child := by
  obtain ⟨body, stored, _, target, built⟩ := receipt_resolved_at_cut run cut receipt
  exact ⟨body, stored, target, recipe_body_children built⟩

theorem finish_scan_empty {s : Scan} {p : Parsed} (result : finish s = some p) : s.pending = [] := by
  unfold finish at result
  split at result
  · rename_i valid; exact valid.1
  · cases result

theorem scan_result_unique {t : Tables} {s : Scan} {left right : Parsed}
    (first : ScanRun t s left) (second : ScanRun t s right) : left = right := by
  induction first with
  | done result =>
      cases second with
      | done other => exact Option.some.inj (result.symm.trans other)
      | step pending next rest => exact (pending (finish_scan_empty result)).elim
  | step pending next rest ih =>
      cases second with
      | done result => exact (pending (finish_scan_empty result)).elim
      | step pending' next' rest' =>
          have same := Option.some.inj (next.symm.trans next')
          subst same
          exact ih rest'

theorem parser_fuel_independent {t : Tables} {firstFuel secondFuel context : Nat}
    {left right : Parsed} (first : parse t firstFuel context = some left)
    (second : parse t secondFuel context = some right) : left = right :=
  scan_result_unique (scan_computes_run first) (scan_computes_run second)

theorem nonempty_prepare_parser {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {fuel : Nat} {key : Key} {p : Prefix}
    (result : prepare t a levels q fuel key = some p) (nonempty : p.parsed.filters ≠ []) :
    key.context ≠ 0 ∧ parse t fuel key.context = some p.parsed := by
  unfold prepare at result
  split at result
  · obtain ⟨parsed, parser, checked⟩ := Option.bind_eq_some_iff.mp result
    have same := (prepare_parsed_exact checked).1
    by_cases identity : key.context = 0
    · simp [identity] at parser
      rw [same, ← parser] at nonempty
      exact (nonempty rfl).elim
    · refine ⟨identity, ?_⟩
      simp only [identity, ↓reduceIte] at parser
      split at parser
      · simpa [same] using parser
      · cases parser
  · cases result

theorem cached_parser_readback {t : Tables} {packet : PrefixPacket t}
    (fresh : FreshChecks packet) (nonempty : packet.segment.parsed.filters ≠ [])
    {fuel : Nat} {parsed : Parsed} (current : parse t fuel packet.key.context = some parsed) :
    parsed = packet.segment.parsed := by
  obtain ⟨a, levels, q, firstFuel, result⟩ := fresh
  have earlier := (nonempty_prepare_parser result nonempty).2
  exact parser_fuel_independent current earlier

namespace LifetimeBoundary

/-- Native rollback truncates this raw Context slot; a later constructor can
reuse it. These are two legal parser inputs, not a source-program refutation. -/
def first : Tables :=
  { contexts := fun id => if id = 1 then some (.prefix 1 0) else none
    weights := fun id => if id = 1 then some ⟨[], 7, 0, 0, [], []⟩ else none
    views := fun id => if id = 7 then some ⟨[], none, some 1, 0, 0⟩ else none
    contributions := fun _ => none
    prefixIdentity := fun _ => 1 }

def reused : Tables := { first with contexts := fun id => if id = 1 then some (.swap 0) else none }

theorem two_successful_parses :
    parse first 3 1 = some ⟨[1], 0, false, false, false⟩ ∧
    parse reused 3 1 = some ⟨[], 1, false, true, false⟩ := by decide

theorem no_single_raw_table :
    ¬ ∃ t : Tables, t.contexts 1 = first.contexts 1 ∧ t.contexts 1 = reused.contexts 1 := by
  rintro ⟨t, first, second⟩
  have impossible := first.symm.trans second
  cases impossible

end LifetimeBoundary

namespace Witness

def tables : Tables := ⟨fun _ => none, fun _ => none, fun _ => none, fun _ => none, fun _ => 0⟩
def available : Availability :=
  ⟨true, true, fun _ => false, fun _ => true, fun _ => true,
    fun _ => true, fun _ => true, fun _ => true, true⟩
def key : Key := ⟨.bottom, .emptyNegative, 0, some 9, 2⟩
def raw : Task := .effect key.lower key.upper
def relationState : State tables := { initial tables with relations := put (fun _ => none) 0 (.effect key) }
def registered : State tables := { relationState with tasks := put (fun _ => none) 0 raw }
def work : Work := ⟨0, 0, 0, none⟩
def frame : Frame := { birth := 0, index := 0 }
def startedControl : Control :=
  { NativeDrainOwnership.pushWork NativeDrainOwnership.initial work false with
    frames := [frame], nextBirth := 1 }
def started : State tables := controlOnly registered startedControl
def activeFrame : Frame := { frame with current := some work, processing := some 0 }
def activeControl : Control := { startedControl with queue := [], frames := [activeFrame] }
def active : State tables := controlOnly started activeControl
def route : Route tables := makeRoute active work 0 (.effect key)
def transported : State tables :=
  { active with
    control := { active.control with frames := [{ activeFrame with processing := some 0 }] }
    routes := put active.routes work route
    edges := active.edges ++ route.derived }
def segment : Prefix := ⟨⟨[], 0, false, false, false⟩, [], 0, false⟩
def ready : Ready tables :=
  ⟨route, ⟨key, segment, .checked available (fun _ => 0) id 0 segment rfl⟩, rfl⟩
def contextual : State tables := { transported with ready := put transported.ready work ready }
def admitted : State tables := admitOwner contextual ready raw

theorem active_memo_run : Run tables (initial tables) admitted := by
  have r1 : Run tables (initial tables) relationState := .snoc (.nil _)
    (.intern _ 0 (.effect key) rfl (by intro old; simp [initial]) (by decide))
  have r2 : Run tables (initial tables) registered := .snoc r1 (.task _ 0 raw rfl)
  have r3 : Run tables (initial tables) started := .snoc r2
    (.control _ startedControl (.begin _ 0 0 rfl) rfl (by simp [registered, relationState, initial]))
  have r4 : Run tables (initial tables) active := .snoc r3
    (.control _ activeControl (.takePlain _ frame [] work [] rfl rfl rfl rfl rfl) rfl
      (by simp [started, controlOnly, registered, relationState, initial]))
  have r5 : Run tables (initial tables) transported := .snoc r4
    (.transport _ activeFrame [] work 0 (.effect key) raw rfl rfl rfl rfl rfl rfl rfl rfl
      (by decide) (fun _ => rfl))
  have r6 : Run tables (initial tables) contextual := .snoc r5
    (.contextEmpty _ activeFrame [] route key available (fun _ => 0) 0 segment
      rfl rfl rfl rfl rfl rfl rfl)
  exact .snoc r6 (.admit _ activeFrame [] ready raw rfl rfl rfl rfl rfl rfl rfl rfl)

theorem active_memo_is_not_completed :
    admitted.memo (0, key) = some ⟨0, ⟨ready⟩⟩ ∧ admitted.seals = [] ∧
      LiveWork admitted.control work := by
  refine ⟨rfl, rfl, ?_⟩
  exact ⟨activeFrame, by simp [admitted, admitOwner, contextual, transported, active,
    controlOnly, activeControl, activeFrame], rfl⟩

end Witness

end YulangClosure.NativeContextReadback
