import YulangClosure.NativeContextExpansion
import YulangClosure.NativeExecutionHistory
import YulangClosure.NativeValuePorts
import YulangClosure.NativeContextReadback

/-!
Native-indexed, allocation-stamped Context/weight/View/contribution storage.
Prefix identity is the actual expression-interner lookup, not a fixed external
array. Source computations are interpreted at their observed store version.
-/
namespace YulangClosure.NativeContextTables

open NativeContextExpansion
open NativeMergeExpansion (Key Endpoint Polarity)

structure Cell (A : Type) where
  birth : Nat
  value : A
  deriving DecidableEq, Repr

def values (xs : List (Cell A)) : List A := xs.map Cell.value

def internCell [DecidableEq A] (xs : List (Cell A)) (clock : Nat) (value : A) :
    List (Cell A) × Nat × Nat :=
  if value ∈ values xs then (xs, (values xs).idxOf value, clock)
  else (xs ++ [⟨clock, value⟩], xs.length, clock + 1)

theorem intern_values [DecidableEq A] (xs : List (Cell A)) (clock : Nat) (value : A) :
    values (internCell xs clock value).1 = (NativeValuePorts.intern (values xs) value).1 ∧
    (internCell xs clock value).2.1 = (NativeValuePorts.intern (values xs) value).2 := by
  unfold internCell NativeValuePorts.intern
  split <;> simp [values]

theorem intern_cell_constructed [DecidableEq A] (xs : List (Cell A)) (clock : Nat) (value : A) :
    ∃ cell, (internCell xs clock value).1[(internCell xs clock value).2.1]? = some cell ∧
      cell.value = value := by
  have payload := NativeValuePorts.intern_found (values xs) value
  rw [← (intern_values xs clock value).1, ← (intern_values xs clock value).2] at payload
  simp only [values, List.getElem?_map] at payload
  exact Option.map_eq_some_iff.mp payload

theorem intern_preserves_cells [DecidableEq A] (xs : List (Cell A)) (clock : Nat) (value : A) :
    NativeValuePorts.Extends xs (internCell xs clock value).1 := by
  intro index old found
  unfold internCell
  split
  · exact found
  · obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
    simpa [List.getElem?_append_left bound] using found

theorem intern_clock [DecidableEq A] (xs : List (Cell A)) (clock : Nat) (value : A) :
    clock ≤ (internCell xs clock value).2.2 := by
  unfold internCell
  split <;> simp

theorem intern_fresh_birth [DecidableEq A] (xs : List (Cell A)) (clock : Nat) (value : A)
    (fresh : value ∉ values xs) :
    (internCell xs clock value).1[xs.length]? = some ⟨clock, value⟩ ∧
    (internCell xs clock value).2.1 = xs.length ∧
    (internCell xs clock value).2.2 = clock + 1 := by
  simp [internCell, fresh]

structure AttachmentSource where
  polarity : Polarity
  scope : Nat
  deriving DecidableEq, Repr

structure AttachmentSet where
  source : AttachmentSource
  ordinals : List Nat
  unitPush : Bool
  deriving DecidableEq, Repr

structure WeightRecord where
  payload : Weight
  attachment : Option AttachmentSet
  deriving DecidableEq, Repr

structure OperationOrigin where
  declaration : Nat
  occurrence : Nat
  retainedBytes : Nat
  deriving DecidableEq, Repr

inductive ViewOrigin where
  | annotation
  | operation (origin : OperationOrigin)
  deriving DecidableEq, Repr

structure ViewRecord where
  payload : View
  sourceWeight : Option Nat
  origin : ViewOrigin
  deriving DecidableEq, Repr

structure Contribution where
  effect : Nat
  origin : Nat
  instanceId : Nat
  deriving DecidableEq, Repr

structure ViewInput where
  owner : Nat
  position : Nat
  allowed : List Nat
  tail : Option Nat
  operation : Option OperationOrigin
  attachment : Option AttachmentSource
  deriving DecidableEq, Repr

def ViewInput.needsWeight (v : ViewInput) : Bool :=
  v.operation.isNone && (v.tail.isNone || v.attachment.isSome)

inductive DraftStage where
  | reserved | weighted | published
  deriving DecidableEq, Repr

structure Draft where
  index : Nat
  birth : Nat
  input : ViewInput
  weight : Option Nat
  stage : DraftStage
  deriving DecidableEq, Repr

structure Store where
  contexts : List (Cell Expr) := []
  weights : List (Cell WeightRecord) := []
  views : List (Cell ViewRecord) := []
  contributions : List (Cell Contribution) := []
  pending : Option Draft := none
  clock : Nat := 0
  version : Nat := 0
  deriving DecidableEq, Repr

def Store.contextAt (s : Store) (id : Nat) : Option (Cell Expr) :=
  if id = 0 then none else s.contexts[id - 1]?

def Store.prefixAt (s : Store) (weight : Nat) : Nat :=
  let expression := Expr.prefix weight 0
  if expression ∈ values s.contexts then (values s.contexts).idxOf expression + 1 else 0

def Store.tables (s : Store) : Tables :=
  { contexts := fun id => (s.contextAt id).map Cell.value
    weights := fun id => (s.weights[id]?).map fun cell => cell.value.payload
    views := fun id => (s.views[id]?).map fun cell => cell.value.payload
    contributions := fun id => (s.contributions[id]?).map fun cell => cell.value.effect
    prefixIdentity := s.prefixAt }

def Store.intern (s : Store) (node : Expr) : Store × Nat :=
  let result := internCell s.contexts s.clock node
  ({ s with contexts := result.1, clock := result.2.2, version := s.version + 1 }, result.2.1 + 1)

def Store.reserveView (s : Store) (input : ViewInput) : Store :=
  { s with
    clock := s.clock + 1
    version := s.version + 1
    pending := some ⟨s.views.length, s.clock, input, none,
      if input.needsWeight then .reserved else .weighted⟩ }

def weightRecord (draft : Draft) : WeightRecord :=
  { payload := ⟨draft.input.allowed, draft.index, draft.input.owner, draft.input.position, [], []⟩
    attachment := draft.input.attachment.map fun source =>
      ⟨source, List.range draft.input.allowed.length,
        decide (source.polarity = .positive) && !draft.input.allowed.isEmpty⟩ }

def Store.appendWeight (s : Store) (draft : Draft) : Store :=
  { s with
    weights := s.weights ++ [⟨s.clock, weightRecord draft⟩]
    clock := s.clock + 1
    version := s.version + 1
    pending := some { draft with weight := some s.weights.length, stage := .weighted } }

def viewRecord (draft : Draft) : ViewRecord :=
  { payload := ⟨draft.input.allowed, draft.input.tail,
      if draft.input.tail.isNone then draft.weight else none,
      draft.input.owner, draft.input.position⟩
    sourceWeight := draft.weight
    origin := match draft.input.operation with | none => .annotation | some o => .operation o }

def Store.publishView (s : Store) (draft : Draft) : Store :=
  { s with
    views := s.views ++ [⟨draft.birth, viewRecord draft⟩]
    version := s.version + 1
    pending := some { draft with stage := .published } }

def Store.finishView (s : Store) : Store := { s with pending := none, version := s.version + 1 }

def Store.contribution (s : Store) (effect origin : Nat) : Store × Nat :=
  ({ s with
      contributions := s.contributions ++ [⟨s.clock, ⟨effect, origin, s.contributions.length⟩⟩]
      clock := s.clock + 1
      version := s.version + 1 }, s.contributions.length)

def validateView (s : Store) (weight id : Nat) (view : ViewRecord) : Bool :=
  match s.weights[weight]? with
  | none => false
  | some cell => decide (cell.value.payload.boundary = id ∧
      cell.value.payload.owner = view.payload.owner ∧
      cell.value.payload.position = view.payload.position ∧
      cell.value.payload.allowed = view.payload.allowed ∧
      view.sourceWeight = some weight ∧
      view.payload.closedWeight = if view.payload.tail.isNone then some weight else none)

def copyInput (s : Store) (id : Nat) (tail : Option Nat) : Option ViewInput := do
  let cell ← s.views[id]?
  let attachment ← match cell.value.sourceWeight with
    | none => if cell.value.payload.closedWeight.isSome then none else some none
    | some weight =>
        if validateView s weight id cell.value then
          some ((s.weights[weight]?).bind fun w => w.value.attachment.map AttachmentSet.source)
        else none
  pure ⟨cell.value.payload.owner, cell.value.payload.position, cell.value.payload.allowed, tail,
    (match cell.value.origin with | .annotation => none | .operation origin => some origin), attachment⟩

inductive Lane where
  | context | weight | view | contribution
  deriving DecidableEq, Repr

structure Handle where
  lane : Lane
  raw : Nat
  birth : Nat
  deriving DecidableEq, Repr

inductive Query where
  | context (id : Nat)
  | weight (id : Nat)
  | view (id : Nat)
  | contribution (id : Nat)
  | prefixIdentity (weight : Nat)
  deriving DecidableEq, Repr

inductive Answer where
  | missing
  | context (cell : Cell Expr)
  | weight (cell : Cell WeightRecord)
  | view (cell : Cell ViewRecord)
  | contribution (cell : Cell Contribution)
  | prefixIdentity (handle : Handle)
  deriving DecidableEq, Repr

def lookup (s : Store) : Query → Answer
  | .context id => ((s.contextAt id).map Answer.context).getD .missing
  | .weight id => ((s.weights[id]?).map Answer.weight).getD .missing
  | .view id => ((s.views[id]?).map Answer.view).getD .missing
  | .contribution id => ((s.contributions[id]?).map Answer.contribution).getD .missing
  | .prefixIdentity weight =>
      let id := s.prefixAt weight
      match s.contextAt id with
      | none => .missing
      | some cell => .prefixIdentity ⟨.context, id, cell.birth⟩

structure Observation where
  version : Nat
  query : Query
  answer : Answer
  deriving DecidableEq, Repr

def observe (s : Store) (query : Query) : Observation := ⟨s.version, query, lookup s query⟩

abbrev IndexFits (id : Nat) : Prop := id < 4294967296

/-- Actual successful constructor cuts. The draft records the source weight
before its matching View exists; sampling follows View publication. -/
inductive Step : Store → Store → Prop
  | context (s : Store) (node : Expr) (idle : s.pending = none)
      (children : ∀ child ∈ NativeValuePorts.contextInputs node, child ≤ s.contexts.length)
      (index : IndexFits (s.intern node).2) (reserved : Bool) (success : reserved = true) :
      Step s (s.intern node).1
  | reserveView (s : Store) (input : ViewInput) (idle : s.pending = none)
      (index : IndexFits s.views.length) (reserved : Bool) (success : reserved = true) :
      Step s (s.reserveView input)
  | reserveCopy (s : Store) (source : Nat) (tail : Option Nat) (input : ViewInput)
      (idle : s.pending = none) (copied : copyInput s source tail = some input)
      (index : IndexFits s.views.length) (reserved : Bool) (success : reserved = true) :
      Step s (s.reserveView input)
  | sourceWeight (s : Store) (draft : Draft) (pending : s.pending = some draft)
      (stage : draft.stage = .reserved) (needed : draft.input.needsWeight = true)
      (index : IndexFits s.weights.length) (reserved : Bool) (success : reserved = true) :
      Step s (s.appendWeight draft)
  | publishView (s : Store) (draft : Draft) (pending : s.pending = some draft)
      (stage : draft.stage = .weighted) (index : draft.index = s.views.length) :
      Step s (s.publishView draft)
  | sampleView (s : Store) (draft : Draft) (pending : s.pending = some draft)
      (stage : draft.stage = .published) (sampled : Bool) (success : sampled = true) :
      Step s s.finishView
  | contribution (s : Store) (effect origin : Nat) (idle : s.pending = none)
      (index : IndexFits s.contributions.length) (reserved : Bool) (success : reserved = true) :
      Step s (s.contribution effect origin).1

def Extends (s u : Store) : Prop :=
  NativeValuePorts.Extends s.contexts u.contexts ∧
  NativeValuePorts.Extends s.weights u.weights ∧
  NativeValuePorts.Extends s.views u.views ∧
  NativeValuePorts.Extends s.contributions u.contributions

theorem extends_refl (s : Store) : Extends s s :=
  ⟨NativeValuePorts.extends_refl _, NativeValuePorts.extends_refl _,
    NativeValuePorts.extends_refl _, NativeValuePorts.extends_refl _⟩

theorem append_extends (xs ys : List A) : NativeValuePorts.Extends xs (xs ++ ys) := by
  intro i x found
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
  simpa [List.getElem?_append_left bound] using found

theorem step_extends {s u : Store} (event : Step s u) : Extends s u := by
  cases event with
  | context node => exact ⟨intern_preserves_cells _ _ _,
      NativeValuePorts.extends_refl _, NativeValuePorts.extends_refl _, NativeValuePorts.extends_refl _⟩
  | sourceWeight => exact ⟨NativeValuePorts.extends_refl _, append_extends _ _,
      NativeValuePorts.extends_refl _, NativeValuePorts.extends_refl _⟩
  | publishView => exact ⟨NativeValuePorts.extends_refl _, NativeValuePorts.extends_refl _,
      append_extends _ _, NativeValuePorts.extends_refl _⟩
  | contribution => exact ⟨NativeValuePorts.extends_refl _, NativeValuePorts.extends_refl _,
      NativeValuePorts.extends_refl _, append_extends _ _⟩
  | reserveView | reserveCopy | sampleView => exact extends_refl s

theorem step_clock {s u : Store} (event : Step s u) : s.clock ≤ u.clock := by
  cases event with
  | context => exact intern_clock _ _ _
  | reserveView | reserveCopy | sourceWeight | contribution => exact Nat.le_succ _
  | publishView | sampleView => exact Nat.le_refl _

theorem step_version {s u : Store} (event : Step s u) : u.version = s.version + 1 := by
  cases event <;> rfl

inductive Run : Store → Store → Prop
  | nil (s : Store) : Run s s
  | snoc {s u v : Store} : Run s u → Step u v → Run s v

theorem extends_trans {s u v : Store} (first : Extends s u) (last : Extends u v) : Extends s v :=
  ⟨NativeValuePorts.extends_trans first.1 last.1,
    NativeValuePorts.extends_trans first.2.1 last.2.1,
    NativeValuePorts.extends_trans first.2.2.1 last.2.2.1,
    NativeValuePorts.extends_trans first.2.2.2 last.2.2.2⟩

theorem run_extends {s u : Store} (run : Run s u) : Extends s u := by
  induction run with
  | nil => exact extends_refl _
  | snoc _ event ih => exact extends_trans ih (step_extends event)

theorem run_clock {s u : Store} (run : Run s u) : s.clock ≤ u.clock := by
  induction run with
  | nil => exact Nat.le_refl _
  | snoc _ event ih => exact Nat.le_trans ih (step_clock event)

theorem context_constructed (s : Store) (node : Expr) :
    ∃ cell, (s.intern node).1.contextAt (s.intern node).2 = some cell ∧ cell.value = node := by
  simpa [Store.intern, Store.contextAt] using intern_cell_constructed s.contexts s.clock node

theorem source_weight_before_view (s : Store) (draft : Draft)
    (reserved : draft.index = s.views.length) :
    (s.appendWeight draft).weights[s.weights.length]? = some ⟨s.clock, weightRecord draft⟩ ∧
    (s.appendWeight draft).views[draft.index]? = none := by
  simp [Store.appendWeight, reserved]

theorem view_publication_exact (s : Store) (draft : Draft) :
    (s.publishView draft).views[s.views.length]? = some ⟨draft.birth, viewRecord draft⟩ ∧
    (viewRecord draft).sourceWeight = draft.weight ∧
    (viewRecord draft).payload.closedWeight =
      (if draft.input.tail.isNone then draft.weight else none) := by
  simp [Store.publishView, viewRecord]

/-- Every native constructor extends each storage vector by a suffix. -/
def Prefixes (s u : Store) : Prop :=
  s.contexts <+: u.contexts ∧ s.weights <+: u.weights ∧
    s.views <+: u.views ∧ s.contributions <+: u.contributions

theorem prefix_refl (xs : List A) : xs <+: xs := ⟨[], by simp⟩

theorem prefix_trans {xs ys zs : List A} (first : xs <+: ys) (last : ys <+: zs) :
    xs <+: zs := by
  obtain ⟨left, rfl⟩ := first
  obtain ⟨right, rfl⟩ := last
  exact ⟨left ++ right, by simp [List.append_assoc]⟩

theorem prefixes_refl (s : Store) : Prefixes s s :=
  ⟨prefix_refl _, prefix_refl _, prefix_refl _, prefix_refl _⟩

theorem intern_prefix [DecidableEq A] (xs : List (Cell A)) (clock : Nat) (value : A) :
    xs <+: (internCell xs clock value).1 := by
  unfold internCell
  split
  · exact prefix_refl _
  · exact ⟨_, rfl⟩

theorem step_prefixes {s u : Store} (event : Step s u) : Prefixes s u := by
  cases event with
  | context => exact ⟨intern_prefix _ _ _, prefix_refl _, prefix_refl _, prefix_refl _⟩
  | sourceWeight => exact ⟨prefix_refl _, ⟨_, rfl⟩, prefix_refl _, prefix_refl _⟩
  | publishView => exact ⟨prefix_refl _, prefix_refl _, ⟨_, rfl⟩, prefix_refl _⟩
  | contribution => exact ⟨prefix_refl _, prefix_refl _, prefix_refl _, ⟨_, rfl⟩⟩
  | reserveView | reserveCopy | sampleView => exact prefixes_refl s

theorem prefixes_trans {s u v : Store} (first : Prefixes s u) (last : Prefixes u v) :
    Prefixes s v :=
  ⟨prefix_trans first.1 last.1, prefix_trans first.2.1 last.2.1,
    prefix_trans first.2.2.1 last.2.2.1, prefix_trans first.2.2.2 last.2.2.2⟩

theorem run_prefixes {s u : Store} (run : Run s u) : Prefixes s u := by
  induction run with
  | nil => exact prefixes_refl _
  | snoc _ event ih => exact prefixes_trans ih (step_prefixes event)

structure Frontier where
  contexts : Nat
  weights : Nat
  views : Nat
  contributions : Nat
  deriving DecidableEq, Repr

def Store.frontier (s : Store) : Frontier :=
  ⟨s.contexts.length, s.weights.length, s.views.length, s.contributions.length⟩

/-- Native `drain(checkpoint..)` and `truncate(checkpoint)` operations. Context
keys, including prefixIdentity, are reconstructed from the retained vector. The
allocation clock and event version are ghost fields and never rewind. -/
def truncate (s : Store) (saved : Frontier) : Store :=
  { s with
    contexts := s.contexts.take saved.contexts
    weights := s.weights.take saved.weights
    views := s.views.take saved.views
    contributions := s.contributions.take saved.contributions
    pending := none
    version := s.version + 1 }

def cancel (saved current : Store) : Store := truncate current saved.frontier

theorem prefix_take {xs ys : List A} (segment : xs <+: ys) : ys.take xs.length = xs := by
  obtain ⟨rest, rfl⟩ := segment
  simp

theorem cancellation_vectors {saved current : Store} (run : Run saved current) :
    (cancel saved current).contexts = saved.contexts ∧
    (cancel saved current).weights = saved.weights ∧
    (cancel saved current).views = saved.views ∧
    (cancel saved current).contributions = saved.contributions := by
  have prefixes := run_prefixes run
  exact ⟨prefix_take prefixes.1, prefix_take prefixes.2.1,
    prefix_take prefixes.2.2.1, prefix_take prefixes.2.2.2⟩

theorem cancellation_all_five_tables {saved current : Store} (run : Run saved current) :
    (cancel saved current).tables = saved.tables := by
  obtain ⟨contexts, weights, views, contributions⟩ := cancellation_vectors run
  have keys : (cancel saved current).prefixAt = saved.prefixAt := by
    funext weight
    simp only [Store.prefixAt, contexts]
  simp only [Store.tables, Store.contextAt, contexts, weights, views, contributions, keys]

theorem cancellation_lookup {saved current : Store} (run : Run saved current) (query : Query) :
    lookup (cancel saved current) query = lookup saved query := by
  obtain ⟨contexts, weights, views, contributions⟩ := cancellation_vectors run
  cases query <;> simp [lookup, Store.contextAt, Store.prefixAt, contexts, weights, views, contributions]

theorem cancellation_clock_version (saved current : Store) :
    (cancel saved current).clock = current.clock ∧
    (cancel saved current).version = current.version + 1 := ⟨rfl, rfl⟩

theorem cancellation_recovers_interner {saved current : Store} (run : Run saved current)
    (weight : Nat) :
    (cancel saved current).prefixAt weight = saved.prefixAt weight := by
  simp only [Store.prefixAt, (cancellation_vectors run).1]

theorem prefix_identity_readback (s : Store) (weight : Nat) (present : s.prefixAt weight ≠ 0) :
    ∃ cell, s.contextAt (s.prefixAt weight) = some cell ∧ cell.value = .prefix weight 0 := by
  by_cases presentNode : Expr.prefix weight 0 ∈ values s.contexts
  · simp only [Store.prefixAt, presentNode, ↓reduceIte]
    have found := NativeValuePorts.intern_found (values s.contexts) (.prefix weight 0)
    simp only [NativeValuePorts.intern, presentNode, ↓reduceIte] at found
    simp only [values, List.getElem?_map] at found
    simpa [Store.contextAt, values] using Option.map_eq_some_iff.mp found
  · simp [Store.prefixAt, presentNode] at present

theorem prefix_identity_extension {s u : Store} (prefixes : Prefixes s u) (weight : Nat)
    (present : s.prefixAt weight ≠ 0) : u.prefixAt weight = s.prefixAt weight := by
  have presentNode : Expr.prefix weight 0 ∈ values s.contexts := by
    by_cases yes : Expr.prefix weight 0 ∈ values s.contexts
    · exact yes
    · simp [Store.prefixAt, yes] at present
  obtain ⟨tail, eq⟩ := prefixes.1
  have mapped : values u.contexts = values s.contexts ++ values tail := by simp [← eq, values]
  simp only [Store.prefixAt, mapped]
  simp [List.idxOf_append, presentNode]

theorem run_prefix_identity {s u : Store} (run : Run s u) (weight : Nat)
    (present : s.prefixAt weight ≠ 0) : u.prefixAt weight = s.prefixAt weight :=
  prefix_identity_extension (run_prefixes run) weight present

theorem context_extension {s u : Store} (extension : Extends s u) {id : Nat} {cell : Cell Expr}
    (found : s.contextAt id = some cell) : u.contextAt id = some cell := by
  unfold Store.contextAt at found ⊢
  split at found
  · cases found
  · rename_i nonzero
    simp only [nonzero, ↓reduceIte]
    exact extension.1 _ _ found

/-- An allocated cell keeps both payload and birth during any forward run. No
claim is made that a formerly missing query remains missing. -/
theorem allocated_lookup_extension {s u : Store} (run : Run s u) (query : Query)
    (allocated : lookup s query ≠ .missing) : lookup u query = lookup s query := by
  have extension := run_extends run
  cases query with
  | context id =>
      cases found : s.contextAt id with
      | none => simp [lookup, found] at allocated
      | some cell => simp [lookup, found, context_extension extension found]
  | weight id =>
      cases found : s.weights[id]? with
      | none => simp [lookup, found] at allocated
      | some cell => simp [lookup, found, extension.2.1 _ _ found]
  | view id =>
      cases found : s.views[id]? with
      | none => simp [lookup, found] at allocated
      | some cell => simp [lookup, found, extension.2.2.1 _ _ found]
  | contribution id =>
      cases found : s.contributions[id]? with
      | none => simp [lookup, found] at allocated
      | some cell => simp [lookup, found, extension.2.2.2 _ _ found]
  | prefixIdentity weight =>
      have nonzero : s.prefixAt weight ≠ 0 := by
        intro zero
        simp [lookup, zero, Store.contextAt] at allocated
      obtain ⟨cell, found, _⟩ := prefix_identity_readback s weight nonzero
      simp [lookup, run_prefix_identity run weight nonzero, found, context_extension extension found]

def BornBefore (clock : Nat) (cells : List (Cell A)) : Prop :=
  ∀ cell ∈ cells, cell.birth < clock

structure Fresh (s : Store) : Prop where
  contexts : BornBefore s.clock s.contexts
  weights : BornBefore s.clock s.weights
  views : BornBefore s.clock s.views
  contributions : BornBefore s.clock s.contributions
  pending : ∀ draft, s.pending = some draft → draft.birth < s.clock

theorem born_mono {xs : List (Cell A)} {clock later : Nat}
    (born : BornBefore clock xs) (mono : clock ≤ later) : BornBefore later xs := by
  intro cell member
  exact Nat.lt_of_lt_of_le (born cell member) mono

theorem born_append {xs : List (Cell A)} {clock : Nat} (born : BornBefore clock xs) (value : A) :
    BornBefore (clock + 1) (xs ++ [⟨clock, value⟩]) := by
  intro cell member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with old | rfl
  · exact Nat.lt_succ_of_lt (born cell old)
  · exact Nat.lt_succ_self _

theorem intern_born [DecidableEq A] {xs : List (Cell A)} {clock : Nat}
    (born : BornBefore clock xs) (value : A) :
    BornBefore (internCell xs clock value).2.2 (internCell xs clock value).1 := by
  unfold internCell
  split
  · exact born
  · exact born_append born value

theorem fresh_initial : Fresh ({} : Store) := by
  constructor <;> simp [BornBefore]

theorem step_fresh {s u : Store} (event : Step s u) (fresh : Fresh s) : Fresh u := by
  have mono := step_clock event
  cases event with
  | context node idle =>
      refine ⟨intern_born fresh.contexts _, born_mono fresh.weights mono,
        born_mono fresh.views mono, born_mono fresh.contributions mono, ?_⟩
      simp [Store.intern, idle]
  | reserveView input | reserveCopy _ _ input =>
      refine ⟨born_mono fresh.contexts mono, born_mono fresh.weights mono,
        born_mono fresh.views mono, born_mono fresh.contributions mono, ?_⟩
      intro draft found
      simp only [Store.reserveView, Option.some.injEq] at found
      subst draft
      exact Nat.lt_succ_self _
  | sourceWeight draft pending =>
      refine ⟨born_mono fresh.contexts mono, born_append fresh.weights _,
        born_mono fresh.views mono, born_mono fresh.contributions mono, ?_⟩
      intro next found
      simp only [Store.appendWeight, Option.some.injEq] at found
      subst next
      exact Nat.lt_succ_of_lt (fresh.pending draft pending)
  | publishView draft pending =>
      refine ⟨fresh.contexts, fresh.weights, ?_, fresh.contributions, ?_⟩
      · intro cell member
        simp only [Store.publishView, List.mem_append, List.mem_singleton] at member
        rcases member with old | rfl
        · exact fresh.views cell old
        · exact fresh.pending draft pending
      · intro next found
        simp only [Store.publishView, Option.some.injEq] at found
        subst next
        exact fresh.pending draft pending
  | sampleView =>
      exact ⟨fresh.contexts, fresh.weights, fresh.views, fresh.contributions, by simp [Store.finishView]⟩
  | contribution _ _ idle =>
      refine ⟨born_mono fresh.contexts mono, born_mono fresh.weights mono,
        born_mono fresh.views mono, born_append fresh.contributions _, ?_⟩
      simp [Store.contribution, idle]

theorem run_fresh {s u : Store} (run : Run s u) (fresh : Fresh s) : Fresh u := by
  induction run with
  | nil => exact fresh
  | snoc _ event ih => exact step_fresh event ih

theorem cancel_fresh {saved current : Store} (run : Run saved current)
    (fresh : Fresh saved) : Fresh (cancel saved current) := by
  obtain ⟨contexts, weights, views, contributions⟩ := cancellation_vectors run
  have mono := run_clock run
  constructor
  · change BornBefore current.clock _
    rw [contexts]
    exact born_mono fresh.contexts mono
  · change BornBefore current.clock _
    rw [weights]
    exact born_mono fresh.weights mono
  · change BornBefore current.clock _
    rw [views]
    exact born_mono fresh.views mono
  · change BornBefore current.clock _
    rw [contributions]
    exact born_mono fresh.contributions mono
  · simp [cancel, truncate]

/-- A retry can reuse the raw Context index, but cannot reuse any birth from
the cancelled attempt's allocated cells. -/
theorem retry_context_birth {saved current : Store} (run : Run saved current)
    (fresh : Fresh saved) (node : Expr)
    (absent : node ∉ values saved.contexts) (old : Cell Expr) (allocated : old ∈ current.contexts) :
    ((cancel saved current).intern node).2 = saved.contexts.length + 1 ∧
    ∃ cell, ((cancel saved current).intern node).1.contextAt
      (saved.contexts.length + 1) = some cell ∧ cell.value = node ∧ old.birth < cell.birth := by
  have vectors := cancellation_vectors run
  have new := intern_fresh_birth (cancel saved current).contexts current.clock node
    (by simpa [vectors.1] using absent)
  have born := (run_fresh run fresh).contexts old allocated
  refine ⟨?_, ⟨⟨current.clock, node⟩, ?_, rfl, born⟩⟩
  · change (internCell (cancel saved current).contexts current.clock node).2.1 + 1 = _
    rw [new.2.1, vectors.1]
  · change (if saved.contexts.length + 1 = 0 then none else
      (internCell (cancel saved current).contexts current.clock node).1[saved.contexts.length + 1 - 1]?) = _
    simpa only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, vectors.1] using new.1

inductive History : Store → Prop
  | initial : History {}
  | commit {saved current : Store} : History saved → Run saved current →
      current.pending = none → History current
  | cancel {saved current : Store} : History saved → Run saved current → History (cancel saved current)

theorem history_fresh {s : Store} (history : History s) : Fresh s := by
  induction history with
  | initial => exact fresh_initial
  | commit _ run _ ih => exact run_fresh run ih
  | cancel _ run ih => exact cancel_fresh run ih

theorem history_idle {s : Store} (history : History s) : s.pending = none := by
  cases history with
  | initial => rfl
  | commit _ _ idle => exact idle
  | cancel => rfl

/-- Only successful allocated reads are stable. This is supplied by native
constructors; it deliberately permits `none` to become `some` after allocation. -/
structure TableExtension (before after : Tables) : Prop where
  contexts : ∀ id value, before.contexts id = some value → after.contexts id = some value
  weights : ∀ id value, before.weights id = some value → after.weights id = some value
  views : ∀ id value, before.views id = some value → after.views id = some value
  contributions : ∀ id value, before.contributions id = some value → after.contributions id = some value
  prefixIdentity : ∀ weight, before.prefixIdentity weight ≠ 0 →
    after.prefixIdentity weight = before.prefixIdentity weight

theorem mapped_success {f : A → B} {before after : Option A}
    (preserved : ∀ value, before = some value → after = some value) {value : B}
    (found : before.map f = some value) : after.map f = some value := by
  obtain ⟨cell, actual, payload⟩ := Option.map_eq_some_iff.mp found
  simp [preserved cell actual, payload]

theorem run_table_extension {s u : Store} (run : Run s u) : TableExtension s.tables u.tables := by
  have ext := run_extends run
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro id value found
    exact mapped_success (fun _ found => context_extension ext found) found
  · intro id value found
    exact mapped_success (ext.2.1 id) found
  · intro id value found
    exact mapped_success (ext.2.2.1 id) found
  · intro id value found
    exact mapped_success (ext.2.2.2 id) found
  · exact run_prefix_identity run

theorem valid_weight_extension {t u : Tables} (ext : TableExtension t u) {weight : Nat}
    (valid : weightValid t weight = true) : weightValid u weight = true := by
  cases payload : t.weights weight with
  | none => simp [weightValid, payload] at valid
  | some w =>
      cases view : t.views w.boundary with
      | none => simp [weightValid, payload, view] at valid
      | some v =>
          simpa only [weightValid, payload, view, ext.weights _ _ payload,
            ext.views _ _ view] using valid

theorem scan_step_extension {t u : Tables} (ext : TableExtension t u) {s next : Scan}
    (result : scanStep t s = some next) : scanStep u s = some next := by
  unfold scanStep at result ⊢
  cases pending : s.pending with
  | nil => simp [pending] at result
  | cons head rest =>
      obtain ⟨id, mode⟩ := head
      simp only [pending] at result ⊢
      by_cases skipped : id = 0 ∨ (id, mode) ∈ s.visited
      · simpa [skipped] using result
      · simp only [skipped, ↓reduceIte] at result ⊢
        cases found : t.contexts id with
        | none => simp [found] at result
        | some node =>
            simp only [found, ext.contexts _ _ found] at result ⊢
            cases node with
            | «prefix» weight input =>
                by_cases guards : (mode = .outer ∨ (mode = .replay ∧ input = 0)) ∧
                    input < id ∧ weightValid t weight = true
                · have valid := valid_weight_extension ext guards.2.2
                  simpa [guards.1, guards.2.1, guards.2.2, valid] using result
                · simp [guards] at result
            | suffix input weight => exact result
            | both input certificate => exact result
            | swap input => exact result
            | without input => exact result
            | replay lower upper => exact result

theorem scan_loop_extension {t u : Tables} (ext : TableExtension t u) {fuel : Nat}
    {s : Scan} {parsed : Parsed} (result : scanLoop t fuel s = some parsed) :
    scanLoop u fuel s = some parsed := by
  induction fuel generalizing s with
  | zero => exact result
  | succ fuel ih =>
      simp only [scanLoop] at result ⊢
      by_cases empty : s.pending = []
      · simpa [empty] using result
      · simp only [empty, ↓reduceIte] at result ⊢
        obtain ⟨next, step, tail⟩ := Option.bind_eq_some_iff.mp result
        simp [scan_step_extension ext step, ih tail]

theorem parse_extension {t u : Tables} (ext : TableExtension t u) {fuel root : Nat}
    {parsed : Parsed} (result : parse t fuel root = some parsed) :
    parse u fuel root = some parsed := scan_loop_extension ext result

theorem source_extension {t u : Tables} (ext : TableExtension t u) {upper : Endpoint}
    (available : sourceAvailable t upper = true) :
    sourceAvailable u upper = true ∧
      NativeReplayCurrent.sourceContext (admissionTables u) upper =
        NativeReplayCurrent.sourceContext (admissionTables t) upper := by
  cases upper <;> try exact ⟨rfl, rfl⟩
  rename_i id
  cases found : t.views id with
  | none => simp [sourceAvailable, found] at available
  | some view =>
      cases weight : view.closedWeight with
      | none => simp [sourceAvailable, found, ext.views _ _ found, weight,
          NativeReplayCurrent.sourceContext, admissionTables]
      | some w =>
          have facts : t.prefixIdentity w ≠ 0 ∧ t.contexts (t.prefixIdentity w) = some (.prefix w 0) := by
            simpa [sourceAvailable, found, weight] using available
          have identity := ext.prefixIdentity w facts.1
          simp [sourceAvailable, found, ext.views _ _ found, weight, identity, facts.1,
            ext.contexts _ _ facts.2, NativeReplayCurrent.sourceContext, admissionTables]

theorem admit_extension {t u : Tables} (ext : TableExtension t u) {a : Availability}
    {q : Nat → Nat} {parent child : Key} {pair : NativeReplayCurrent.Pair}
    (result : admit t a q parent pair = some child) : admit u a q parent pair = some child := by
  unfold admit at result ⊢
  dsimp only at result ⊢
  split at result
  · rename_i guards
    have available : sourceAvailable t pair.2 = true :=
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp guards).1).1
    have source := source_extension ext available
    have childSame : NativeReplayCurrent.admittedChild (admissionTables u) q parent pair =
        NativeReplayCurrent.admittedChild (admissionTables t) q parent pair := by
      simp [NativeReplayCurrent.admittedChild, source.2]
    simp only [childSame, source.1, Bool.true_and]
    have rest := Bool.and_eq_true_iff.mp guards
    simp only [(Bool.and_eq_true_iff.mp rest.1).2, rest.2, Bool.and_self, ↓reduceIte]
    exact result
  · cases result

theorem collect_extension {A B : Type} {before after : A → Option B}
    (ext : ∀ input output, before input = some output → after input = some output)
    {inputs : List A} {outputs : List B} (result : collect before inputs = some outputs) :
    collect after inputs = some outputs := by
  induction inputs generalizing outputs with
  | nil => exact result
  | cons input rest ih =>
      simp only [collect] at result ⊢
      obtain ⟨head, first, tail⟩ := Option.bind_eq_some_iff.mp result
      obtain ⟨last, done, equal⟩ := Option.bind_eq_some_iff.mp tail
      simp [ext _ _ first, ih done]
      simpa using equal

theorem value_context_extension {V : Type} {t u : Tables} (ext : TableExtension t u)
    {fuel : Nat} {request output : ValueRequest V}
    (result : valueContext t fuel request = some output) :
    valueContext u fuel request = some output := by
  unfold valueContext at result ⊢
  split at result
  · cases result
  · rename_i transformer
    simp only [transformer, ↓reduceIte]
    split at result
    · rename_i identity
      simpa [identity] using result
    · rename_i nonidentity
      simp only [nonidentity, ↓reduceIte]
      obtain ⟨parsed, found, tail⟩ := Option.bind_eq_some_iff.mp result
      simpa [parse_extension ext found] using tail


theorem effect_member_extension {t u : Tables} (ext : TableExtension t u)
    {lower : Endpoint} {effect : Nat}
    (result : NativeMergeExpansion.Effect.memberEffect (effectTables t) lower = some effect) :
    NativeMergeExpansion.Effect.memberEffect (effectTables u) lower = some effect := by
  cases lower with
  | contribution id => exact ext.contributions _ _ result
  | annotationMember id member =>
      cases found : t.views id with
      | none => simp [NativeMergeExpansion.Effect.memberEffect, effectTables, found] at result
      | some view =>
          simpa [NativeMergeExpansion.Effect.memberEffect, effectTables, found, ext.views _ _ found] using result
  | row | support | allowance | bottom | emptyNegative => cases result

/-- A successful native member/allowance operand checks the closed-weight
lookup before using `closedAllowed`; this is what rules out None→Some changing
an already completed membership decision. -/
theorem closed_view_extension {t u : Tables} (ext : TableExtension t u)
    {id : Nat} {view : View} (found : t.views id = some view)
    (available : operandAvailable t (.contribution 0) (.allowance id) = true) :
    (effectTables u).views id = (effectTables t).views id := by
  cases weight : view.closedWeight with
  | none => simp [effectTables, found, ext.views _ _ found, weight]
  | some w =>
      cases payload : t.weights w with
      | none => simp [operandAvailable, found, weight, payload] at available
      | some p => simp [effectTables, found, ext.views _ _ found, weight,
          payload, ext.weights _ _ payload]

theorem member_check_extension {t u : Tables} (ext : TableExtension t u)
    {q : Nat → Nat} {lower upper : Endpoint}
    (available : operandAvailable t (.contribution 0) upper = true)
    (success : NativeMergeExpansion.Effect.checkMember q (effectTables t) lower upper ≠ .unavailable) :
    NativeMergeExpansion.Effect.checkMember q (effectTables u) lower upper =
      NativeMergeExpansion.Effect.checkMember q (effectTables t) lower upper := by
  cases upper with
  | allowance id =>
      cases member : NativeMergeExpansion.Effect.memberEffect (effectTables t) lower with
      | none => simp [NativeMergeExpansion.Effect.checkMember, member] at success
      | some effect =>
          cases found : t.views id with
          | none => simp [NativeMergeExpansion.Effect.checkMember, effectTables, found] at success
          | some view =>
              simp only [NativeMergeExpansion.Effect.checkMember, effect_member_extension ext member, member,
                closed_view_extension ext found available]
  | row | support | contribution | annotationMember | bottom | emptyNegative => rfl

theorem operand_check_extension {t u : Tables} (ext : TableExtension t u)
    {q : Nat → Nat} {lower upper : Endpoint}
    (available : operandAvailable t lower upper = true)
    (success : NativeMergeExpansion.Effect.checkOperand q (effectTables t) lower upper ≠ .unavailable) :
    NativeMergeExpansion.Effect.checkOperand q (effectTables u) lower upper =
      NativeMergeExpansion.Effect.checkOperand q (effectTables t) lower upper := by
  cases lower with
  | support id =>
      cases found : t.views id with
      | none => simp [NativeMergeExpansion.Effect.checkOperand, effectTables, found] at success
      | some view => simp [NativeMergeExpansion.Effect.checkOperand, effectTables, found, ext.views _ _ found]
  | contribution id =>
      apply member_check_extension ext
      · cases upper <;> exact available
      · exact success
  | annotationMember id member =>
      apply member_check_extension ext
      · cases upper <;> exact available
      · exact success
  | row | allowance | bottom | emptyNegative => rfl

theorem operand_available_extension {t u : Tables} (ext : TableExtension t u)
    {lower upper : Endpoint} (available : operandAvailable t lower upper = true) :
    operandAvailable u lower upper = true := by
  cases lower <;> cases upper <;> try rfl
  all_goals
    rename_i id
    cases found : t.views id with
    | none => simp [operandAvailable, found] at available
    | some view =>
        cases weight : view.closedWeight with
        | none => simp [operandAvailable, ext.views _ _ found, weight]
        | some w =>
            cases payload : t.weights w with
            | none => simp [operandAvailable, found, weight, payload] at available
            | some p => simp [operandAvailable, ext.views _ _ found, weight, ext.weights _ _ payload]

theorem apply_effect_extension {t u : Tables} (ext : TableExtension t u)
    {a : Availability} {levels q : Nat → Nat} {parent : Key} {context : Nat}
    {pair : NativeReplayCurrent.Pair} {leaf : Leaf}
    (result : applyEffect t a levels q parent context pair = some leaf) :
    applyEffect u a levels q parent context pair = some leaf := by
  unfold applyEffect at result ⊢
  by_cases equal : pair.1 = pair.2
  · simpa [equal] using result
  · simp only [equal, ↓reduceIte] at result ⊢
    cases bound : placedBound levels pair.1 pair.2 with
    | some fiber => simpa [bound] using result
    | none =>
        simp only [bound] at result ⊢
        split at result
        · rename_i available
          simp only [operand_available_extension ext available, ↓reduceIte]
          have success : NativeMergeExpansion.Effect.checkOperand q (effectTables t) pair.1 pair.2 ≠ .unavailable := by
            intro unavailable
            simp [unavailable] at result
          rw [operand_check_extension ext available success]
          cases outcome : NativeMergeExpansion.Effect.checkOperand q (effectTables t) pair.1 pair.2 with
          | localReturn | conflict => simpa [outcome] using result
          | unavailable => contradiction
          | children pairs =>
              simp only [outcome] at result ⊢
              obtain ⟨children, found, equal⟩ := Option.map_eq_some_iff.mp result
              simp [collect_extension (fun _ _ h => admit_extension ext h) found, equal]
        · cases result

theorem apply_filter_extension {t u : Tables} (ext : TableExtension t u)
    {a : Availability} {levels q : Nat → Nat} {parent : Key} {view : Nat} {leaf : Leaf}
    (result : applyFilter t a levels q parent view = some leaf) :
    applyFilter u a levels q parent view = some leaf := by
  unfold applyFilter at result ⊢
  cases lower : (NativeReplayCurrent.currentPair q parent).1 <;>
    simp only [lower] at result ⊢
  all_goals first
    | exact apply_effect_extension ext result
    | (split at result
       · rename_i registered
         simpa only [registered, ↓reduceIte] using result
       · rename_i unregistered
         simp only [unregistered]
         exact apply_effect_extension ext result)

theorem check_filter_extension {t u : Tables} (ext : TableExtension t u)
    {a : Availability} {levels q : Nat → Nat} {parent : Key} {weight : Nat} {check : Check}
    (result : checkFilter t a levels q parent weight = some check) :
    checkFilter u a levels q parent weight = some check := by
  unfold checkFilter at result ⊢
  obtain ⟨payload, found, tail⟩ := Option.bind_eq_some_iff.mp result
  simp only [ext.weights _ _ found]
  split at tail
  · rename_i valid
    simp only [valid_weight_extension ext valid, ↓reduceIte]
    obtain ⟨leaf, applied, done⟩ := Option.bind_eq_some_iff.mp tail
    simpa [apply_filter_extension ext applied] using done
  · cases tail

theorem prepare_parsed_extension {t u : Tables} (ext : TableExtension t u)
    {a : Availability} {levels q : Nat → Nat} {key : Key} {parsed : Parsed}
    {segment : NativeContextReadback.Prefix}
    (result : NativeContextReadback.prepareParsed t a levels q key parsed = some segment) :
    NativeContextReadback.prepareParsed u a levels q key parsed = some segment := by
  unfold NativeContextReadback.prepareParsed at result ⊢
  split at result
  · rename_i guard
    simp only [guard, ↓reduceIte]
    obtain ⟨checks, found, done⟩ := Option.bind_eq_some_iff.mp result
    simpa [collect_extension (fun _ _ h => check_filter_extension ext h) found] using done
  · cases result

theorem prepare_extension {t u : Tables} (ext : TableExtension t u)
    {a : Availability} {levels q : Nat → Nat} {fuel : Nat} {key : Key}
    {segment : NativeContextReadback.Prefix}
    (result : NativeContextReadback.prepare t a levels q fuel key = some segment) :
    NativeContextReadback.prepare u a levels q fuel key = some segment := by
  unfold NativeContextReadback.prepare at result ⊢
  split at result
  · rename_i entered
    simp only [entered, ↓reduceIte]
    obtain ⟨parsed, found, done⟩ := Option.bind_eq_some_iff.mp result
    have parsedAgain :
        (if key.context = 0 then some (⟨[], 0, false, false, false⟩ : Parsed)
          else if a.parser then parse u fuel key.context else none) = some parsed := by
      split at found
      · rename_i identity
        simpa [identity] using found
      · rename_i nonidentity
        simp only [nonidentity, ↓reduceIte]
        split at found
        · rename_i available
          simp only [available, ↓reduceIte]
          exact parse_extension ext found
        · cases found
    simp [parsedAgain, prepare_parsed_extension ext done]
  · cases result

theorem finish_prefix_extension {t u : Tables} (ext : TableExtension t u)
    {a : Availability} {levels q : Nat → Nat} {key : Key}
    {segment : NativeContextReadback.Prefix} {body : Body}
    (result : NativeContextReadback.finishPrefix t a levels q key segment = some body) :
    NativeContextReadback.finishPrefix u a levels q key segment = some body := by
  unfold NativeContextReadback.finishPrefix at result ⊢
  split at result
  · rename_i consumed
    simpa only [consumed, ↓reduceIte] using result
  · rename_i residual
    simp only [residual]
    obtain ⟨leaf, found, done⟩ := Option.map_eq_some_iff.mp result
    simp [apply_effect_extension ext found, done]

theorem prefix_recipe_extension {t u : Tables} (ext : TableExtension t u)
    {key : Key} {segment : NativeContextReadback.Prefix}
    (recipe : NativeContextReadback.PrefixRecipe t key segment) :
    NativeContextReadback.PrefixRecipe u key segment := by
  induction recipe with
  | checked a levels q fuel p result => exact .checked a levels q fuel p (prepare_extension ext result)
  | transported prior q post ih => exact .transported ih q post

theorem body_recipe_extension {t u : Tables} (ext : TableExtension t u)
    {key : Key} {body : Body} (recipe : NativeContextReadback.BodyRecipe t key body) :
    NativeContextReadback.BodyRecipe u key body := by
  induction recipe with
  | finished origin a levels q body result =>
      exact .finished (prefix_recipe_extension ext origin) a levels q body (finish_prefix_extension ext result)
  | transported prior q post ih => exact .transported ih q post

theorem run_trans {s u v : Store} (first : Run s u) (last : Run u v) : Run s v := by
  induction last with
  | nil => exact first
  | snoc _ event ih => exact .snoc ih event

def reservedDraft (s : Store) (input : ViewInput) : Draft :=
  ⟨s.views.length, s.clock, input, none, if input.needsWeight then .reserved else .weighted⟩

def weightedDraft (s : Store) (input : ViewInput) : Draft :=
  { reservedDraft s input with
    weight := if input.needsWeight then some s.weights.length else none
    stage := .weighted }

def Store.constructView (s : Store) (input : ViewInput) : Store :=
  let reserved := s.reserveView input
  let weighted := if input.needsWeight then reserved.appendWeight (reservedDraft s input) else reserved
  (weighted.publishView (weightedDraft s input)).finishView

theorem construct_view_tail (s : Store) (input : ViewInput)
    (weightIndex : input.needsWeight = true → IndexFits s.weights.length) :
    Run (s.reserveView input) (s.constructView input) := by
  by_cases needed : input.needsWeight = true
  · have allocate : Step (s.reserveView input)
        ((s.reserveView input).appendWeight (reservedDraft s input)) :=
      .sourceWeight _ _ rfl (by simp [reservedDraft, needed]) needed (weightIndex needed) true rfl
    have published : Step ((s.reserveView input).appendWeight (reservedDraft s input))
        (((s.reserveView input).appendWeight (reservedDraft s input)).publishView (weightedDraft s input)) :=
      .publishView _ _ (by simp [Store.appendWeight, Store.reserveView, reservedDraft, weightedDraft, needed])
        rfl rfl
    have sampled : Step
        (((s.reserveView input).appendWeight (reservedDraft s input)).publishView (weightedDraft s input))
        ((((s.reserveView input).appendWeight (reservedDraft s input)).publishView (weightedDraft s input)).finishView) :=
      .sampleView _ _ rfl rfl true rfl
    simpa only [Store.constructView, needed, Bool.false_eq_true, ↓reduceIte] using
      Run.snoc (Run.snoc (Run.snoc (.nil _) allocate) published) sampled
  · have published : Step (s.reserveView input) ((s.reserveView input).publishView (weightedDraft s input)) :=
      .publishView _ _ (by simp [Store.reserveView, reservedDraft, weightedDraft, needed]) rfl rfl
    have sampled : Step ((s.reserveView input).publishView (weightedDraft s input))
        (((s.reserveView input).publishView (weightedDraft s input)).finishView) :=
      .sampleView _ _ rfl rfl true rfl
    simpa only [Store.constructView, needed, Bool.false_eq_true, ↓reduceIte] using
      Run.snoc (Run.snoc (.nil _) published) sampled

theorem construct_view_run (s : Store) (input : ViewInput) (idle : s.pending = none)
    (viewIndex : IndexFits s.views.length)
    (weightIndex : input.needsWeight = true → IndexFits s.weights.length) :
    Run s (s.constructView input) :=
  run_trans (.snoc (.nil _) (.reserveView s input idle viewIndex true rfl))
    (construct_view_tail s input weightIndex)

theorem construct_copy_run (s : Store) (source : Nat) (tail : Option Nat) (input : ViewInput)
    (idle : s.pending = none) (copied : copyInput s source tail = some input)
    (viewIndex : IndexFits s.views.length)
    (weightIndex : input.needsWeight = true → IndexFits s.weights.length) :
    Run s (s.constructView input) :=
  run_trans (.snoc (.nil _) (.reserveCopy s source tail input idle copied viewIndex true rfl))
    (construct_view_tail s input weightIndex)

theorem construct_view_readback (s : Store) (input : ViewInput) :
    (s.constructView input).views[s.views.length]? =
      some ⟨s.clock, viewRecord (weightedDraft s input)⟩ ∧
    (s.constructView input).pending = none ∧
    (s.constructView input).contexts = s.contexts ∧
    (s.constructView input).contributions = s.contributions := by
  by_cases needed : input.needsWeight = true <;>
    simp [Store.constructView, Store.finishView, Store.publishView, Store.appendWeight,
      Store.reserveView, weightedDraft, reservedDraft, needed]

theorem construct_weight_readback (s : Store) (input : ViewInput) (needed : input.needsWeight = true) :
    (s.constructView input).weights[s.weights.length]? =
      some ⟨s.clock + 1, weightRecord (reservedDraft s input)⟩ := by
  simp [Store.constructView, Store.finishView, Store.publishView, Store.appendWeight,
    Store.reserveView, needed]

theorem constructed_closed_weight_valid (s : Store) (input : ViewInput)
    (annotation : input.operation = none) (closed : input.tail = none) :
    weightValid (s.constructView input).tables s.weights.length = true := by
  have needed : input.needsWeight = true := by simp [ViewInput.needsWeight, annotation, closed]
  have view := (construct_view_readback s input).1
  have weight := construct_weight_readback s input needed
  simp [weightValid, Store.tables, view, weight, weightRecord, viewRecord,
    reservedDraft, weightedDraft, needed, closed]

theorem constructed_view_exact_input (s : Store) (input : ViewInput) :
    (viewRecord (weightedDraft s input)).payload.allowed = input.allowed ∧
    (viewRecord (weightedDraft s input)).payload.tail = input.tail ∧
    (viewRecord (weightedDraft s input)).payload.owner = input.owner ∧
    (viewRecord (weightedDraft s input)).payload.position = input.position ∧
    (viewRecord (weightedDraft s input)).sourceWeight =
      (if input.needsWeight then some s.weights.length else none) := by
  simp [viewRecord, weightedDraft, reservedDraft]

theorem constructed_attachment_exact (s : Store) (input : ViewInput) (source : AttachmentSource)
    (attached : input.attachment = some source) :
    (weightRecord (reservedDraft s input)).attachment = some
      ⟨source, List.range input.allowed.length,
        decide (source.polarity = .positive) && !input.allowed.isEmpty⟩ := by
  simp [weightRecord, reservedDraft, attached]

theorem interner_prefix_identity (s : Store) (weight : Nat) :
    (s.intern (.prefix weight 0)).1.prefixAt weight = (s.intern (.prefix weight 0)).2 := by
  by_cases present : Expr.prefix weight 0 ∈ values s.contexts
  · simp [Store.intern, internCell, Store.prefixAt, present]
  · have absent : Expr.prefix weight 0 ∉ s.contexts.map Cell.value := present
    simp [Store.intern, internCell, Store.prefixAt, values, List.idxOf_append, absent]

theorem interned_source_available (s : Store) (view : Nat) (v : ViewRecord) (weight : Nat)
    (found : s.views[view]? = some ⟨birth, v⟩) (closed : v.payload.closedWeight = some weight) :
    sourceAvailable (s.intern (.prefix weight 0)).1.tables (.allowance view) = true := by
  obtain ⟨cell, actual, value⟩ := context_constructed s (.prefix weight 0)
  have nonzero : (s.intern (.prefix weight 0)).2 ≠ 0 := Nat.add_one_ne_zero _
  have contexts : (s.intern (.prefix weight 0)).1.tables.contexts (s.intern (.prefix weight 0)).2 =
      some (.prefix weight 0) := by simp [Store.tables, actual, value]
  have views : (s.intern (.prefix weight 0)).1.tables.views view = some v.payload := by
    simp [Store.tables, Store.intern, found]
  simp only [sourceAvailable, views, closed]
  change (decide ((s.intern (.prefix weight 0)).1.prefixAt weight ≠ 0) &&
    decide ((s.intern (.prefix weight 0)).1.tables.contexts
      ((s.intern (.prefix weight 0)).1.prefixAt weight) = some (.prefix weight 0))) = true
  rw [interner_prefix_identity]
  simp [nonzero, contexts]

def truncateContext (s : Store) (saved : Frontier) : Store :=
  { s with contexts := s.contexts.take saved.contexts, weights := s.weights.take saved.weights }

def truncateEffect (s : Store) (saved : Frontier) : Store :=
  { s with
    views := s.views.take saved.views
    contributions := s.contributions.take saved.contributions
    pending := none
    version := s.version + 1 }

theorem native_rollback_order (saved current : Store) :
    truncateEffect (truncateContext current saved.frontier) saved.frontier = cancel saved current := rfl

theorem context_rollback_can_precede_view_rollback (s : Store) (input : ViewInput)
    (_needed : input.needsWeight = true) :
    (truncateContext (s.constructView input) s.frontier).weights[s.weights.length]? = none ∧
    (truncateContext (s.constructView input) s.frontier).views[s.views.length]? =
      some ⟨s.clock, viewRecord (weightedDraft s input)⟩ := by
  constructor
  · simp [truncateContext, Store.frontier]
    omega
  · exact (construct_view_readback s input).1

/-- Local rename validates source IDs against the captured frontier, so fresh
outputs cannot make an invalid old source handle legal. -/
def renameSource (saved current : Store) (id : Nat) : Option Expr :=
  if id = 0 then none
  else if id ≤ saved.contexts.length then current.contextAt id |>.map Cell.value else none

theorem rename_source_old_frontier {saved current : Store} (run : Run saved current)
    (id : Nat) : renameSource saved current id = saved.tables.contexts id := by
  unfold renameSource Store.tables Store.contextAt
  by_cases zero : id = 0
  · simp [zero]
  · simp only [zero, ↓reduceIte]
    by_cases bound : id ≤ saved.contexts.length
    · simp only [bound, ↓reduceIte]
      have index : id - 1 < saved.contexts.length := by omega
      have found := List.getElem?_eq_getElem index
      rw [(run_extends run).1 _ _ found, found]
    · have outside : saved.contexts.length ≤ id - 1 := by omega
      simp [bound, List.getElem?_eq_none outside]

theorem rename_new_source_rejected (saved current : Store) (id : Nat)
    (new : saved.contexts.length < id) : renameSource saved current id = none := by
  simp [renameSource, Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.zero_le _) new), Nat.not_le.mpr new]

theorem execute_value_extension {t u : Tables} (ext : TableExtension t u)
    {a : Availability} {levels q : Nat → Nat} {fuel : Nat} {request : ValueRequest Nat}
    (result : executeInput t a levels q fuel (.value request) = some (.value request)) :
    executeInput u a levels q fuel (.value request) = some (.value request) := by
  simp only [executeInput] at result ⊢
  split at result
  · rename_i enter
    simp only [enter, ↓reduceIte]
    obtain ⟨output, found, same⟩ := Option.map_eq_some_iff.mp result
    simp [value_context_extension ext found, same]
  · cases result

namespace Reindex
open NativeContextReadback

def packet {t u : Tables} (ext : TableExtension t u) (p : PrefixPacket t) : PrefixPacket u :=
  ⟨p.key, p.segment, prefix_recipe_extension ext p.construction⟩

def body {t u : Tables} (ext : TableExtension t u) (p : BodyPacket t) : BodyPacket u :=
  ⟨p.key, p.body, body_recipe_extension ext p.construction⟩

def route {t u : Tables} (ext : TableExtension t u) (r : Route t) : Route u :=
  ⟨r.work, r.processing, r.source, r.effectMap, r.valueMap, r.previous.map (packet ext)⟩

@[simp] theorem route_post {t u : Tables} (ext : TableExtension t u) (r : Route t) :
    (route ext r).post = r.post := by
  cases found : r.previous <;> simp [route, Route.post, found, packet]

@[simp] theorem route_target {t u : Tables} (ext : TableExtension t u) (r : Route t) :
    (route ext r).target = r.target := by
  change r.source.transported r.effectMap r.valueMap (route ext r).post = r.target
  rw [route_post]
  rfl

@[simp] theorem route_derived {t u : Tables} (ext : TableExtension t u) (r : Route t) :
    (route ext r).derived = r.derived := rfl

def ready {t u : Tables} (ext : TableExtension t u) (r : Ready t) : Ready u :=
  ⟨route ext r.route, packet ext r.packet, by simpa [packet] using r.exactKey⟩

def value {t u : Tables} (ext : TableExtension t u) (r : ValueReady t) : ValueReady u :=
  ⟨route ext r.route, r.request, by simpa using r.exactKey,
    r.availability, r.levels, r.q, r.fuel, execute_value_extension ext r.result⟩

def owner {t u : Tables} (ext : TableExtension t u) (o : Owner t) : Owner u := ⟨ready ext o.ready⟩

def memo {t u : Tables} (ext : TableExtension t u) (m : Memo t) : Memo u :=
  ⟨m.generation, owner ext m.owner⟩

def receipt {t u : Tables} (ext : TableExtension t u) : Receipt t → Receipt u
  | .effect r o => .effect (ready ext r) (owner ext o)
  | .value r => .value (value ext r)

def state {t u : Tables} (ext : TableExtension t u) (s : State t) : State u :=
  { control := s.control
    effectMap := s.effectMap
    valueMap := s.valueMap
    generation := s.generation
    relations := s.relations
    tasks := s.tasks
    routes := fun w => (s.routes w).map (route ext)
    checked := fun w => (s.checked w).map (ready ext)
    published := fun w => (s.published w).map (ready ext)
    ready := fun w => (s.ready w).map (ready ext)
    valueReady := fun w => (s.valueReady w).map (value ext)
    publications := fun key => (s.publications key).map (packet ext)
    postContexts := s.postContexts
    owners := fun w => (s.owners w).map (owner ext)
    memo := fun key => (s.memo key).map (memo ext)
    typed := s.typed
    seals := s.seals.map fun pair => (owner ext pair.1, body ext pair.2)
    receipts := s.receipts.map (receipt ext)
    edges := s.edges
    settling := s.settling }

@[simp] theorem state_initial {t u : Tables} (ext : TableExtension t u) :
    state ext (initial t) = initial u := rfl

theorem map_put {I A B : Type} [DecidableEq I]
    (f : A → B) (table : I → Option A) (id : I) (a : A) :
    (fun key => (put table id a key).map f) = put (fun key => (table key).map f) id (f a) := by
  funext key
  by_cases same : key = id <;> simp [put, same]

@[simp] theorem make_route {t u : Tables} (ext : TableExtension t u) (s : State t)
    (w : NativeDrainOwnership.Work) (processing : Nat) (source : Relation) :
    makeRoute (state ext s) w processing source = route ext (makeRoute s w processing source) := by
  cases source <;> rfl

@[simp] theorem pair_current {t u : Tables} (ext : TableExtension t u) (s : State t)
    (r : Ready t) (raw : Task) : pairCurrent (state ext s) (ready ext r) raw = pairCurrent s r raw := by
  simp only [pairCurrent, state, ready, route, packet]
  cases s.memo (r.route.processing, r.packet.key) <;> rfl

@[simp] theorem packet_move {t u : Tables} (ext : TableExtension t u) (p : PrefixPacket t)
    (q : Nat → Nat) (post : Key → Nat) :
    (packet ext p).move q post = packet ext (p.move q post) := rfl

@[simp] theorem state_admit {t u : Tables} (ext : TableExtension t u) (s : State t)
    (r : Ready t) (raw : Task) :
    admitOwner (state ext s) (ready ext r) raw = state ext (admitOwner s r raw) := by
  simp only [admitOwner]
  change { state ext s with
    owners := put (state ext s).owners r.route.work (owner ext ⟨r⟩)
    memo := if raw = (route ext r.route).target.task then
      put (state ext s).memo (r.route.processing, r.packet.key) ⟨s.generation, owner ext ⟨r⟩⟩
      else (state ext s).memo
    typed := NativeMergeExpansion.attach raw s.typed } = _
  rw [route_target]
  split <;> simp [state, map_put, ready, owner, memo, route, packet, Owner.work, Owner.key, Owner.relation]

@[simp] theorem state_finish {t u : Tables} (ext : TableExtension t u) (s : State t)
    (f : NativeDrainOwnership.Frame) (fs : List NativeDrainOwnership.Frame)
    (o : Owner t) (b : BodyPacket t) (transitions : Nat) :
    finishOwner (state ext s) f fs (owner ext o) (body ext b) transitions =
      state ext (finishOwner s f fs o b transitions) := by
  simp [finishOwner, state, owner, ready, route, receipt, Owner.work]

@[simp] theorem state_reuse {t u : Tables} (ext : TableExtension t u) (s : State t)
    (f : NativeDrainOwnership.Frame) (fs : List NativeDrainOwnership.Frame)
    (r : Ready t) (o : Owner t) (transitions : Nat) :
    finishReuse (state ext s) f fs (ready ext r) (owner ext o) transitions =
      state ext (finishReuse s f fs r o transitions) := by
  simp [finishReuse, state, owner, ready, route, receipt]

@[simp] theorem state_value {t u : Tables} (ext : TableExtension t u) (s : State t)
    (f : NativeDrainOwnership.Frame) (fs : List NativeDrainOwnership.Frame)
    (r : ValueReady t) (transitions : Nat) :
    finishValue (state ext s) f fs (value ext r) transitions =
      state ext (finishValue s f fs r transitions) := by
  simp [finishValue, state, value, route, receipt]

theorem state_publish {t u : Tables} (ext : TableExtension t u) (s : State t) (r : Ready t) :
    { state ext s with
      publications := put (state ext s).publications ((ready ext r).route.processing, (ready ext r).packet.key)
        (ready ext r).packet
      published := put (state ext s).published (ready ext r).route.work (ready ext r)
      postContexts := fun key => if key = (ready ext r).packet.key then
        (ready ext r).packet.segment.postContext else (state ext s).postContexts key } =
    state ext { s with
      publications := put s.publications (r.route.processing, r.packet.key) r.packet
      published := put s.published r.route.work r
      postContexts := fun key => if key = r.packet.key then r.packet.segment.postContext else s.postContexts key } := by
  simp only [state, map_put]
  rfl

theorem state_cached {t u : Tables} (ext : TableExtension t u) (s : State t) (r : Route t)
    (p : PrefixPacket t) (keyIs : r.target = .effect p.key) :
    { state ext s with
      ready := put (state ext s).ready (route ext r).work
        ⟨route ext r, (packet ext p).move (state ext s).effectMap (postAt (state ext s)),
          by simpa [packet, PrefixPacket.move] using keyIs⟩ } =
    state ext { s with ready := put s.ready r.work ⟨r, p.move s.effectMap (postAt s), keyIs⟩ } := by
  simp only [state, map_put]
  rfl

theorem step {t u : Tables} (ext : TableExtension t u) {s next : State t}
    (event : NativeContextReadback.Step t s next) :
    NativeContextReadback.Step u (state ext s) (state ext next) := by
  cases event with
  | control next event administrative settlement =>
      simpa only [state, controlOnly] using
        NativeContextReadback.Step.control (state ext s) next event administrative settlement
  | intern id relation fresh unique valid =>
      simpa only [state] using NativeContextReadback.Step.intern (state ext s) id relation fresh unique valid
  | task id task fresh =>
      simpa only [state] using NativeContextReadback.Step.task (state ext s) id task fresh
  | transport f fs w processing source raw top phase current before relation task pair interned valid unchanged =>
      have event := NativeContextReadback.Step.transport (state ext s) f fs w processing source raw
        top phase current before relation task pair
        (by change s.relations processing = some (makeRoute (state ext s) w processing source).target
            simpa only [make_route, route_target] using interned)
        (by simpa only [make_route, route_target] using valid) unchanged
      simp only [make_route, route_derived] at event
      simpa only [state, map_put] using event
  | contextEmpty f fs r key a levels fuel p top current processing routed keyIs result empty =>
      have event := NativeContextReadback.Step.contextEmpty (state ext s) f fs (route ext r) key a levels fuel p
        top current processing (by simp [state, route, routed]) (by simpa using keyIs)
        (prepare_extension ext result) empty
      simpa [state, map_put, ready, packet, route] using event
  | contextCheck f fs r key a levels fuel p top current processing routed keyIs undischarged result nonempty =>
      have event := NativeContextReadback.Step.contextCheck (state ext s) f fs (route ext r) key a levels fuel p
        top current processing (by simp [state, route, routed]) (by simpa using keyIs)
        (by simp [state, route, undischarged]) (prepare_extension ext result) nonempty
      simpa [state, map_put, ready, packet, route] using event
  | publish r checked reserved success =>
      have event := NativeContextReadback.Step.publish (state ext s) (ready ext r)
        (by simp only [state, ready, route, checked, Option.map_some]) reserved success
      rw [state_publish] at event
      exact event
  | sample r published sampled success =>
      have event := NativeContextReadback.Step.sample (state ext s) (ready ext r)
        (by simp only [state, ready, route, published, Option.map_some]) sampled success
      simpa only [state, map_put, ready, route] using event
  | contextCached f fs r p fuel top current processing routed keyIs discharged parsed nonempty guard canonical =>
      have event := NativeContextReadback.Step.contextCached (state ext s) f fs (route ext r) (packet ext p) fuel
        top current processing (by simp [state, route, routed]) (by simpa [packet, PrefixPacket.move] using keyIs)
        (by simp only [state, route, packet, discharged, Option.map_some])
        (parse_extension ext parsed) nonempty guard canonical
      rw [state_cached] at event
      exact event
  | contextValue f fs r top current processing routed =>
      have event := NativeContextReadback.Step.contextValue (state ext s) f fs (value ext r)
        top current processing (by simp only [state, value, route, routed, Option.map_some])
      simpa only [state, map_put, value, route] using event
  | admit f fs r raw top phase current processing context task fresh notCurrent =>
      have event := NativeContextReadback.Step.admit (state ext s) f fs (ready ext r) raw
        top phase current processing (by simp only [state, ready, route, context, Option.map_some])
        task (by simp only [state, ready, route, fresh, Option.map_none])
        (by simpa only [pair_current] using notCurrent)
      simpa only [state_admit] using event
  | finish f fs o a levels b transitions top phase current processing owned result =>
      have event := NativeContextReadback.Step.finish (state ext s) f fs (owner ext o) a levels b transitions
        top phase current processing
        (by change (s.owners o.work).map (owner ext) = some (owner ext o)
            rw [owned]
            rfl)
        (finish_prefix_extension ext result)
      change NativeContextReadback.Step u (state ext s)
        (finishOwner (state ext s) f fs (owner ext o)
          (body ext ⟨o.key, b, .finished o.ready.packet.construction a levels s.effectMap b result⟩) transitions) at event
      simpa only [state_finish] using event
  | duplicate f fs r m raw transitions top phase current processing context task typed found generation notOwner =>
      have event := NativeContextReadback.Step.duplicate (state ext s) f fs (ready ext r) (memo ext m) raw transitions
        top phase current processing (by simp only [state, ready, route, context, Option.map_some])
        task typed (by simp only [state, ready, route, packet, found, Option.map_some])
        generation (by simp only [state, ready, route, notOwner, Option.map_none])
      simpa only [memo, state_reuse] using event
  | valueExit f fs r transitions top phase current processing context notOwner =>
      have event := NativeContextReadback.Step.valueExit (state ext s) f fs (value ext r) transitions
        top phase current processing (by simp only [state, value, route, context, Option.map_some])
        (by simp only [state, value, route, notOwner, Option.map_none])
      simpa only [state_value] using event
  | beginSettlement f fs top phase current queue notSettling =>
      simpa only [state] using NativeContextReadback.Step.beginSettlement (state ext s) f fs
        top phase current queue notSettling
  | merge effect value settling absorbsEffect absorbsValue =>
      simpa only [state] using NativeContextReadback.Step.merge (state ext s) effect value
        settling absorbsEffect absorbsValue
  | endSettlement settling =>
      simpa only [state] using NativeContextReadback.Step.endSettlement (state ext s) settling

theorem run {t u : Tables} (ext : TableExtension t u) {s next : State t}
    (history : NativeContextReadback.Run t s next) :
    NativeContextReadback.Run u (state ext s) (state ext next) := by
  induction history with
  | nil => exact .nil _
  | snoc _ event ih => exact .snoc ih (step ext event)

theorem reachable {t u : Tables} (ext : TableExtension t u) {s : State t}
    (history : NativeContextReadback.Run t (initial t) s) :
    NativeContextReadback.Run u (initial u) (state ext s) := by
  simpa only [state_initial] using run ext history

end Reindex

/-- One shared payload: table construction and the original Context/drain
driver cannot select unrelated histories. Reads retain their actual version. -/
structure Joint where
  store : Store
  context : NativeContextReadback.State store.tables
  observations : List Observation := []

def jointInitial : Joint := ⟨{}, NativeContextReadback.initial ({} : Store).tables, []⟩

inductive JointStep : Joint → Joint → Prop
  | table (before : Joint) (after : Store) (event : Step before.store after) :
      JointStep before
        ⟨after, Reindex.state (run_table_extension (.snoc (.nil _) event)) before.context, before.observations⟩
  | context (before : Joint) (after : NativeContextReadback.State before.store.tables)
      (event : NativeContextReadback.Step before.store.tables before.context after) :
      JointStep before ⟨before.store, after, before.observations⟩
  | observe (before : Joint) (query : Query) :
      JointStep before ⟨before.store, before.context, before.observations ++ [observe before.store query]⟩

inductive JointRun : Joint → Joint → Prop
  | nil (state : Joint) : JointRun state state
  | snoc {saved current after : Joint} : JointRun saved current → JointStep current after → JointRun saved after

theorem joint_run_tables {saved current : Joint} (history : JointRun saved current) :
    Run saved.store current.store := by
  induction history with
  | nil => exact .nil _
  | snoc prior event ih =>
      cases event with
      | table after event => exact .snoc ih event
      | context | observe => exact ih

theorem joint_run_context {saved current : Joint} (history : JointRun saved current)
    (earlier : NativeContextReadback.Run saved.store.tables
      (NativeContextReadback.initial saved.store.tables) saved.context) :
    NativeContextReadback.Run current.store.tables
      (NativeContextReadback.initial current.store.tables) current.context := by
  induction history with
  | nil => exact earlier
  | snoc prior event ih =>
      cases event with
      | table after event => exact Reindex.reachable (run_table_extension (.snoc (.nil _) event)) ih
      | context after event => exact .snoc ih event
      | observe => exact ih

def castContext {t u : Tables} (same : t = u) (context : NativeContextReadback.State t) :
    NativeContextReadback.State u := same ▸ context

theorem cast_context_run {t u : Tables} (same : t = u) {context : NativeContextReadback.State t}
    (history : NativeContextReadback.Run t (NativeContextReadback.initial t) context) :
    NativeContextReadback.Run u (NativeContextReadback.initial u) (castContext same context) := by
  cases same
  exact history

def jointCancel (saved current : Joint) (history : JointRun saved current) : Joint :=
  ⟨cancel saved.store current.store,
    castContext (cancellation_all_five_tables (joint_run_tables history)).symm saved.context,
    saved.observations⟩

inductive JointHistory : Joint → Prop
  | initial : JointHistory jointInitial
  | commit {saved current : Joint} : JointHistory saved → JointRun saved current →
      current.store.pending = none → JointHistory current
  | cancel {saved current : Joint} (earlier : JointHistory saved)
      (attempt : JointRun saved current) : JointHistory (jointCancel saved current attempt)

theorem joint_history_facts {state : Joint} (history : JointHistory state) :
    Fresh state.store ∧ state.store.pending = none ∧
    NativeContextReadback.Run state.store.tables
      (NativeContextReadback.initial state.store.tables) state.context := by
  induction history with
  | initial => exact ⟨fresh_initial, rfl, .nil _⟩
  | commit prior attempt idle ih =>
      exact ⟨run_fresh (joint_run_tables attempt) ih.1, idle, joint_run_context attempt ih.2.2⟩
  | cancel prior attempt ih =>
      exact ⟨cancel_fresh (joint_run_tables attempt) ih.1, rfl,
        cast_context_run (cancellation_all_five_tables (joint_run_tables attempt)).symm ih.2.2⟩

/-- The previously fixed-table drain theorem now receives a table and Context
driver produced by the same append/intern/rollback/retry history. -/
theorem committed_tables_context_readback {state : Joint} (history : JointHistory state)
    (queue : state.context.control.queue = []) (stack : state.context.control.frames = []) :
    ∀ work ∈ state.context.control.issued, ∃ receipt ∈ state.context.receipts,
      receipt.work = work ∧ NativeContextReadback.Resolved state.context receipt ∧
      NativeContextReadback.RouteValid state.context receipt.route :=
  NativeContextReadback.quiescent_original_context_readback (joint_history_facts history).2.2 queue stack

theorem committed_tables_original_body {state : Joint} (history : JointHistory state)
    (cut : NativeContextReadback.NoCurrent state.context)
    {ready : NativeContextReadback.Ready state.store.tables}
    {owner : NativeContextReadback.Owner state.store.tables}
    (receipt : NativeContextReadback.Receipt.effect ready owner ∈ state.context.receipts) :
    (∃ body, (owner, body) ∈ state.context.seals ∧ ready.route.target = .effect body.key ∧
      NativeContextReadback.BodyRecipe state.store.tables body.key body.body) ∧
    (∀ packet, ready.route.previous = some packet → ready.route.source = .effect packet.key ∧
      NativeContextReadback.FreshChecks packet ∧ packet.segment.parsed.filters ≠ []) ∧
    (∀ edge ∈ ready.route.derived, edge ∈ state.context.edges) ∧
    (ready.packet.key.sources = ready.route.source.sources ∧
      ready.packet.key.transformer = ready.route.source.transformer ∧
      ready.route.source.demand = none) :=
  NativeContextReadback.effect_receipt_original_body (joint_history_facts history).2.2 cut receipt

theorem committed_tables_whole_child {state : Joint} (history : JointHistory state)
    (cut : NativeContextReadback.NoCurrent state.context)
    {ready : NativeContextReadback.Ready state.store.tables}
    {owner : NativeContextReadback.Owner state.store.tables}
    (receipt : NativeContextReadback.Receipt.effect ready owner ∈ state.context.receipts) :
    ∃ body, (owner, body) ∈ state.context.seals ∧
      ∀ child ∈ body.body.children,
        NativeContextReadback.ChildPayload state.store.tables body.key child := by
  obtain ⟨⟨body, stored, _, recipe⟩, _⟩ := committed_tables_original_body history cut receipt
  exact ⟨body, stored, NativeContextReadback.recipe_body_children recipe⟩

theorem joint_cancel_lookup {saved current : Joint} (attempt : JointRun saved current) (query : Query) :
    lookup (jointCancel saved current attempt).store query = lookup saved.store query :=
  cancellation_lookup (joint_run_tables attempt) query

theorem joint_cancel_versions {saved current : Joint} (attempt : JointRun saved current) :
    (jointCancel saved current attempt).store.clock = current.store.clock ∧
    (jointCancel saved current attempt).store.version = current.store.version + 1 ∧
    (jointCancel saved current attempt).observations = saved.observations := ⟨rfl, rfl, rfl⟩

theorem actual_observation (before : Joint) (query : Query) :
    JointStep before ⟨before.store, before.context, before.observations ++ [observe before.store query]⟩ ∧
    (observe before.store query).version = before.store.version ∧
    (observe before.store query).answer = lookup before.store query := ⟨.observe before query, rfl, rfl⟩

theorem joint_history_tables {state : Joint} (history : JointHistory state) : History state.store := by
  induction history with
  | initial => exact .initial
  | commit prior attempt idle ih => exact .commit ih (joint_run_tables attempt) idle
  | cancel prior attempt ih => exact .cancel ih (joint_run_tables attempt)

def ObservationWitness (observation : Observation) : Prop :=
  ∃ saved cut, History saved ∧ Run saved cut ∧ observation.version = cut.version ∧
    observation.answer = lookup cut observation.query

theorem joint_run_observations {saved current : Joint} (history : JointRun saved current)
    (base : History saved.store)
    (earlier : ∀ observation ∈ saved.observations, ObservationWitness observation) :
    ∀ observation ∈ current.observations, ObservationWitness observation := by
  induction history with
  | nil => exact earlier
  | snoc prior event ih =>
      cases event with
      | table | context => exact ih
      | observe query =>
          intro observation member
          rcases List.mem_append.mp member with old | new
          · exact ih observation old
          · have same := List.mem_singleton.mp new
            subst observation
            exact ⟨saved.store, _, base, joint_run_tables prior, rfl, rfl⟩

theorem committed_observation_readback {state : Joint} (history : JointHistory state) :
    ∀ observation ∈ state.observations, ObservationWitness observation := by
  induction history with
  | initial => simp [jointInitial]
  | commit prior attempt idle ih => exact joint_run_observations attempt (joint_history_tables prior) ih
  | cancel prior attempt ih => exact ih

def AllocatedBirth (s : Store) (birth : Nat) : Prop :=
  (∃ cell ∈ s.contexts, cell.birth = birth) ∨
  (∃ cell ∈ s.weights, cell.birth = birth) ∨
  (∃ cell ∈ s.views, cell.birth = birth) ∨
  (∃ cell ∈ s.contributions, cell.birth = birth)

theorem allocated_birth_lt {s : Store} (fresh : Fresh s) {birth : Nat}
    (allocated : AllocatedBirth s birth) : birth < s.clock := by
  rcases allocated with ⟨cell, member, rfl⟩ | ⟨cell, member, rfl⟩ |
      ⟨cell, member, rfl⟩ | ⟨cell, member, rfl⟩
  · exact fresh.contexts cell member
  · exact fresh.weights cell member
  · exact fresh.views cell member
  · exact fresh.contributions cell member

theorem retry_all_lanes_birth {saved current : Store} (history : History saved) (attempt : Run saved current)
    {birth : Nat} (allocated : AllocatedBirth current birth) (input : ViewInput) (effect origin : Nat) :
    birth < (cancel saved current).clock ∧
    ((cancel saved current).constructView input).views[(cancel saved current).views.length]? =
      some ⟨current.clock, viewRecord (weightedDraft (cancel saved current) input)⟩ ∧
    ((cancel saved current).contribution effect origin).1.contributions[(cancel saved current).contributions.length]? =
      some ⟨current.clock, ⟨effect, origin, (cancel saved current).contributions.length⟩⟩ ∧
    (input.needsWeight = true →
      ((cancel saved current).constructView input).weights[(cancel saved current).weights.length]? =
        some ⟨current.clock + 1, weightRecord (reservedDraft (cancel saved current) input)⟩) := by
  have later := allocated_birth_lt (run_fresh attempt (history_fresh history)) allocated
  refine ⟨later, (construct_view_readback _ _).1, ?_, fun needed => construct_weight_readback _ _ needed⟩
  simp [Store.contribution, cancel, truncate]

theorem cancel_is_retained_snapshot_with_fresh_clock {saved current : Store}
    (attempt : Run saved current) (idle : saved.pending = none) :
    cancel saved current = { saved with clock := current.clock, version := current.version + 1 } := by
  obtain ⟨contexts, weights, views, contributions⟩ := cancellation_vectors attempt
  cases saved
  cases current
  simp_all [cancel, truncate, Store.frontier]

namespace Examples

def closedInput : ViewInput := ⟨3, 4, [7, 8], none, none, some ⟨.positive, 9⟩⟩
def firstView : Store := ({} : Store).constructView closedInput
def firstContext : Store := (firstView.intern (.prefix 0 0)).1
def first : Store := (firstContext.contribution 7 44).1

theorem first_run : Run ({} : Store) first := by
  have view := construct_view_run ({} : Store) closedInput rfl (by decide) (by decide)
  have context : Step firstView firstContext :=
    .context firstView (.prefix 0 0) rfl (by simp [NativeValuePorts.contextInputs]) (by decide) true rfl
  have contribution : Step firstContext first :=
    .contribution firstContext 7 44 rfl (by decide) true rfl
  exact .snoc (.snoc view context) contribution

theorem first_history : History first := .commit .initial first_run rfl

def cancelled : Store := cancel ({} : Store) first
def retryInput : ViewInput := ⟨5, 6, [99], none, none, none⟩
def retryView : Store := cancelled.constructView retryInput
def retry : Store := (retryView.intern (.swap 0)).1

theorem retry_run : Run cancelled retry := by
  have view := construct_view_run cancelled retryInput rfl (by decide) (by decide)
  exact .snoc view (.context retryView (.swap 0) rfl
    (by simp [NativeValuePorts.contextInputs, retryView, Store.constructView,
      Store.finishView, Store.publishView, Store.reserveView, Store.appendWeight]) (by decide) true rfl)

theorem retry_history : History retry :=
  .commit (.cancel .initial first_run) retry_run rfl

theorem all_five_lanes_first :
    first.tables.contexts 1 = some (.prefix 0 0) ∧
    first.tables.weights 0 = some ⟨[7, 8], 0, 3, 4, [], []⟩ ∧
    first.tables.views 0 = some ⟨[7, 8], none, some 0, 3, 4⟩ ∧
    first.tables.contributions 0 = some 7 ∧ first.tables.prefixIdentity 0 = 1 := by decide

theorem meaningful_missing_changes :
    lookup ({} : Store) (.prefixIdentity 0) = .missing ∧
    lookup first (.prefixIdentity 0) = .prefixIdentity ⟨.context, 1, 2⟩ ∧
    lookup cancelled (.prefixIdentity 0) = .missing := by decide

theorem actual_retry_changes_allocation :
    first.contextAt 1 = some ⟨2, .prefix 0 0⟩ ∧
    retry.contextAt 1 = some ⟨6, .swap 0⟩ ∧
    first.tables.prefixIdentity 0 = 1 ∧ retry.tables.prefixIdentity 0 = 0 ∧
    first.version < retry.version := by decide

theorem actual_retry_parser :
    parse first.tables 3 1 = some ⟨[0], 0, false, false, false⟩ ∧
    parse retry.tables 3 1 = some ⟨[], 1, false, true, false⟩ := by decide

def callbacks : Availability :=
  ⟨true, true, fun _ => true, fun _ => true, fun _ => true,
    fun _ => true, fun _ => true, fun _ => true, true⟩

def key : Key := ⟨.bottom, .allowance 0, 1, some 11, 4⟩
def segment : NativeContextReadback.Prefix :=
  ⟨⟨[0], 0, false, false, false⟩, [⟨0, 0, false, .localReturn⟩], 0, true⟩
def completed : Body :=
  ⟨⟨[0], 0, false, false, false⟩, [⟨0, 0, false, .localReturn⟩], 0, true, none⟩

theorem actual_completed_prefix :
    NativeContextReadback.prepare first.tables callbacks (fun _ => 0) id 3 key = some segment := by decide

theorem actual_completed_body : NativeContextReadback.BodyRecipe first.tables key completed :=
  .finished (.checked callbacks (fun _ => 0) id 3 segment actual_completed_prefix)
    callbacks (fun _ => 0) id completed (by decide)

theorem completed_body_survives_fresh_allocation (effect origin : Nat) :
    NativeContextReadback.BodyRecipe (first.contribution effect origin).1.tables key completed := by
  apply body_recipe_extension (run_table_extension (.snoc (.nil first)
    (.contribution first effect origin rfl (by decide) true rfl))) actual_completed_body

end Examples

/-- The native `context_keys` map, as a lookup function. This section derives
its coherence under the actual insert/remove operations; it is not assumed as
a table-equality callback. -/
def keyLookup (nodes : List Expr) (query : Expr) : Option Nat :=
  if query ∈ nodes then some (nodes.idxOf query + 1) else none

def keyInsert (keys : Expr → Option Nat) (node : Expr) (id : Nat) : Expr → Option Nat :=
  fun query => if query = node then some id else keys query

def keyErase (keys : Expr → Option Nat) (node : Expr) : Expr → Option Nat :=
  fun query => if query = node then none else keys query

def keyRemove (keys : Expr → Option Nat) (nodes : List Expr) : Expr → Option Nat :=
  nodes.foldl keyErase keys

def Store.keys (s : Store) : Expr → Option Nat := keyLookup (values s.contexts)

theorem native_key_insert (nodes : List Expr) (node : Expr) (fresh : node ∉ nodes) :
    keyLookup (nodes ++ [node]) = keyInsert (keyLookup nodes) node (nodes.length + 1) := by
  funext query
  by_cases same : query = node
  · subst query
    simp [keyLookup, keyInsert, fresh, List.idxOf_append]
  · by_cases old : query ∈ nodes <;>
      simp [keyLookup, keyInsert, same, old, List.idxOf_append]

theorem native_interner_cache (s : Store) (node : Expr) :
    (s.intern node).1.keys =
      match s.keys node with
      | some _ => s.keys
      | none => keyInsert s.keys node (s.contexts.length + 1) := by
  by_cases found : node ∈ values s.contexts
  · simp [Store.intern, Store.keys, internCell, keyLookup, found]
  · have insertion := native_key_insert (values s.contexts) node found
    have mapped : node ∉ s.contexts.map Cell.value := found
    simpa [Store.intern, Store.keys, internCell, keyLookup, found, values, mapped] using insertion

theorem native_interner_reuse (s : Store) (node : Expr) (id : Nat) (found : s.keys node = some id) :
    (s.intern node).2 = id ∧ (s.intern node).1.contexts = s.contexts := by
  unfold Store.keys keyLookup at found
  split at found
  · rename_i present
    cases found
    simp [Store.intern, internCell, present]
  · cases found

theorem native_prefix_is_cache_lookup (s : Store) (weight : Nat) :
    s.prefixAt weight = (s.keys (.prefix weight 0)).getD 0 := by
  simp only [Store.prefixAt, Store.keys, keyLookup]
  split <;> rfl

theorem key_remove_queries (keys : Expr → Option Nat) (nodes : List Expr) (query : Expr) :
    keyRemove keys nodes query = if query ∈ nodes then none else keys query := by
  induction nodes generalizing keys with
  | nil => rfl
  | cons node rest ih =>
      simp only [keyRemove, List.foldl_cons]
      rw [show rest.foldl keyErase (keyErase keys node) query =
        if query ∈ rest then none else keyErase keys node query from ih _]
      by_cases head : query = node <;> by_cases tail : query ∈ rest <;>
        simp [List.mem_cons, head, tail, keyErase]

theorem intern_context_unique (s : Store) (node : Expr) (unique : (values s.contexts).Nodup) :
    (values (s.intern node).1.contexts).Nodup := by
  by_cases present : node ∈ values s.contexts
  · simpa [Store.intern, internCell, present] using unique
  · change (values (internCell s.contexts s.clock node).1).Nodup
    have mapped : node ∉ s.contexts.map Cell.value := present
    simp only [internCell, values, mapped, ↓reduceIte, List.map_append, List.map_cons, List.map_nil]
    apply List.nodup_append.mpr
    refine ⟨unique, by simp, ?_⟩
    intro old member other equal
    have same : other = node := by simpa using equal
    subst other
    intro oldIs
    exact present (oldIs ▸ member)

theorem step_context_unique {s u : Store} (event : Step s u) (unique : (values s.contexts).Nodup) :
    (values u.contexts).Nodup := by
  cases event with
  | context node => exact intern_context_unique s node unique
  | reserveView | reserveCopy | sourceWeight | publishView | sampleView | contribution => exact unique

theorem run_context_unique {s u : Store} (history : Run s u) (unique : (values s.contexts).Nodup) :
    (values u.contexts).Nodup := by
  induction history with
  | nil => exact unique
  | snoc prior event ih => exact step_context_unique event ih

theorem history_context_unique {s : Store} (history : History s) : (values s.contexts).Nodup := by
  induction history with
  | initial => simp [values]
  | commit prior run idle ih => exact run_context_unique run ih
  | cancel prior run ih => simpa only [(cancellation_vectors run).1] using ih

theorem remove_fresh_suffix (old tail : List Expr) (unique : (old ++ tail).Nodup) :
    keyRemove (keyLookup (old ++ tail)) tail = keyLookup old := by
  have separate := (List.nodup_append.mp unique).2.2
  funext query
  rw [key_remove_queries]
  by_cases retained : query ∈ old
  · have fresh : query ∉ tail := by
      intro removed
      exact separate query retained query removed rfl
    simp [fresh, keyLookup, retained, List.idxOf_append]
  · by_cases removed : query ∈ tail <;> simp [keyLookup, retained, removed]

theorem native_cache_rollback {saved current : Store} (history : History saved)
    (attempt : Run saved current) :
    keyRemove current.keys (values (current.contexts.drop saved.contexts.length)) = saved.keys := by
  obtain ⟨tail, extension⟩ := (run_prefixes attempt).1
  have unique := run_context_unique attempt (history_context_unique history)
  have mapped : values current.contexts = values saved.contexts ++ values tail := by
    simp [← extension, values]
  rw [mapped] at unique
  have removed := remove_fresh_suffix (values saved.contexts) (values tail) unique
  simpa only [Store.keys, ← extension, List.drop_left, values, List.map_append] using removed

theorem native_prefix_rollback {saved current : Store} (history : History saved)
    (attempt : Run saved current) (weight : Nat) :
    (keyRemove current.keys (values (current.contexts.drop saved.contexts.length))
      (.prefix weight 0)).getD 0 = (cancel saved current).prefixAt weight := by
  rw [native_cache_rollback history attempt, cancellation_recovers_interner attempt,
    native_prefix_is_cache_lookup]

/-- Each installed check may see a later native allocation cut. The list is
still the complete original parser order, with no deletion or deduplication. -/
inductive VersionedChecks (a : Availability) (levels q : Nat → Nat) (parent : Key) :
    Store → Store → List Nat → List Check → Prop
  | nil {before after : Store} (allocation : Run before after) :
      VersionedChecks a levels q parent before after [] []
  | cons {before atCheck after : Store} {weight : Nat} {weights : List Nat}
      {check : Check} {checks : List Check}
      (allocation : Run before atCheck)
      (result : checkFilter atCheck.tables a levels q parent weight = some check)
      (rest : VersionedChecks a levels q parent atCheck after weights checks) :
      VersionedChecks a levels q parent before after (weight :: weights) (check :: checks)

theorem versioned_checks_run {a : Availability} {levels q : Nat → Nat} {parent : Key}
    {before after : Store} {weights : List Nat} {checks : List Check}
    (history : VersionedChecks a levels q parent before after weights checks) : Run before after := by
  induction history with
  | nil allocation => exact allocation
  | cons allocation result rest ih => exact run_trans allocation ih

theorem versioned_checks_readback {a : Availability} {levels q : Nat → Nat} {parent : Key}
    {before after : Store} {weights : List Nat} {checks : List Check}
    (history : VersionedChecks a levels q parent before after weights checks) :
    collect (checkFilter after.tables a levels q parent) weights = some checks := by
  induction history with
  | nil => rfl
  | cons allocation result rest ih =>
      have head := check_filter_extension (run_table_extension (versioned_checks_run rest)) result
      simp [collect, head, ih]

def stagedPrefix (q : Nat → Nat) (parent : Key) (parsed : Parsed) (checks : List Check) :
    NativeContextReadback.Prefix :=
  ⟨parsed, checks, if parsed.filters = [] then parent.context else parsed.residual,
    consumed (NativeReplayCurrent.currentPair q parent).2 checks⟩

theorem versioned_prepare_readback {a : Availability} {levels q : Nat → Nat} {parent : Key}
    {before after : Store} {fuel : Nat} {parsed : Parsed} {checks : List Check}
    (entered : a.enter = true)
    (canonical : parent.lower = (NativeReplayCurrent.currentPair q parent).1 ∧
      parent.upper = (NativeReplayCurrent.currentPair q parent).2)
    (guard : relationGuard ⟨(NativeReplayCurrent.currentPair q parent).1,
      (NativeReplayCurrent.currentPair q parent).2, parent.context, parent.sources, parent.transformer⟩ = true)
    (parser : (if parent.context = 0 then some (⟨[], 0, false, false, false⟩ : Parsed)
      else if a.parser then parse before.tables fuel parent.context else none) = some parsed)
    (history : VersionedChecks a levels q parent before after parsed.filters checks) :
    NativeContextReadback.prepare after.tables a levels q fuel parent =
      some (stagedPrefix q parent parsed checks) := by
  have parseAgain : (if parent.context = 0 then some (⟨[], 0, false, false, false⟩ : Parsed)
      else if a.parser then parse after.tables fuel parent.context else none) = some parsed := by
    split at parser
    · rename_i identity
      simpa [identity] using parser
    · rename_i nonidentity
      simp only [nonidentity, ↓reduceIte]
      split at parser
      · rename_i enabled
        simp only [enabled, ↓reduceIte]
        exact parse_extension (run_table_extension (versioned_checks_run history)) parser
      · cases parser
  simp [NativeContextReadback.prepare, entered, canonical, parseAgain,
    NativeContextReadback.prepareParsed, guard, versioned_checks_readback history, stagedPrefix]

theorem versioned_finish_readback {a : Availability} {levels q : Nat → Nat} {parent : Key}
    {before after : Store} {segment : NativeContextReadback.Prefix} {body : Body}
    (origin : NativeContextReadback.PrefixRecipe before.tables parent segment)
    (allocation : Run before after)
    (finished : NativeContextReadback.finishPrefix after.tables a levels q parent segment = some body) :
    NativeContextReadback.BodyRecipe after.tables parent body :=
  .finished (prefix_recipe_extension (run_table_extension allocation) origin) a levels q body finished

/-- Closed-weight copy validation retains every native comparison and returns
the exact attachment source, while a changed tail selects a fresh View. -/
theorem copy_input_fields {s : Store} {source : Nat} {tail : Option Nat} {input : ViewInput}
    (copied : copyInput s source tail = some input) :
    ∃ cell, s.views[source]? = some cell ∧ input.owner = cell.value.payload.owner ∧
      input.position = cell.value.payload.position ∧ input.allowed = cell.value.payload.allowed ∧
      input.tail = tail ∧ input.operation =
        (match cell.value.origin with | .annotation => none | .operation origin => some origin) := by
  unfold copyInput at copied
  obtain ⟨cell, found, rest⟩ := Option.bind_eq_some_iff.mp copied
  refine ⟨cell, found, ?_⟩
  cases weight : cell.value.sourceWeight with
  | none =>
      by_cases closed : cell.value.payload.closedWeight.isSome = true
      · simp [weight, closed] at rest
      · simp [weight, closed] at rest
        cases rest
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | some w =>
      by_cases valid : validateView s w source cell.value = true
      · simp [weight, valid] at rest
        cases rest
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      · simp [weight, valid] at rest

theorem view_validation_readback {s : Store} {weight id : Nat} {view : ViewRecord}
    (valid : validateView s weight id view = true) :
    ∃ cell, s.weights[weight]? = some cell ∧ cell.value.payload.boundary = id ∧
      cell.value.payload.owner = view.payload.owner ∧ cell.value.payload.position = view.payload.position ∧
      cell.value.payload.allowed = view.payload.allowed ∧ view.sourceWeight = some weight ∧
      view.payload.closedWeight = if view.payload.tail.isNone then some weight else none := by
  cases found : s.weights[weight]? with
  | none => simp [validateView, found] at valid
  | some cell =>
      exact ⟨cell, rfl, by simpa [validateView, found] using valid⟩

end YulangClosure.NativeContextTables
