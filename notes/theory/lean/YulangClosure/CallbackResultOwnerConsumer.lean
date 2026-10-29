import Init

/-!
R22 source-specific callback Result lifecycle candidate. Runtime owners:
receiving.rs::callback_entry, callback_use, execution, observe, callback_grant,
local_grant; machine.rs::OperationResultConsumer, RootCompReturn,
end_execution_view, propagate_request, validate_handler_installation.

This module does not assume a Rust-to-Lean correspondence. No concrete source
trace is instantiated until the sole Cargo receipt authenticates one. Source
policy: 2026-10-10-annotation-effect-hygiene-integration.md §§1.1–1.2.
The RootComp companion is a distinct constructor and is not a callback entry.
-/
namespace YulangClosure.CallbackResultOwnerConsumer

structure Site where
  root : Nat
  occurrence : Nat
  deriving DecidableEq, Repr

inductive Owner where
  | moduleRun
  | invocation (id : Nat)
  deriving DecidableEq, Repr

structure Schema where
  lambda : Site
  formal : Nat
  families : List Nat
  deriving DecidableEq, Repr

structure Receipt where
  owner : Owner
  view : Nat
  slot : Site
  formal : Option Nat
  deriving DecidableEq, Repr

structure Entry where
  schema : Schema
  receiver : Nat
  value : Nat
  incomingView : Nat
  view : Nat
  formalReceipt : Nat
  deriving DecidableEq, Repr

structure Use where
  entry : Nat
  sourceView : Nat
  apply : Site
  resultView : Nat
  receipt : Nat
  deriving DecidableEq, Repr

structure Execution where
  view : Nat
  receipt : Nat
  occurrence : Nat
  deriving DecidableEq, Repr

structure Observation where
  execution : Execution
  observer : Nat
  event : Nat
  deriving DecidableEq, Repr

/-- Historical arena; closing a live delimiter does not remove executions. -/
abbrev ExecutionArena := List (Nat × Nat)

def Authentic (arena : ExecutionArena) (x : Execution) : Prop :=
  arena[x.occurrence]? = some (x.view, x.receipt)

/-- Concrete source constructors retain independent formal and actual-use
receipts. Neither constructor emits an operation request. -/
def entryReceipt (schema : Schema) (receiver view : Nat) : Receipt :=
  ⟨.invocation receiver, view, schema.lambda, some schema.formal⟩

def useReceipt (receiver resultView : Nat) (apply : Site) : Receipt :=
  ⟨.invocation receiver, resultView, apply, none⟩

inductive ViewKind where
  | ordinary | rootComp | callbackEntry (entry : Nat) | callbackResult (useHandle : Nat)
  deriving DecidableEq, Repr

structure View where
  value : Nat
  image : Option Nat
  unknown : Bool
  kind : ViewKind
  deriving DecidableEq, Repr

/-- Arena lookups and the source-schema constructor precede this allocation.
Each handle argument is the corresponding arena length, not a source label. -/
def allocateEntry (schema : Schema) (receiver value incomingHandle entryHandle
    viewHandle receiptHandle : Nat) (incoming : View) : Entry × View × Receipt :=
  (⟨schema, receiver, value, incomingHandle, viewHandle, receiptHandle⟩,
   ⟨value, incoming.image, incoming.unknown, .callbackEntry entryHandle⟩,
   entryReceipt schema receiver viewHandle)

/-- Guard in callback_use after its successful entry/source-view lookups. -/
def UseReady (entry : Entry) (value sourceView : Nat) (view : View) (owner : Owner) : Prop :=
  owner = .invocation entry.receiver ∧ entry.value = value ∧
    entry.view = sourceView ∧ view.value = value

/-- Successful callback_use allocation copies provenance and publishes the
actual Apply receipt before machine.rs mints the operation invocation. -/
def allocateUse (entryHandle useHandle resultView receiptHandle receiver
    sourceView value : Nat) (apply : Site) (source : View) : Use × View × Receipt :=
  (⟨entryHandle, sourceView, apply, resultView, receiptHandle⟩,
   ⟨value, source.image, source.unknown, .callbackResult useHandle⟩,
   useReceipt receiver resultView apply)

theorem allocated_entry_owner (schema : Schema) (receiver value incomingHandle
    entryHandle viewHandle receiptHandle : Nat) (incoming : View) :
    (allocateEntry schema receiver value incomingHandle entryHandle viewHandle receiptHandle incoming).2.2.owner =
      .invocation receiver ∧
    (allocateEntry schema receiver value incomingHandle entryHandle viewHandle receiptHandle incoming).2.2.formal =
      some schema.formal := ⟨rfl, rfl⟩

theorem allocated_use_owner (entryHandle useHandle resultView receiptHandle receiver
    sourceView value : Nat) (apply : Site) (source : View) :
    (allocateUse entryHandle useHandle resultView receiptHandle receiver sourceView value apply source).2.2.owner =
      .invocation receiver ∧
    (allocateUse entryHandle useHandle resultView receiptHandle receiver sourceView value apply source).2.2.slot = apply ∧
    (allocateUse entryHandle useHandle resultView receiptHandle receiver sourceView value apply source).2.1.kind =
      .callbackResult useHandle := ⟨rfl, rfl, rfl⟩

/-- callback_entry after the incoming-view arena lookup. Failure is preserved;
non-invocation owners cannot construct a callback receiving entry. -/
def checkedEntry (schema : Schema) (owner : Owner) (value incomingHandle
    entryHandle viewHandle receiptHandle : Nat) (incoming : View) :
    Option (Entry × View × Receipt) :=
  match owner with
  | .moduleRun => none
  | .invocation receiver =>
      if incoming.value = value then
        some (allocateEntry schema receiver value incomingHandle entryHandle viewHandle receiptHandle incoming)
      else none

/-- Exact callback_entry_for_apply guards after its immutable arena and
receipt_index lookups. Formal entry and actual Name-read receipts are separate;
only the Name receipt must identify the actual callee source occurrence. -/
def ApplyReady (e : Entry) (entryHandle value viewHandle formal : Nat)
    (owner : Owner) (callee : Site) (entryView incoming : View)
    (formalReceipt nameReceipt : Receipt) : Prop :=
  owner = .invocation e.receiver ∧
  entryView.kind = .callbackEntry entryHandle ∧
  e.value = value ∧ e.view = viewHandle ∧ incoming.value = e.value ∧
  e.schema.formal = formal ∧ formalReceipt.owner = owner ∧
  formalReceipt.view = viewHandle ∧ formalReceipt.formal = some formal ∧
  formalReceipt.slot.occurrence = e.schema.lambda.occurrence ∧
  nameReceipt.owner = owner ∧ nameReceipt.view = viewHandle ∧
  nameReceipt.formal = none ∧ nameReceipt.slot = callee

def checkedApply (e : Entry) (entryHandle value viewHandle formal : Nat)
    (owner : Owner) (callee : Site) (entryView incoming : View)
    (formalReceipt nameReceipt : Receipt) : Option Nat :=
  if ApplyReady e entryHandle value viewHandle formal owner callee entryView incoming
      formalReceipt nameReceipt then some entryHandle else none

theorem checked_apply_identity {e : Entry} {entryHandle value viewHandle formal : Nat}
    {owner : Owner} {callee : Site} {entryView incoming : View}
    {formalReceipt nameReceipt : Receipt} {selected : Nat}
    (built : checkedApply e entryHandle value viewHandle formal owner callee entryView incoming
      formalReceipt nameReceipt = some selected) :
    selected = entryHandle ∧ owner = .invocation e.receiver ∧
    e.view = viewHandle ∧ formalReceipt.formal = some formal ∧
    nameReceipt.slot = callee := by
  unfold checkedApply at built
  split at built
  next ready =>
    have same := Option.some.inj built
    rcases ready with ⟨ownerEq, _, _, viewEq, _, _, _, _, formalEq, _, _, _, _, siteEq⟩
    exact ⟨same.symm, ownerEq, viewEq, formalEq, siteEq⟩
  next _ => cases built

/-- callback_use after the actual entry/source-view arena lookups. -/
def checkedUse (e : Entry) (owner : Owner) (value sourceView entryHandle useHandle
    resultView receiptHandle : Nat) (apply : Site) (source : View) :
    Option (Use × View × Receipt) :=
  if UseReady e value sourceView source owner then
    some (allocateUse entryHandle useHandle resultView receiptHandle e.receiver sourceView value apply source)
  else none

/-- execution's CallbackResult arm after exact use/view/receipt lookups.
Entry-only views never pass this guard. No liveness test is imposed on the
historical receipt: runtime execution authenticates immutable evidence. -/
def ExecutionReady (u : Use) (useHandle viewHandle receiptHandle : Nat)
    (view : View) (receipt : Receipt) : Prop :=
  view.kind = .callbackResult useHandle ∧
  u.resultView = viewHandle ∧ u.receipt = receiptHandle ∧
  receipt.view = viewHandle ∧ receipt.formal = none ∧ receipt.slot = u.apply

def checkedExecution (u : Use) (useHandle viewHandle receiptHandle : Nat)
    (view : View) (receipt : Receipt) (arena : ExecutionArena) :
    Option (Execution × ExecutionArena) :=
  if ExecutionReady u useHandle viewHandle receiptHandle view receipt then
    some (⟨viewHandle, receiptHandle, arena.length⟩,
      arena ++ [(viewHandle, receiptHandle)])
  else none

theorem checked_entry_origin {schema : Schema} {owner : Owner}
    {value incomingHandle entryHandle viewHandle receiptHandle : Nat}
    {incoming : View} {out : Entry × View × Receipt}
    (built : checkedEntry schema owner value incomingHandle entryHandle viewHandle receiptHandle incoming = some out) :
    owner = .invocation out.1.receiver ∧ out.1.schema = schema ∧
    out.1.view = viewHandle ∧ out.1.formalReceipt = receiptHandle ∧
    out.2.1.kind = .callbackEntry entryHandle ∧ out.2.2.owner = owner ∧
    out.2.2.view = viewHandle ∧ out.2.2.formal = some schema.formal ∧
    out.2.2.slot = schema.lambda ∧ incoming.value = value := by
  cases owner with
  | moduleRun => cases built
  | invocation receiver =>
      unfold checkedEntry at built
      split at built
      next same =>
        have outEq := Option.some.inj built
        subst out
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, same⟩
      next _ => cases built

/-- The actual successful callback_use constructor forces the original entry
owner and exact source view; this is derived from its checked equation. -/
theorem checked_use_owner {e : Entry} {owner : Owner}
    {value sourceView entryHandle useHandle resultView receiptHandle : Nat}
    {apply : Site} {source : View} {out : Use × View × Receipt}
    (built : checkedUse e owner value sourceView entryHandle useHandle resultView receiptHandle apply source = some out) :
    owner = .invocation e.receiver ∧ e.value = value ∧ e.view = sourceView ∧
    out.1.entry = entryHandle ∧ out.1.sourceView = e.view ∧
    out.2.2.owner = owner ∧ out.2.2.view = resultView ∧
    out.2.2.slot = apply ∧ out.2.2.formal = none := by
  unfold checkedUse at built
  split at built
  next ready =>
    have outEq := Option.some.inj built
    subst out
    rcases ready with ⟨ownerEq, valueEq, viewEq, _⟩
    exact ⟨ownerEq, valueEq, viewEq, rfl, viewEq.symm, ownerEq.symm, rfl, rfl, rfl⟩
  next _ => cases built

/-- Successful execution retains its exact immutable use and Apply receipt;
the fresh occurrence is allocated from the actual execution arena length. -/
theorem checked_execution_identity {u : Use} {useHandle viewHandle receiptHandle : Nat}
    {view : View} {receipt : Receipt} {arena : ExecutionArena}
    {out : Execution × ExecutionArena}
    (built : checkedExecution u useHandle viewHandle receiptHandle view receipt arena = some out) :
    u.resultView = out.1.view ∧ u.receipt = out.1.receipt ∧
    receipt.view = out.1.view ∧ receipt.formal = none ∧ receipt.slot = u.apply ∧
    out.1.occurrence = arena.length ∧ out.2 = arena ++ [(viewHandle, receiptHandle)] := by
  unfold checkedExecution at built
  split at built
  next ready =>
    have outEq := Option.some.inj built
    subst out
    rcases ready with ⟨_, viewEq, receiptEq, exactView, noFormal, siteEq⟩
    exact ⟨viewEq, receiptEq, exactView, noFormal, siteEq, rfl, rfl⟩
  next _ => cases built

/-- All callback_grant joins after its successful arena lookups. Handles remain
separate from the records obtained at those handles. This is not source typing. -/
structure GrantOperands where
  entryHandle : Nat
  entry : Entry
  useHandle : Nat
  useRecord : Use
  formalReceipt : Receipt
  actualReceipt : Receipt
  entryViewKind : Nat
  entryViewValue : Nat
  resultViewValue : Nat
  resultViewKind : Nat
  observation : Observation
  deriving DecidableEq, Repr

/-- Callback branch of local_grant, including its event/authenticity/activity
checks. Actual operation-ID/arm matching is a separate Catch consumer guard. -/
def CallbackGrant (g : GrantOperands) (arena : ExecutionArena)
    (nextObserver event receiver family : Nat) (active : Nat → Bool) : Prop :=
  active receiver = true ∧
  g.observation.event = event ∧
  g.observation.observer < nextObserver ∧
  Authentic arena g.observation.execution ∧
  g.useRecord.entry = g.entryHandle ∧
  g.resultViewKind = g.useHandle ∧
  g.useRecord.resultView = g.observation.execution.view ∧
  g.useRecord.receipt = g.observation.execution.receipt ∧
  g.useRecord.sourceView = g.entry.view ∧
  g.entry.receiver = receiver ∧
  g.entryViewKind = g.entryHandle ∧
  g.entry.value = g.entryViewValue ∧
  g.entry.value = g.resultViewValue ∧
  g.actualReceipt.owner = .invocation receiver ∧
  g.actualReceipt.view = g.useRecord.resultView ∧
  g.actualReceipt.formal = none ∧
  g.actualReceipt.slot = g.useRecord.apply ∧
  g.formalReceipt.owner = .invocation receiver ∧
  g.formalReceipt.view = g.entry.view ∧
  g.formalReceipt.formal = some g.entry.schema.formal ∧
  g.formalReceipt.slot = g.entry.schema.lambda ∧
  family ∈ g.entry.schema.families

inductive Frame where
  | ordinary
  | operationResultConsumer (useHandle : Nat)
  | rootCompReturn (execution : Execution)
  deriving DecidableEq, Repr

/-- Stack order is top first (the reverse of Rust Vec storage order). -/
def delimiters : List Frame → List Execution
  | [] => []
  | .rootCompReturn x :: rest => x :: delimiters rest
  | _ :: rest => delimiters rest

structure Machine where
  frames : List Frame
  executing : List Execution
  executions : ExecutionArena
  active : Nat → Bool

/-- This is the existing source runtime's live delimiter invariant. It is not
used as the definition of source typing, grant, or native execution. -/
def Delimited (s : Machine) : Prop := delimiters s.frames = s.executing

/-- Relevant successful machine transitions. Entry/use allocation and argument
preparation do not add an execution delimiter; the retained result consumer
opens it. Normal return and request unwind close the same exact occurrence.
The history is unchanged on close/retire. Replay opens a fresh occurrence. -/
inductive Step : Machine → Machine → Prop where
  | prepare (s : Machine) (u : Nat) :
      Step s {s with frames := .operationResultConsumer u :: s.frames}
  | resultConsumer (s : Machine) (u view receipt : Nat) (rest : List Frame)
      (ready : s.frames = .operationResultConsumer u :: rest) :
      Step s {s with frames := .rootCompReturn ⟨view, receipt, s.executions.length⟩ :: rest,
        executing := ⟨view, receipt, s.executions.length⟩ :: s.executing,
        executions := s.executions ++ [(view, receipt)]}
  | replay (s : Machine) (view receipt : Nat) :
      Step s {s with frames := .rootCompReturn ⟨view, receipt, s.executions.length⟩ :: s.frames,
        executing := ⟨view, receipt, s.executions.length⟩ :: s.executing,
        executions := s.executions ++ [(view, receipt)]}
  | close (s : Machine) (x : Execution) (rest : List Frame) (xs : List Execution)
      (frame : s.frames = .rootCompReturn x :: rest)
      (execution : s.executing = x :: xs) :
      Step s {s with frames := rest, executing := xs}
  | retire (s : Machine) (receiver : Nat) :
      Step s {s with active := fun id => if id = receiver then false else s.active id}

/-- Preservation across the actual delimiter constructor/consumer shapes,
including dormant uses, request unwind, and fresh replay. -/
theorem step_preserves_delimiters {before after : Machine}
    (step : Step before after) (inv : Delimited before) : Delimited after := by
  cases step with
  | prepare s u => exact inv
  | resultConsumer s u view receipt rest ready =>
      unfold Delimited at inv ⊢
      rw [ready] at inv
      change _ :: delimiters _ = _ :: s.executing
      exact congrArg (List.cons _) inv
  | replay s view receipt => exact congrArg (List.cons _) inv
  | close s x rest xs frame execution =>
      unfold Delimited at inv ⊢
      rw [frame, execution] at inv
      exact List.cons.inj inv |>.2
  | retire s receiver => exact inv

/-- Historical request authenticity survives the closure that precedes Catch
query. No continued liveness of the observing execution is assumed. -/
theorem close_preserves_observation (s : Machine) (rest : List Frame)
    (xs : List Execution) (o : Observation)
    (auth : Authentic s.executions o.execution) :
    Authentic ({s with frames := rest, executing := xs} : Machine).executions
      o.execution := auth

/-- Closing a delimiter keeps the exact same event, original receipts, owner,
permission, and execution record usable by the positive callback branch. -/
theorem close_preserves_grant (s : Machine) (rest : List Frame)
    (xs : List Execution) (g : GrantOperands) (nextObserver event receiver family : Nat)
    (grant : CallbackGrant g s.executions nextObserver event receiver family s.active) :
    CallbackGrant g ({s with frames := rest, executing := xs} : Machine).executions
      nextObserver event receiver family s.active := grant

/-- Owner/lifetime consequence for the actual grant branch: the candidate
owner is the original callback-entry receiver and remains active at query time;
the actual contribution is this exact event with an authentic historical
execution, independently of the formal permission membership. -/
theorem grant_owner_lifetime {g : GrantOperands} {s : Machine}
    {nextObserver event receiver family : Nat}
    (grant : CallbackGrant g s.executions nextObserver event receiver family s.active) :
    g.entry.receiver = receiver ∧ s.active receiver = true ∧
    g.observation.event = event ∧ Authentic s.executions g.observation.execution ∧
    g.actualReceipt.owner = .invocation receiver ∧
    g.formalReceipt.owner = .invocation receiver ∧ family ∈ g.entry.schema.families := by
  rcases grant with ⟨live, eventEq, _, authentic, _, _, _, _, _, receiverEq,
    _, _, _, useOwner, _, _, _, formalOwner, _, _, _, permission⟩
  exact ⟨receiverEq, live, eventEq, authentic, useOwner, formalOwner, permission⟩

/-- Retirement of the original receiver cannot transfer its grant to a fresh
replay owner. This is independent of historical receipt authenticity. -/
theorem retired_receiver_rejected (g : GrantOperands) (s : Machine)
    (nextObserver event receiver family : Nat) :
    ¬ CallbackGrant g s.executions nextObserver event receiver family
      (fun id => if id = receiver then false else s.active id) := by
  intro grant
  have h := grant.1
  simp at h

/-- A sibling event cannot substitute for the observation's own actual request. -/
theorem sibling_event_rejected (g : GrantOperands) (arena : ExecutionArena)
    (nextObserver event receiver family : Nat) (active : Nat → Bool)
    (different : g.observation.event ≠ event) :
    ¬ CallbackGrant g arena nextObserver event receiver family active := by
  intro grant
  exact different grant.2.1

theorem sibling_receiver_rejected (g : GrantOperands) (arena : ExecutionArena)
    (nextObserver event receiver family : Nat) (active : Nat → Bool)
    (different : g.entry.receiver ≠ receiver) :
    ¬ CallbackGrant g arena nextObserver event receiver family active := by
  intro grant
  rcases grant with ⟨_, _, _, _, _, _, _, _, _, same, _⟩
  exact different same

/-- Permission membership is necessary independently of actual contribution;
this theorem does not assert that any request was emitted. -/
theorem absent_permission_rejected (g : GrantOperands) (arena : ExecutionArena)
    (nextObserver event receiver family : Nat) (active : Nat → Bool)
    (absent : family ∉ g.entry.schema.families) :
    ¬ CallbackGrant g arena nextObserver event receiver family active := by
  intro grant
  rcases grant with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, member⟩
  exact absent member

/-- The operation-ID filter in propagate_request precedes committed selection.
The same residual request is returned by a nonmatching inner operation arm. -/
def operationFilter (armOperation requestOperation event : Nat) : Option Nat :=
  if armOperation = requestOperation then none else some event

theorem distinct_operation_keeps_event (signalOperation writeOperation writeEvent : Nat)
    (distinct : signalOperation ≠ writeOperation) :
    operationFilter signalOperation writeOperation writeEvent = some writeEvent := by
  simp [operationFilter, distinct]

/-!
Parent application remains OPEN pending authenticated arena/owner/source joins,
concrete event and committed Catch selection, return 1, and the independently
owned RootComp companion's same write event reaching outer receive. Neither the
Step projection nor CallbackGrant is a native correspondence assumption. All
source Simple-sub A/B quantifiers, effect hygiene, source safety, principality,
termination, and production authority remain unchanged and OPEN.
-/
end YulangClosure.CallbackResultOwnerConsumer
