import YulangClosure.OriginalSourceInterpretation

/-!
The selected immutable pair `my f x = g; my g y = f`.

Authority: native-recursive-interface-definition §§2–3, selecting
recursive-original-interface-embedding §§3–6, and the selected Knu operator.
The raw constructor algebra below retains an arbitrary original carrier
machine. It does not assume a pair execution classification, a completed
world, opposite-member validity, or `sourceCases`/`replace`.

The native suffix is an actual composition of parameter-cell allocation,
captured Name/read-receipt construction, and owned invocation return.
The carrier's complete raw transition graph remains independent of typing.
The source receipt is explicitly phase-indexed; it is not asserted to be an
already executed native RootComp receipt at a Value-entry boundary.
-/
namespace YulangClosure.OriginalRecursivePair

open NativeClosureEnvironment SourceIdentityWorld
open OriginalSourceInterpretation

inductive Side where
  | first | second
  deriving DecidableEq, Repr

def Side.other : Side → Side
  | .first => .second
  | .second => .first

theorem other_other (side : Side) : side.other.other = side := by cases side <;> rfl
theorem other_ne (side : Side) : side.other ≠ side := by cases side <;> decide

/-- Original resolved source data, not a supplied rule tree or typing proof. -/
structure SourcePair where
  group : OriginalSource.Site
  binding : Side → OriginalSource.Site
  name : Side → OriginalSource.Name
  lambda : Side → OriginalSource.Site
  formalSite : Side → OriginalSource.Site
  formalName : Side → OriginalSource.Name
  nameSite : Side → OriginalSource.Site

def SourcePair.formal (pair : SourcePair) (side : Side) : OriginalSource.Formal :=
  ⟨pair.formalSite side, pair.formalName side, none, false⟩

def SourcePair.body (pair : SourcePair) (side : Side) : OriginalSource.Source .expression :=
  .name ⟨pair.nameSite side, none⟩ (pair.name side.other)

def SourcePair.member (pair : SourcePair) (side : Side) : OriginalSource.Source .expression :=
  .lambda ⟨pair.lambda side, none⟩ (pair.formal side)
    (.varPattern (pair.formalSite side) (pair.formalName side)) (pair.body side)

def SourcePair.bindings (pair : SourcePair) : OriginalSource.Source .bindings :=
  .binding (pair.binding .first) (pair.name .first) none (pair.member .first)
    (.binding (pair.binding .second) (pair.name .second) none (pair.member .second)
      .bindingsNil)

def SourcePair.statement (pair : SourcePair) : OriginalSource.Source .statement :=
  .letS pair.group true pair.bindings

theorem source_value_entry (pair : SourcePair) (side : Side) :
    (pair.formal side).entry = .value := rfl

theorem source_body_opposite (pair : SourcePair) (side : Side) :
    pair.body side = .name ⟨pair.nameSite side, none⟩ (pair.name side.other) := rfl

/-- Fresh receiver construction is the native append/push/current operation.
It does not create a handler grant or revive an exited maker. -/
def enter (control : Control Site) (call provider : Site) : Control Site :=
  ⟨control.invocations.push ⟨call, provider, true⟩,
    control.invocations.size :: control.active, .invocation control.invocations.size⟩

theorem enter_current (control : Control Site) (call provider : Site) :
    (enter control call provider).current = .invocation control.invocations.size := rfl

theorem enter_registered (control : Control Site) (call provider : Site) :
    (enter control call provider).invocations.cell control.invocations.size =
      some ⟨call, provider, true⟩ := push_current _ _

theorem enter_preserves_old (control : Control Site) (call provider : Site)
    (id : Nat) (old : id < control.invocations.size) :
    (enter control call provider).invocations.cell id = control.invocations.cell id :=
  push_old _ _ _ old

def enterWorld (world : World K D V ViewData Site Rest) (call provider : Site) :
    World K D V ViewData Site Rest :=
  {world with control := enter world.control call provider}

theorem enter_then_leave (control : Control Site) (call provider : Site) :
    (enter control call provider).leave control.invocations.size control.current =
      some ⟨deactivate (control.invocations.push ⟨call, provider, true⟩)
        control.invocations.size ⟨call, provider, true⟩,
        control.active, control.current⟩ :=
  leave_success rfl rfl (enter_registered _ _ _) rfl

/-- Data owned by the original body and the *current* invocation delimiter.
The owner/previous fields are read from the actual resumed delimiter, not
restored from a closure-maker snapshot. -/
structure Suffix (K Site : Type) where
  capturedEnvironment : Nat
  formal : K
  opposite : K
  nameSite : Site
  dispatch : Option Nat
  owner : Nat
  previous : Owner

/-- Unlike the identity suffix, the Name reads the old opposite capture from
the newly extended parameter environment. -/
def suffixStep [DecidableEq K] [DecidableEq V] (suffix : Suffix K Site) :
    SuffixState K D V ViewData Site Rest → Option (SuffixState K D V ViewData Site Rest)
  | .entry world returned =>
      match found : nodeAt world.environments suffix.capturedEnvironment with
      | none => none
      | some node => some (.body
          (bindValue world suffix.capturedEnvironment suffix.formal returned node found)
          world.environments.size)
  | .body world environment =>
      (observeName world environment suffix.opposite suffix.nameSite suffix.dispatch).map
        (fun result => .returning result.1 result.2)
  | .returning world result =>
      (returnOwned world suffix.owner suffix.previous result).map
        (fun returned => .done returned.1 returned.2)
  | .done _ _ => none

theorem bind_captured_read [DecidableEq K]
    (world : World K D V ViewData Site Rest) (suffix : Suffix K Site)
    (returned : Received V) (node : Node K D)
    (found : nodeAt world.environments suffix.capturedEnvironment = some node)
    (distinct : suffix.formal ≠ suffix.opposite)
    (cell : Nat) (within : cell < world.cells.size)
    (captured : lookupKey suffix.opposite world.environments suffix.capturedEnvironment = some cell) :
    observe (fun key => decide (key = suffix.opposite))
      (bindValue world suffix.capturedEnvironment suffix.formal returned node found).environments
      world.environments.size
      (bindValue world suffix.capturedEnvironment suffix.formal returned node found).cells.cell =
      world.cells.cell cell := by
  change (lookupKey suffix.opposite
    (.append world.environments suffix.capturedEnvironment
      (some (suffix.formal, world.cells.size)) node.dispatch) world.environments.size).bind
        (world.cells.push returned.asValue).cell = _
  rw [parameter_preserves _ _ _ _ _ _ distinct, captured]
  exact push_old _ _ _ within

/-- Construct the two different-value source actions after the actual typed
carrier Return. No successful Name/return or opposite-membership premise. -/
theorem opposite_suffix [DecidableEq K] [DecidableEq V]
    (world : World K D V ViewData Site Rest) (suffix : Suffix K Site)
    (returned opposite : Received V) (node : Node K D)
    (found : nodeAt world.environments suffix.capturedEnvironment = some node)
    (distinct : suffix.formal ≠ suffix.opposite)
    (cell : Nat) (within : cell < world.cells.size)
    (captured : lookupKey suffix.opposite world.environments suffix.capturedEnvironment = some cell)
    (stored : world.cells.cell cell = some opposite)
    (matching : Matches world.receiving opposite)
    (rest : List Nat) (invocation : Invocation Site)
    (current : world.control.current = .invocation suffix.owner)
    (stack : world.control.active = suffix.owner :: rest)
    (registered : world.control.invocations.cell suffix.owner = some invocation)
    (live : invocation.active = true) :
    let bound := bindValue world suffix.capturedEnvironment suffix.formal returned node found
    let read := {bound with receiving :=
      world.receiving.record (.invocation suffix.owner) opposite.view suffix.nameSite none}
    let final := {read with control :=
      ⟨deactivate world.control.invocations suffix.owner invocation, rest, suffix.previous⟩}
    observeName bound world.environments.size suffix.opposite suffix.nameSite suffix.dispatch =
      some (read, opposite.atName suffix.dispatch) ∧
    returnOwned read suffix.owner suffix.previous (opposite.atName suffix.dispatch) =
      some (final, (opposite.atName suffix.dispatch).asValue) ∧
    final.receiving.receipts.cell world.receiving.receipts.size =
      some ⟨.invocation suffix.owner, opposite.view, suffix.nameSite, none⟩ ∧
    final.receiving.receipts.size = world.receiving.receipts.size + 1 ∧
    final.cells.cell world.cells.size = some returned.asValue ∧
    final.cells.cell cell = some opposite ∧
    final.receiving.views = world.receiving.views ∧
    final.rest = world.rest := by
  dsimp only
  have read := (bind_captured_read world suffix returned node found distinct cell within captured).trans stored
  refine ⟨?_, ?_, receipt_new _ _ _ _ _, rfl, push_current _ _, ?_, rfl, rfl⟩
  · simpa only [bindValue, current] using
      (name_success (site := suffix.nameSite) (dispatch := suffix.dispatch) read matching)
  · have leave := leave_success current stack registered live (previous := suffix.previous)
    simp only [returnOwned, bindValue, leave]
    rfl
  · exact (push_old _ _ _ within).trans stored

/-- The finite post-Force execution preserves the opposite value even when
the independently returned argument value is different. -/
theorem opposite_suffix_prefixes [DecidableEq K] [DecidableEq V]
    (world : World K D V ViewData Site Rest) (suffix : Suffix K Site)
    (returned opposite : Received V) (node : Node K D)
    (found : nodeAt world.environments suffix.capturedEnvironment = some node)
    (distinct : suffix.formal ≠ suffix.opposite)
    (cell : Nat) (within : cell < world.cells.size)
    (captured : lookupKey suffix.opposite world.environments suffix.capturedEnvironment = some cell)
    (stored : world.cells.cell cell = some opposite)
    (matching : Matches world.receiving opposite)
    (rest : List Nat) (invocation : Invocation Site)
    (current : world.control.current = .invocation suffix.owner)
    (stack : world.control.active = suffix.owner :: rest)
    (registered : world.control.invocations.cell suffix.owner = some invocation)
    (live : invocation.active = true)
    {n : Nat} {last : SuffixState K D V ViewData Site Rest}
    (path : Prefix (fun first next => suffixStep suffix first = some next)
      n (.entry world returned) last) :
    let bound := bindValue world suffix.capturedEnvironment suffix.formal returned node found
    let read := {bound with receiving :=
      world.receiving.record (.invocation suffix.owner) opposite.view suffix.nameSite none}
    let final := {read with control :=
      ⟨deactivate world.control.invocations suffix.owner invocation, rest, suffix.previous⟩}
    last = .entry world returned ∨
      last = .body bound world.environments.size ∨
      last = .returning read (opposite.atName suffix.dispatch) ∨
      last = .done final (opposite.atName suffix.dispatch).asValue := by
  have actions := opposite_suffix world suffix returned opposite node found distinct cell within
    captured stored matching rest invocation current stack registered live
  dsimp only at actions ⊢
  apply four_phase_prefix (suffixStep suffix) _ _ _ _
    (by
      simp only [suffixStep]
      split
      · rename_i absent
        cases absent.symm.trans found
      · rename_i other present
        have same : other = node := Option.some.inj (present.symm.trans found)
        subst other
        rfl)
    (by simp only [suffixStep, actions.1, Option.map_some])
    (by simp only [suffixStep, actions.2.1, Option.map_some]) rfl path

/-! ## Exact carrier sequencing

The independent carrier supplies its raw state/transition/return graph, not
a successful or eventually returning execution. The source wrapper retains
its ordered suffix through every administrative step, request and resumption.
The actual returned delimiter can have new activation IDs after raw replay.
-/

/-- Fixed source-owned operands of the unfinished suffix. -/
structure BodyPlan (K Site : Type) where
  capturedEnvironment : Nat
  formal : K
  opposite : K
  nameSite : Site

def Suffix.plan (suffix : Suffix K Site) : BodyPlan K Site :=
  ⟨suffix.capturedEnvironment, suffix.formal, suffix.opposite, suffix.nameSite⟩

/-- Actual Return data. The source operands are constructed by the wrapper;
they are not supplied or filtered by the carrier. The delimiter is the one
at the current Return, including after raw resumption. -/
structure Returned (K D V ViewData Site Rest : Type) where
  world : World K D V ViewData Site Rest
  value : Received V
  dispatch : Option Nat
  owner : Nat
  previous : Owner

def Returned.suffix (packet : Returned K D V ViewData Site Rest)
    (plan : BodyPlan K Site) : Suffix K Site :=
  ⟨plan.capturedEnvironment, plan.formal, plan.opposite, plan.nameSite,
    packet.dispatch, packet.owner, packet.previous⟩

theorem returned_plan (packet : Returned K D V ViewData Site Rest) (plan : BodyPlan K Site) :
    (packet.suffix plan).plan = plan := rfl

/-- Independent raw Force component, with no source-body typing or output
certificate field. Response data retains the original raw handle, operation,
current world and scoped incidence; no membership test forms this relation. -/
structure Carrier (K D V ViewData Site Rest : Type) where
  State : Type
  Request : Type
  Response : Type
  internal : State → State → Prop
  requested : State → Request → Prop
  resume : State → Request → Response → State → Prop
  returned : State → Returned K D V ViewData Site Rest → Prop

inductive Carrier.Move (carrier : Carrier K D V ViewData Site Rest) :
    carrier.State → carrier.State → Prop where
  | internal {first next} : carrier.internal first next → carrier.Move first next
  | resume {first next request response} :
      carrier.requested first request → carrier.resume first request response next →
      carrier.Move first next

inductive State (carrier : Carrier K D V ViewData Site Rest) where
  | forcing (current : carrier.State)
  | suffix (actual : Suffix K Site) (current : SuffixState K D V ViewData Site Rest)

/-- Selected ordinary Bind. A request cannot enter the rebind branch;
resumption cannot replay receipt. No returned carrier packet is excluded. -/
inductive Move [DecidableEq K] [DecidableEq V]
    (carrier : Carrier K D V ViewData Site Rest) (plan : BodyPlan K Site) :
    State carrier → State carrier → Prop where
  | force {first next} : carrier.Move first next → Move carrier plan (.forcing first) (.forcing next)
  | returned {current packet} : carrier.returned current packet →
      Move carrier plan (.forcing current)
        (.suffix (packet.suffix plan) (.entry packet.world packet.value))
  | suffix {actual first next} : suffixStep actual first = some next →
      Move carrier plan (.suffix actual first) (.suffix actual next)

/-- `M_E^ctor` cases reconstructed from raw prefixes. The first case covers
every zero/admin/pending/divergent Force prefix. The second retains the actual
Return before any suffix action. This contains no semantic membership atom. -/
def ConstructorPrefix [DecidableEq K] [DecidableEq V]
    (carrier : Carrier K D V ViewData Site Rest) (plan : BodyPlan K Site)
    (initial : carrier.State) : State carrier → Prop
  | .forcing current => ∃ count, Prefix carrier.Move count initial current
  | .suffix actual current => ∃ count before packet suffixCount,
      Prefix carrier.Move count initial before ∧ carrier.returned before packet ∧
      actual = packet.suffix plan ∧
      Prefix (fun first next => suffixStep actual first = some next)
        suffixCount (.entry packet.world packet.value) current

theorem constructor_prefix_step [DecidableEq K] [DecidableEq V]
    {carrier : Carrier K D V ViewData Site Rest} {plan : BodyPlan K Site}
    {initial : carrier.State} {first next : State carrier}
    (prior : ConstructorPrefix carrier plan initial first) (step : Move carrier plan first next) :
    ConstructorPrefix carrier plan initial next := by
  cases step with
  | force move =>
      obtain ⟨count, history⟩ := prior
      exact ⟨count + 1, .snoc history move⟩
  | returned returned =>
      obtain ⟨count, history⟩ := prior
      exact ⟨count, _, _, 0, history, returned, rfl, .refl _⟩
  | suffix move =>
      obtain ⟨count, before, packet, suffixCount, history, returned, actualEq, rest⟩ := prior
      exact ⟨count, before, packet, suffixCount + 1, history, returned, actualEq,
        .snoc rest move⟩

theorem every_raw_prefix [DecidableEq K] [DecidableEq V]
    {carrier : Carrier K D V ViewData Site Rest} {plan : BodyPlan K Site}
    {initial : carrier.State} {count : Nat} {last : State carrier}
    (path : Prefix (Move carrier plan) count (.forcing initial) last) :
    ConstructorPrefix carrier plan initial last := by
  have preserve : ∀ {first next : State carrier} {length : Nat},
      Prefix (Move carrier plan) length first next →
      ConstructorPrefix carrier plan initial first → ConstructorPrefix carrier plan initial next := by
    intro first next length steps
    induction steps with
    | refl => exact fun prior => prior
    | snoc prior move ih => exact fun valid => constructor_prefix_step (ih valid) move
  exact preserve path ⟨0, .refl _⟩

theorem force_prefix_embeds [DecidableEq K] [DecidableEq V]
    {carrier : Carrier K D V ViewData Site Rest} (plan : BodyPlan K Site)
    {initial current : carrier.State} {count : Nat}
    (path : Prefix carrier.Move count initial current) :
    Prefix (Move carrier plan) count (.forcing initial) (.forcing current) := by
  induction path with
  | refl => exact .refl _
  | snoc prior move ih => exact .snoc ih (.force move)

theorem suffix_prefix_embeds [DecidableEq K] [DecidableEq V]
    {carrier : Carrier K D V ViewData Site Rest} (plan : BodyPlan K Site)
    {actual : Suffix K Site}
    {first current : SuffixState K D V ViewData Site Rest} {count : Nat}
    (path : Prefix (fun a b => suffixStep actual a = some b) count first current) :
    Prefix (Move carrier plan) count (.suffix actual first) (.suffix actual current) := by
  induction path with
  | refl => exact .refl _
  | snoc prior move ih => exact .snoc ih (.suffix move)

theorem prefix_append {S : Type} {step : S → S → Prop}
    {first middle last : S} {left right : Nat}
    (one : Prefix step left first middle) (two : Prefix step right middle last) :
    Prefix step (left + right) first last := by
  induction two with
  | refl => simpa using one
  | snoc prior move ih => simpa [Nat.add_assoc] using Prefix.snoc (ih one) move

/-- Reverse construction does not require typing either. -/
theorem constructor_prefix_executes [DecidableEq K] [DecidableEq V]
    {carrier : Carrier K D V ViewData Site Rest} {plan : BodyPlan K Site}
    {initial : carrier.State} {last : State carrier}
    (witness : ConstructorPrefix carrier plan initial last) :
    ∃ count, Prefix (Move carrier plan) count (.forcing initial) last := by
  cases last with
  | forcing current =>
      obtain ⟨count, history⟩ := witness
      exact ⟨count, force_prefix_embeds plan history⟩
  | suffix actual current =>
      obtain ⟨count, before, packet, suffixCount, history, returned, actualEq, rest⟩ := witness
      subst actual
      exact ⟨count + 1 + suffixCount,
        prefix_append (.snoc (force_prefix_embeds plan history) (.returned returned))
          (suffix_prefix_embeds plan rest)⟩

theorem constructor_prefix_iff [DecidableEq K] [DecidableEq V]
    {carrier : Carrier K D V ViewData Site Rest} {plan : BodyPlan K Site}
    {initial : carrier.State} {last : State carrier} :
    ConstructorPrefix carrier plan initial last ↔
      ∃ count, Prefix (Move carrier plan) count (.forcing initial) last :=
  ⟨constructor_prefix_executes, fun ⟨_, history⟩ => every_raw_prefix history⟩

/-- Actual response/current-state data is preserved, with the same source
suffix and no inserted receipt or result-membership test. -/
theorem resume_keeps_suffix [DecidableEq K] [DecidableEq V]
    {carrier : Carrier K D V ViewData Site Rest} (plan : BodyPlan K Site)
    {first next : carrier.State} {request : carrier.Request} {response : carrier.Response}
    (pending : carrier.requested first request)
    (resumed : carrier.resume first request response next) :
    Move carrier plan (.forcing first) (.forcing next) := .force (.resume pending resumed)

/-! ## Source-constructed immutable capture graph

Both finite closures point at the same final lexical environment. Their cells
hold distinct actual value handles. The knot consists of numeric references,
so constructing it does not require a circular Lean value or either member's
semantic validity. Arbitrary old cells, views, providers and rest fields stay.
-/

structure SourceClosure where
  source : OriginalSource.Source .expression
  formal : OriginalSource.Formal
  code : Closure (OriginalSource.Source .expression)

structure Heap (D ViewData Rest : Type) where
  world : World Nat D Nat ViewData Nat Rest
  providers : Store (Option SourceClosure)

def SourcePair.capturedClosure (pair : SourcePair) (environment : Nat) (side : Side) : SourceClosure :=
  ⟨pair.member side, pair.formal side, capture environment (pair.body side)⟩

def Side.offset : Side → Nat
  | .first => 0
  | .second => 1

def Heap.packet (heap : Heap D ViewData Rest) (side : Side) : Received Nat :=
  ⟨heap.providers.size + side.offset, .value,
    heap.world.receiving.views.size + side.offset, none⟩

def Heap.install (heap : Heap D ViewData Rest) (pair : SourcePair)
    (parent : Nat) (node : Node Nat D)
    (_found : nodeAt heap.world.environments parent = some node)
    (metadata : Side → ViewData) : Heap D ViewData Rest :=
  let environment := heap.world.environments.size + 1
  { providers := (heap.providers.push (some (pair.capturedClosure environment .first))).push
      (some (pair.capturedClosure environment .second))
    world := {heap.world with
      cells := (heap.world.cells.push (heap.packet .first)).push (heap.packet .second)
      environments := .append
        (.append heap.world.environments parent
          (some (pair.name .first, heap.world.cells.size)) node.dispatch)
        heap.world.environments.size (some (pair.name .second, heap.world.cells.size + 1)) node.dispatch
      receiving := {heap.world.receiving with
        views := (heap.world.receiving.views.push
          ⟨heap.providers.size, metadata .first⟩).push
            ⟨heap.providers.size + 1, metadata .second⟩} } }

theorem installed_provider (heap : Heap D ViewData Rest) (pair : SourcePair)
    (parent : Nat) (node : Node Nat D)
    (found : nodeAt heap.world.environments parent = some node)
    (metadata : Side → ViewData) (side : Side) :
    (heap.install pair parent node found metadata).providers.cell
      (heap.providers.size + side.offset) =
      some (some (pair.capturedClosure (heap.world.environments.size + 1) side)) := by
  cases side <;> simp [Heap.install, Side.offset, Store.push]

theorem installed_packet (heap : Heap D ViewData Rest) (pair : SourcePair)
    (parent : Nat) (node : Node Nat D)
    (found : nodeAt heap.world.environments parent = some node)
    (metadata : Side → ViewData) (side : Side) :
    (heap.install pair parent node found metadata).world.cells.cell
      (heap.world.cells.size + side.offset) = some (heap.packet side) := by
  cases side <;> simp [Heap.install, Side.offset, Store.push]

theorem installed_view (heap : Heap D ViewData Rest) (pair : SourcePair)
    (parent : Nat) (node : Node Nat D)
    (found : nodeAt heap.world.environments parent = some node)
    (metadata : Side → ViewData) (side : Side) :
    Matches (heap.install pair parent node found metadata).world.receiving (heap.packet side) := by
  refine ⟨⟨heap.providers.size + side.offset, metadata side⟩, ?_, rfl⟩
  cases side <;> simp [Heap.install, Heap.packet, Side.offset, Store.push]

theorem installed_lookup (heap : Heap D ViewData Rest) (pair : SourcePair)
    (parent : Nat) (node : Node Nat D)
    (found : nodeAt heap.world.environments parent = some node)
    (metadata : Side → ViewData) (names : pair.name .first ≠ pair.name .second)
    (side : Side) :
    lookupKey (pair.name side) (heap.install pair parent node found metadata).world.environments
      (heap.world.environments.size + 1) = some (heap.world.cells.size + side.offset) := by
  cases side
  · simp [Heap.install, lookupKey, lookup, Arena.size, Side.offset, Ne.symm names]
  · simp [Heap.install, lookupKey, lookup, Arena.size, Side.offset]

theorem installed_capture (heap : Heap D ViewData Rest) (pair : SourcePair)
    (parent : Nat) (node : Node Nat D)
    (found : nodeAt heap.world.environments parent = some node)
    (metadata : Side → ViewData) (names : pair.name .first ≠ pair.name .second)
    (side : Side) :
    observe (fun key => decide (key = pair.name side.other))
      (heap.install pair parent node found metadata).world.environments
      (pair.capturedClosure (heap.world.environments.size + 1) side).code.savedEnvironment
      (heap.install pair parent node found metadata).world.cells.cell =
        some (heap.packet side.other) := by
  change (lookupKey (pair.name side.other) _ (heap.world.environments.size + 1)).bind _ = _
  rw [installed_lookup heap pair parent node found metadata names side.other]
  exact installed_packet heap pair parent node found metadata side.other

theorem distinct_installed_values (heap : Heap D ViewData Rest) :
    (heap.packet .first).value ≠ (heap.packet .second).value := by
  simp [Heap.packet, Side.offset]

theorem installation_keeps_receipts (heap : Heap D ViewData Rest) (pair : SourcePair)
    (parent : Nat) (node : Node Nat D)
    (found : nodeAt heap.world.environments parent = some node)
    (metadata : Side → ViewData) :
    (heap.install pair parent node found metadata).world.receiving.receipts =
      heap.world.receiving.receipts ∧
    (heap.install pair parent node found metadata).world.receiving.index =
      heap.world.receiving.index ∧
    (heap.install pair parent node found metadata).world.control = heap.world.control ∧
    (heap.install pair parent node found metadata).world.rest = heap.world.rest := ⟨rfl, rfl, rfl, rfl⟩

def SourcePair.plan (pair : SourcePair) (environment : Nat) (side : Side) : BodyPlan Nat Nat :=
  ⟨environment, pair.formalName side, pair.name side.other, pair.nameSite side⟩

theorem source_plan_body (pair : SourcePair) (environment : Nat) (side : Side) :
    pair.body side = .name ⟨(pair.plan environment side).nameSite, none⟩
      (pair.plan environment side).opposite := rfl

/-- Resolved binding identities for this selected source pair. This excludes
the different program whose body resolves to the formal itself. -/
structure SourcePair.Hygienic (pair : SourcePair) : Prop where
  members : pair.name .first ≠ pair.name .second
  formalFirst : ∀ side, pair.formalName side ≠ pair.name .first
  formalSecond : ∀ side, pair.formalName side ≠ pair.name .second

theorem SourcePair.Hygienic.opposite {pair : SourcePair} (valid : pair.Hygienic) (side : Side) :
    pair.formalName side ≠ pair.name side.other := by
  cases side
  · exact valid.formalSecond .first
  · exact valid.formalFirst .second

def SourcePair.memberBinding (pair : SourcePair) (side : Side) : OriginalSource.Binding :=
  {name := pair.name side, owner := pair.binding side, kind := .internal, component := some pair.group}

def SourcePair.groupContext (pair : SourcePair) (outside : OriginalSource.Context) :
    OriginalSource.Context := [pair.memberBinding .first, pair.memberBinding .second] ++ outside

theorem generated_group_context (pair : SourcePair) (outside : OriginalSource.Context) :
    pair.bindings.bindingRecords.map (fun binding =>
      {binding with kind := .internal, component := some pair.group}) ++ outside =
      pair.groupContext outside := rfl

def SourcePair.formalBinding (pair : SourcePair) (side : Side) : OriginalSource.Binding :=
  {name := (pair.formal side).name, owner := (pair.formal side).site, kind := .formal,
    annotation := (pair.formal side).annotation, entry := some (pair.formal side).entry,
    singleUse := (pair.body side).nameCount (pair.formal side).name == 1}

def SourcePair.bodyContext (pair : SourcePair) (outside : OriginalSource.Context) (side : Side) :
    OriginalSource.Context := pair.formalBinding side :: pair.groupContext outside

/-- Exact `patternContext` computation in the original Lambda rule: the
variable pattern already has the registered formal identity. -/
theorem generated_body_context (pair : SourcePair) (outside : OriginalSource.Context) (side : Side) :
    (OriginalSource.Source.varPattern (pair.formalSite side) (pair.formalName side)).bindingRecords.filter
      (fun binding => !((pair.bodyContext outside side).any
        (fun prior => prior.name == binding.name))) ++ pair.bodyContext outside side =
      pair.bodyContext outside side := by
  simp [OriginalSource.Source.bindingRecords, SourcePair.bodyContext,
    SourcePair.formalBinding, SourcePair.formal]

theorem source_opposite_lookup (pair : SourcePair) (valid : pair.Hygienic)
    (outside : OriginalSource.Context) (side : Side) :
    OriginalSource.lookupBinding (pair.bodyContext outside side) (pair.name side.other) =
      some (pair.memberBinding side.other) := by
  cases side <;>
    simp [OriginalSource.lookupBinding, SourcePair.bodyContext, SourcePair.groupContext,
      SourcePair.formalBinding, SourcePair.formal, SourcePair.memberBinding, Side.other,
      valid.members, valid.formalFirst, valid.formalSecond]

/-- A concrete original Name rule, with the same resolved opposite member
for both local predicates. It is not an assumption of source typing. -/
theorem source_opposite_rule (pair : SourcePair) (valid : pair.Hygienic)
    (outside : OriginalSource.Context) (side : Side) :
    OriginalSource.sourceRules (pair.bodyContext outside side) (pair.body side) =
      .rule .name (pair.nameSite side) (pair.bodyContext outside side)
        [.atom { (OriginalSource.atom .resolvedSameBinding (pair.nameSite side)
            (pair.bodyContext outside side)) with
            names := [pair.name side.other], binding := some (pair.memberBinding side.other) },
         .atom { (OriginalSource.atom .computedFetchOnce (pair.nameSite side)
            (pair.bodyContext outside side)) with
            names := [pair.name side.other], binding := some (pair.memberBinding side.other) }]
        .nil := by
  simp only [SourcePair.body, OriginalSource.sourceRules, source_opposite_lookup pair valid]
  rfl

/-- The parent L4 obligation is emitted at this exact source registration.
The theorem locates it; it does not assert that the atom has been discharged. -/
theorem source_pair_joint_obligation (pair : SourcePair) (outside : OriginalSource.Context) :
    ∃ children, OriginalSource.sourceRules outside pair.statement =
      .rule .letS pair.group outside
        [.atom { (OriginalSource.atom .sourceLetRegistration pair.group outside) with
            names := [pair.name .first, pair.name .second], flag := some true },
         .atom (OriginalSource.atom .recursiveJointMemberWorld pair.group (pair.groupContext outside))]
        children := by
  refine ⟨.one (OriginalSource.bindingsRulesK (pair.groupContext outside) pair.bindings false
    (.publishGroup [(pair.name .first, pair.binding .first), (pair.name .second, pair.binding .second)]
      (.rule .empty pair.group outside [] .nil))), ?_⟩
  simp only [SourcePair.statement, OriginalSource.sourceRules, OriginalSource.statementRulesK]
  rfl

/-! ## Receiver and original source receipt

`receiveWorld` is the selected original source receipt constructor. Native
Value entry does not necessarily execute a RootComp receipt there; therefore
this is not asserted equal to the Rust Value-entry transition. The native
Name receipt in `opposite_suffix` remains a separate actual mutation.
-/

structure EntryData (K V Site : Type) where
  call : Site
  provider : Site
  slot : Site
  formal : K
  carrier : Received V

def receiveWorld [DecidableEq K] (world : World K D V ViewData Site Rest)
    (entry : EntryData K V Site) : World K D V ViewData Site Rest :=
  {world with receiving :=
    world.receiving.record world.control.current entry.carrier.view entry.slot (some entry.formal)}

theorem source_receipt_fields [DecidableEq K] (world : World K D V ViewData Site Rest)
    (entry : EntryData K V Site) :
    (receiveWorld world entry).receiving.receipts.cell world.receiving.receipts.size =
      some ⟨world.control.current, entry.carrier.view, entry.slot, some entry.formal⟩ ∧
    (receiveWorld world entry).receiving.views = world.receiving.views ∧
    (receiveWorld world entry).cells = world.cells ∧
    (receiveWorld world entry).environments = world.environments ∧
    (receiveWorld world entry).control = world.control :=
  ⟨receipt_new _ _ _ _ _, rfl, rfl, rfl, rfl⟩

inductive InvocationState (carrier : Carrier K D V ViewData Site Rest) where
  | before (world : World K D V ViewData Site Rest)
  | active (world : World K D V ViewData Site Rest)
  | received (world : World K D V ViewData Site Rest)
  | running (current : State carrier)

/-- The raw Force-start graph is independent of output typing. All starts
are included, after the same actual source entry and receipt. -/
inductive InvocationMove [DecidableEq K] [DecidableEq V]
    (carrier : Carrier K D V ViewData Site Rest) (entry : EntryData K V Site)
    (plan : BodyPlan K Site)
    (start : World K D V ViewData Site Rest → carrier.State → Prop) :
    InvocationState carrier → InvocationState carrier → Prop where
  | begin (world) : InvocationMove carrier entry plan start (.before world)
      (.active (enterWorld world entry.call entry.provider))
  | receipt (world) : InvocationMove carrier entry plan start (.active world)
      (.received (receiveWorld world entry))
  | force {world initial} : start world initial →
      InvocationMove carrier entry plan start (.received world) (.running (.forcing initial))
  | running {first next} : Move carrier plan first next →
      InvocationMove carrier entry plan start (.running first) (.running next)

def InvocationWitness [DecidableEq K] [DecidableEq V]
    (carrier : Carrier K D V ViewData Site Rest) (entry : EntryData K V Site)
    (plan : BodyPlan K Site)
    (start : World K D V ViewData Site Rest → carrier.State → Prop)
    (initialWorld : World K D V ViewData Site Rest) : InvocationState carrier → Prop
  | .before world => world = initialWorld
  | .active world => world = enterWorld initialWorld entry.call entry.provider
  | .received world => world = receiveWorld (enterWorld initialWorld entry.call entry.provider) entry
  | .running current => ∃ initial,
      start (receiveWorld (enterWorld initialWorld entry.call entry.provider) entry) initial ∧
      ConstructorPrefix carrier plan initial current

theorem invocation_witness_step [DecidableEq K] [DecidableEq V]
    {carrier : Carrier K D V ViewData Site Rest} {entry : EntryData K V Site}
    {plan : BodyPlan K Site} {start : World K D V ViewData Site Rest → carrier.State → Prop}
    {initialWorld : World K D V ViewData Site Rest} {first next : InvocationState carrier}
    (prior : InvocationWitness carrier entry plan start initialWorld first)
    (step : InvocationMove carrier entry plan start first next) :
    InvocationWitness carrier entry plan start initialWorld next := by
  cases step with
  | begin world => change world = initialWorld at prior; subst world; rfl
  | receipt world => change world = _ at prior; subst world; rfl
  | force started =>
      change _ = _ at prior
      subst_vars
      exact ⟨_, started, 0, .refl _⟩
  | running move =>
      obtain ⟨initial, started, history⟩ := prior
      exact ⟨initial, started, constructor_prefix_step history move⟩

/-- Complete selected source entry/prefix reconstruction, including zero
steps, before receipt, after receipt, and all arbitrary carrier developments. -/
theorem invocation_every_prefix [DecidableEq K] [DecidableEq V]
    {carrier : Carrier K D V ViewData Site Rest} {entry : EntryData K V Site}
    {plan : BodyPlan K Site} {start : World K D V ViewData Site Rest → carrier.State → Prop}
    {initialWorld : World K D V ViewData Site Rest} {count : Nat} {last : InvocationState carrier}
    (history : Prefix (InvocationMove carrier entry plan start) count (.before initialWorld) last) :
    InvocationWitness carrier entry plan start initialWorld last := by
  have preserve : ∀ {first next : InvocationState carrier} {length : Nat},
      Prefix (InvocationMove carrier entry plan start) length first next →
      InvocationWitness carrier entry plan start initialWorld first →
      InvocationWitness carrier entry plan start initialWorld next := by
    intro first next length steps
    induction steps with
    | refl => exact fun prior => prior
    | snoc prior move ih => exact fun valid => invocation_witness_step (ih valid) move
  exact preserve history rfl

/-- After Force starts, no source execution step can return to the receipt
phase. This is a property of the actual constructed transition relation. -/
theorem running_stays_running [DecidableEq K] [DecidableEq V]
    {carrier : Carrier K D V ViewData Site Rest} {entry : EntryData K V Site}
    {plan : BodyPlan K Site} {start : World K D V ViewData Site Rest → carrier.State → Prop}
    {first : State carrier} {next : InvocationState carrier}
    (step : InvocationMove carrier entry plan start (.running first) next) :
    ∃ current, next = .running current := by cases step; exact ⟨_, rfl⟩

/-! ## Canonical positive observation construction

This compiler reads the actual source phase. It retains the original
independent observation guards and *all* residual positive fields from the
selected presentation. Its recursive fields are explicit original queries,
including the current world and every actual remaining source transition.
It is not assumed equal to a separately fixed opaque `checkedObservation`.
-/

inductive Phase where
  | force | returnedArgument | rebound | oppositeName | invocationReturn
  deriving DecidableEq, Repr

def phase {carrier : Carrier K D V ViewData Site Rest} : State carrier → Phase
  | .forcing _ => .force
  | .suffix _ (.entry _ _) => .returnedArgument
  | .suffix _ (.body _ _) => .rebound
  | .suffix _ (.returning _ _) => .oppositeName
  | .suffix _ (.done _ _) => .invocationReturn

section ObservationConstruction
variable {s : Sorts} {K D V ViewData Site Rest : Type}
variable {carrier : Carrier K D V ViewData Site Rest}

/-- Readouts contain raw projections and registered interface coordinates,
never a validity, execution-classification, or whole typing field. Logical
checking descriptors are supplied to `interface` outside the raw state. -/
structure ObservationReadout (s : Sorts) (carrier : Carrier K D V ViewData Site Rest) where
  event : World K D V ViewData Site Rest → Event s
  force : carrier.State → TraceRow s
  raw : State carrier → s.Observation
  interface : Phase → s.Descriptor → s.Interface
  value : Received V → s.Value
  root : Received V → s.Root

def ObservationReadout.current (readout : ObservationReadout s carrier) : State carrier → Event s
  | .forcing current => (readout.force current).event
  | .suffix _ (.entry world _) | .suffix _ (.body world _)
  | .suffix _ (.returning world _) | .suffix _ (.done world _) => readout.event world

def ObservationReadout.row (readout : ObservationReadout s carrier)
    (descriptor : s.Descriptor) (current : State carrier) : TraceRow s :=
  ⟨readout.interface (phase current) descriptor, readout.raw current, readout.current current⟩

def ObservationReadout.result (readout : ObservationReadout s carrier)
    (descriptor : s.Descriptor) : State carrier → Option (ValueRow s)
  | .suffix _ (.returning world value) | .suffix _ (.done world value) =>
      some ⟨descriptor, readout.value value, readout.root value, readout.event world⟩
  | _ => none

def resultFields (result : Option (ValueRow s)) : Positive s :=
  match result with
  | none => .guard True
  | some row => .field (.value row)

def forceFields (readout : ObservationReadout s carrier) : State carrier → Positive s
  | .forcing current => .field (.trace (readout.force current))
  | .suffix _ _ => .guard True

/-- Every raw continuation target is retained at its actual new current
world. The domain is the unchanged raw transition graph, before any candidate
family. Raw response data and operation/handle ownership stay in that graph. -/
def nextFields [DecidableEq K] [DecidableEq V]
    (readout : ObservationReadout s carrier) (plan : BodyPlan K Site)
    (descriptor : s.Descriptor) (current : State carrier) : Positive s :=
  .all {next : State carrier // Move carrier plan current next}
    (fun next => .field (.trace (readout.row descriptor next.val)))

def canonicalObservation [DecidableEq K] [DecidableEq V]
    (inputs : Inputs s) (readout : ObservationReadout s carrier) (plan : BodyPlan K Site)
    (descriptor : s.Descriptor) (current : State carrier) : Positive s :=
  let row := readout.row descriptor current
  .both (.guard (inputs.eventCoherent row.event ∧ (inputs.observationGuards row).Valid))
    (.both (.field (.world row.event))
      (.both (resultFields (readout.result descriptor current))
        (.both (forceFields readout current)
          (.both (inputs.observationFields row) (nextFields readout plan descriptor current)))))

theorem canonical_observation_iff [DecidableEq K] [DecidableEq V]
    (inputs : Inputs s) (readout : ObservationReadout s carrier) (plan : BodyPlan K Site)
    (descriptor : s.Descriptor) (current : State carrier) (candidate : Family s) :
    (canonicalObservation inputs readout plan descriptor current).Holds candidate ↔
      (inputs.eventCoherent (readout.current current) ∧
        (inputs.observationGuards (readout.row descriptor current)).Valid) ∧
      candidate (.world (readout.current current)) ∧
      (resultFields (readout.result descriptor current)).Holds candidate ∧
      (forceFields readout current).Holds candidate ∧
      (inputs.observationFields (readout.row descriptor current)).Holds candidate ∧
      ∀ next : {next : State carrier // Move carrier plan current next},
        candidate (.trace (readout.row descriptor next.val)) := Iff.rfl

/-- Full original residual fields are retained literally, not replaced by
an effect support or a guard that tests membership. -/
theorem canonical_retains_original_fields [DecidableEq K] [DecidableEq V]
    {inputs : Inputs s} {readout : ObservationReadout s carrier} {plan : BodyPlan K Site}
    {descriptor : s.Descriptor} {current : State carrier} {candidate : Family s}
    (valid : (canonicalObservation inputs readout plan descriptor current).Holds candidate) :
    (inputs.observationFields (readout.row descriptor current)).Holds candidate :=
  valid.2.2.2.2.1

theorem canonical_every_continuation [DecidableEq K] [DecidableEq V]
    {inputs : Inputs s} {readout : ObservationReadout s carrier} {plan : BodyPlan K Site}
    {descriptor : s.Descriptor} {current next : State carrier} {candidate : Family s}
    (valid : (canonicalObservation inputs readout plan descriptor current).Holds candidate)
    (move : Move carrier plan current next) :
    candidate (.trace (readout.row descriptor next)) := valid.2.2.2.2.2 ⟨next, move⟩

theorem canonical_return_uses_checked_descriptor [DecidableEq K] [DecidableEq V]
    {inputs : Inputs s} {readout : ObservationReadout s carrier} {plan : BodyPlan K Site}
    {descriptor : s.Descriptor} {actual : Suffix K Site}
    {world : World K D V ViewData Site Rest} {value : Received V} {candidate : Family s}
    (valid : (canonicalObservation inputs readout plan descriptor
      (.suffix actual (.done world value))).Holds candidate) :
    candidate (.value ⟨descriptor, readout.value value, readout.root value, readout.event world⟩) :=
  valid.2.2.1

/-- Raw state, value/root and current event are fixed while result
descriptions vary. Their recursive result requirements remain distinguishable. -/
theorem return_descriptors_distinguished (event : Event s) (value : s.Value) (root : s.Root)
    (first second : s.Descriptor) (different : first ≠ second) :
    ∃ candidate : Family s,
      candidate (.world event) ∧
      candidate (.value ⟨first, value, root, event⟩) ∧
      ¬ candidate (.value ⟨second, value, root, event⟩) := by
  refine ⟨fun query => query = .world event ∨ query = .value ⟨first, value, root, event⟩,
    .inl rfl, .inr rfl, ?_⟩
  intro member
  rcases member with impossible | same
  · cases impossible
  · have rows := Query.value.inj same
    exact different (congrArg ValueRow.descriptor rows).symm

/-- The independent whole-carrier certificate is unfolded in the selected
declared-hole interpretation. No world/trace hole or own-world validity is
assumed, and no actual Force prefix is discarded. -/
theorem background_force_prefix (inputs : Inputs s) (holes : ValueRow s → Prop)
    (carrier : CarrierRow s) (valid : Background inputs holes (.carrier carrier))
    (event : Event s) (demanded : inputs.demand carrier event)
    (observation : RawObservation s) (executed : inputs.force carrier.input event observation) :
    inputs.forceIncidence carrier event observation ∧
    Background inputs holes (.trace (observation.atInterface carrier.interface)) ∧
    Background inputs holes (.world observation.event) := by
  have opened := greatest_unfold (RelativePhi inputs holes) (relative_monotone inputs holes)
    (.carrier carrier) valid
  rcases opened with ordinary | impossible
  · have forced := (ordinary.2.2.2.2.1 event demanded).2 observation executed
    have trace := greatest_unfold (RelativePhi inputs holes) (relative_monotone inputs holes)
      (.trace (observation.atInterface carrier.interface)) forced.2
    rcases trace with traced | impossible
    · exact ⟨forced.1, forced.2, traced.2.2.1⟩
    · cases impossible
  · cases impossible

end ObservationConstruction

/-- Construct the complete finite suffix path; successful execution is a
conclusion of the raw capture/view/delimiter equations. -/
theorem opposite_suffix_executes [DecidableEq K] [DecidableEq V]
    (world : World K D V ViewData Site Rest) (suffix : Suffix K Site)
    (returned opposite : Received V) (node : Node K D)
    (found : nodeAt world.environments suffix.capturedEnvironment = some node)
    (distinct : suffix.formal ≠ suffix.opposite)
    (cell : Nat) (within : cell < world.cells.size)
    (captured : lookupKey suffix.opposite world.environments suffix.capturedEnvironment = some cell)
    (stored : world.cells.cell cell = some opposite)
    (matching : Matches world.receiving opposite)
    (rest : List Nat) (invocation : Invocation Site)
    (current : world.control.current = .invocation suffix.owner)
    (stack : world.control.active = suffix.owner :: rest)
    (registered : world.control.invocations.cell suffix.owner = some invocation)
    (live : invocation.active = true) :
    ∃ final, Prefix (fun first next => suffixStep suffix first = some next) 3
      (.entry world returned) (.done final (opposite.atName suffix.dispatch).asValue) ∧
      final.receiving.receipts.cell world.receiving.receipts.size =
        some ⟨.invocation suffix.owner, opposite.view, suffix.nameSite, none⟩ ∧
      final.cells.cell world.cells.size = some returned.asValue ∧
      final.cells.cell cell = some opposite := by
  have actions := opposite_suffix world suffix returned opposite node found distinct cell within
    captured stored matching rest invocation current stack registered live
  dsimp only at actions
  let bound := bindValue world suffix.capturedEnvironment suffix.formal returned node found
  let read := {bound with receiving :=
    world.receiving.record (.invocation suffix.owner) opposite.view suffix.nameSite none}
  let final := {read with control :=
    ⟨deactivate world.control.invocations suffix.owner invocation, rest, suffix.previous⟩}
  have bindStep : suffixStep suffix (.entry world returned) =
      some (.body bound world.environments.size) := by
    simp only [suffixStep]
    split
    · rename_i absent
      cases absent.symm.trans found
    · rename_i other present
      have same : other = node := Option.some.inj (present.symm.trans found)
      subst other
      rfl
  have nameStep : suffixStep suffix (.body bound world.environments.size) =
      some (.returning read (opposite.atName suffix.dispatch)) := by
    dsimp only [bound, read]
    simp only [suffixStep, actions.1, Option.map_some]
  have returnStep : suffixStep suffix (.returning read (opposite.atName suffix.dispatch)) =
      some (.done final (opposite.atName suffix.dispatch).asValue) := by
    dsimp only [final, read, bound]
    simp only [suffixStep, actions.2.1, Option.map_some]
  exact ⟨final, .snoc (.snoc (.snoc (.refl _) bindStep) nameStep) returnStep,
    actions.2.2.1, actions.2.2.2.2.1, actions.2.2.2.2.2.1⟩

def SourcePair.actualSuffix (pair : SourcePair) (heap : Heap D ViewData Rest)
    (side : Side) (dispatch : Option Nat) : Suffix Nat Nat :=
  ⟨heap.world.environments.size + 1, pair.formalName side, pair.name side.other,
    pair.nameSite side, dispatch, heap.world.control.invocations.size, heap.world.control.current⟩

theorem actual_suffix_plan (pair : SourcePair) (heap : Heap D ViewData Rest)
    (side : Side) (dispatch : Option Nat) :
    (pair.actualSuffix heap side dispatch).plan =
      pair.plan (heap.world.environments.size + 1) side := rfl

theorem installed_final_node (heap : Heap D ViewData Rest) (pair : SourcePair)
    (parent : Nat) (node : Node Nat D)
    (found : nodeAt heap.world.environments parent = some node)
    (metadata : Side → ViewData) :
    nodeAt (heap.install pair parent node found metadata).world.environments
      (heap.world.environments.size + 1) =
      some ⟨heap.world.environments.size,
        some (pair.name .second, heap.world.cells.size + 1), node.dispatch⟩ := by
  simp [Heap.install, nodeAt, Arena.size]

/-- Original selected pair application. Source registration constructs both
captures, the actual receiver constructs the delimiter, and the actual
parameter-return packet can contain *any* value. The native suffix returns
the opposite installed closure, not that argument. This is the entry-current
case; arbitrary later-world interpretation is not smuggled into this theorem. -/
theorem selected_pair_suffix (heap : Heap D ViewData Rest) (pair : SourcePair)
    (hygiene : pair.Hygienic) (parent : Nat) (node : Node Nat D)
    (found : nodeAt heap.world.environments parent = some node)
    (metadata : Side → ViewData) (side : Side) (call : Nat)
    (returned : Received Nat) (dispatch : Option Nat) :
    let installed := heap.install pair parent node found metadata
    let entered := enterWorld installed.world call (pair.lambda side)
    let actual := pair.actualSuffix heap side dispatch
    ∃ final, Prefix (fun first next => suffixStep actual first = some next) 3
      (.entry entered returned)
      (.done final ((heap.packet side.other).atName dispatch).asValue) ∧
      final.receiving.receipts.cell heap.world.receiving.receipts.size =
        some ⟨.invocation heap.world.control.invocations.size,
          (heap.packet side.other).view, pair.nameSite side, none⟩ ∧
      final.cells.cell (heap.world.cells.size + 2) = some returned.asValue ∧
      final.cells.cell (heap.world.cells.size + side.other.offset) = some (heap.packet side.other) := by
  dsimp only
  apply opposite_suffix_executes
    (enterWorld (heap.install pair parent node found metadata).world call (pair.lambda side))
    (pair.actualSuffix heap side dispatch) returned (heap.packet side.other)
    ⟨heap.world.environments.size,
      some (pair.name .second, heap.world.cells.size + 1), node.dispatch⟩
  · exact installed_final_node heap pair parent node found metadata
  · exact hygiene.opposite side
  · cases side <;> simp [enterWorld, Heap.install, Store.push, Side.other, Side.offset] <;> omega
  · exact installed_lookup heap pair parent node found metadata hygiene.members side.other
  · exact installed_packet heap pair parent node found metadata side.other
  · exact installed_view heap pair parent node found metadata side.other
  · rfl
  · rfl
  · exact enter_registered _ _ _
  · rfl

/-! ## Complete canonical world readout

These records retain raw registry equalities, not recursive certificates.
All actual installed entries are read, including entries beyond `count`;
`count` bounds capture addresses only. The independent immediate guards and
the complete original event tuple remain separate from V/Car membership.
-/

section Worlds
variable {s : Sorts}

structure AliasData (bindings : Nat → Option (Installed s)) (count : Nat) where
  left : Nat
  right : Nat
  leftBound : left < count
  rightBound : right < count
  object : Installed s
  leftObject : bindings left = some object
  rightObject : bindings right = some object

structure CaptureData (bindings : Nat → Option (Installed s)) (count : Nat) where
  address : Nat
  within : address < count
  object : Installed s
  found : bindings address = some object

structure WorldRegistry (s : Sorts) where
  guards : WorldGuards
  count : Nat
  bindings : Nat → Option (Installed s)
  aliases : List (AliasData bindings count)
  captures : s.Provider → Nat → Option (CaptureData bindings count)
  witnessReference : s.WitnessPosition → Nat
  witnessValue : Nat → s.WitnessValue

/-- A constructed missing-native world interpretation. All nonworld fields
of the selected operator, including independent domains, remain unchanged.
No claim of equality with separately fixed old world readouts is made. -/
def worldInputs (base : Inputs s) (registry : Event s → WorldRegistry s) : Inputs s :=
  {base with
    worldGuards := fun event => (registry event).guards
    installedCount := fun event => (registry event).count
    installed := fun event => (registry event).bindings
    alias := fun event left right => ∃ link ∈ (registry event).aliases,
      link.left = left ∧ link.right = right
    capture := fun event provider name => ((registry event).captures provider name).map CaptureData.address
    captureValue := fun event provider name => ((registry event).captures provider name).map CaptureData.object
    sharedPosition := fun event first second =>
      (registry event).witnessReference first = (registry event).witnessReference second
    witnessAt := fun event position =>
      (registry event).witnessValue ((registry event).witnessReference position)}

theorem world_aliases_from_data (base : Inputs s) (registry : Event s → WorldRegistry s)
    (event : Event s) : AliasesAgree (worldInputs base registry) event := by
  rintro first second ⟨link, _, rfl, rfl⟩
  exact ⟨link.object, link.leftObject, link.rightObject⟩

theorem world_captures_from_data (base : Inputs s) (registry : Event s → WorldRegistry s)
    (event : Event s) : CapturesAgree (worldInputs base registry) event := by
  intro provider name address found
  change ((registry event).captures provider name).map CaptureData.address = some address at found
  cases present : (registry event).captures provider name with
  | none => simp [present] at found
  | some captured =>
      simp only [present, Option.map_some, Option.some.injEq] at found
      subst address
      exact ⟨captured.within, captured.object, captured.found, by
        change ((registry event).captures provider name).map CaptureData.object = _
        rw [present]
        rfl⟩

theorem world_witnesses_from_data (base : Inputs s) (registry : Event s → WorldRegistry s)
    (event : Event s) : WitnessesAgree (worldInputs base registry) event := by
  intro first second shared
  exact congrArg (registry event).witnessValue shared

/-- Full PhiW: recursive installed certificates remain explicit, while all
alias/capture/shared-position equations are derived from the actual registry
data. This is not AllInstalled renamed as world validity. -/
theorem canonical_world (base : Inputs s) (registry : Event s → WorldRegistry s)
    (candidate : Family s) (event : Event s)
    (coherent : base.eventCoherent event) (guards : (registry event).guards.Valid)
    (bindings : ∀ index object, (registry event).bindings index = some object →
      object.Valid candidate event) :
    PhiW (worldInputs base registry) candidate event :=
  ⟨coherent, guards, world_aliases_from_data base registry event,
    world_captures_from_data base registry event, world_witnesses_from_data base registry event,
    bindings⟩

/-- Actual fresh-cell update. No bounded scan is used to interpret installed
entries; every old Some outside the fresh address remains present. -/
def extendBindings (bindings : Nat → Option (Installed s)) (fresh : Nat) (object : Installed s) :
    Nat → Option (Installed s) :=
  fun index => if index = fresh then some object else bindings index

theorem extend_bindings_new (bindings : Nat → Option (Installed s)) (fresh : Nat) (object : Installed s) :
    extendBindings bindings fresh object fresh = some object := by simp [extendBindings]

theorem extend_bindings_old {bindings : Nat → Option (Installed s)} {fresh index : Nat}
    {object previous : Installed s} (empty : bindings fresh = none)
    (present : bindings index = some previous) :
    extendBindings bindings fresh object index = some previous := by
  by_cases same : index = fresh
  · subst index
    rw [empty] at present
    cases present
  · simp only [extendBindings, ite_eq_right same, present]

def AliasData.extend {bindings : Nat → Option (Installed s)} {count : Nat}
    (link : AliasData bindings count) (object : Installed s) :
    AliasData (extendBindings bindings count object) (count + 1) :=
  ⟨link.left, link.right, Nat.lt_succ_of_lt link.leftBound, Nat.lt_succ_of_lt link.rightBound,
    link.object,
    by simpa only [extendBindings, ite_eq_right (Nat.ne_of_lt link.leftBound)] using link.leftObject,
    by simpa only [extendBindings, ite_eq_right (Nat.ne_of_lt link.rightBound)] using link.rightObject⟩

def CaptureData.extend {bindings : Nat → Option (Installed s)} {count : Nat}
    (captured : CaptureData bindings count) (object : Installed s) :
    CaptureData (extendBindings bindings count object) (count + 1) :=
  ⟨captured.address, Nat.lt_succ_of_lt captured.within, captured.object,
    by simpa only [extendBindings, ite_eq_right (Nat.ne_of_lt captured.within)] using captured.found⟩

/-- Actual parameter binding preserves existing capture/alias provenance.
New raw alias/capture declarations, when present, are separate original
constructor outputs; this operation does not invent them. -/
def WorldRegistry.rebind (registry : WorldRegistry s) (object : Installed s)
    (guards : WorldGuards) : WorldRegistry s :=
  {guards, count := registry.count + 1
   bindings := extendBindings registry.bindings registry.count object
   aliases := registry.aliases.map (fun link => link.extend object)
   captures := fun provider name => (registry.captures provider name).map (fun captured => captured.extend object)
   witnessReference := registry.witnessReference, witnessValue := registry.witnessValue}

theorem rebind_preserves_every_old {registry : WorldRegistry s} {object previous : Installed s}
    (guards : WorldGuards) (empty : registry.bindings registry.count = none)
    (index : Nat) (present : registry.bindings index = some previous) :
    (registry.rebind object guards).bindings index = some previous :=
  extend_bindings_old empty present

/-- Construct all recursive fields of a real parameter-result extension from
the old complete binding fields and this actual returned value/carrier.
This lemma quantifies every Some entry, with no count qualification. -/
theorem rebind_binding_fields (registry : WorldRegistry s) (object : Installed s)
    (guards : WorldGuards) (candidate : Family s) (event : Event s)
    (old : ∀ index previous, registry.bindings index = some previous → previous.Valid candidate event)
    (returned : object.Valid candidate event) :
    ∀ index current, (registry.rebind object guards).bindings index = some current →
      current.Valid candidate event := by
  intro index current present
  change (if index = registry.count then some object else registry.bindings index) = some current at present
  split at present
  · cases Option.some.inj present
    exact returned
  · exact old index current present

/-- Direct application to the original PhiW operator at the actual post-Force
event. The data equation is the exact registry-readout seam; it contains no
typing, completed-world or safety proposition. -/
theorem rebind_world (base : Inputs s) (registry : Event s → WorldRegistry s)
    (event : Event s) (before : WorldRegistry s) (object : Installed s) (guards : WorldGuards)
    (actualReadout : registry event = before.rebind object guards)
    (candidate : Family s) (coherent : base.eventCoherent event) (validGuards : guards.Valid)
    (old : ∀ index previous, before.bindings index = some previous → previous.Valid candidate event)
    (returned : object.Valid candidate event) :
    PhiW (worldInputs base registry) candidate event := by
  apply canonical_world base registry candidate event coherent
  · simpa only [actualReadout, WorldRegistry.rebind] using validGuards
  · rw [actualReadout]
    exact rebind_binding_fields before object guards candidate event old returned

structure PairAssignment (s : Sorts) where
  descriptor : Side → s.Descriptor
  value : Side → s.Value
  root : Side → s.Root

def PairAssignment.fromHeap (heap : Heap D ViewData Rest)
    (descriptors : Side → s.Descriptor) (values : Nat → s.Value) (roots : Nat → s.Root) :
    PairAssignment s :=
  ⟨descriptors, fun side => values (heap.packet side).value,
    fun side => roots (heap.packet side).value⟩

def PairAssignment.row (assignment : PairAssignment s) (side : Side) (event : Event s) : ValueRow s :=
  ⟨assignment.descriptor side, assignment.value side, assignment.root side, event⟩

def PairAssignment.object (assignment : PairAssignment s) (side : Side) : Installed s :=
  .value (assignment.descriptor side) (assignment.value side) (assignment.root side)

/-- Exact two value holes at their independently registered original event
positions. No world/carrier/continuation/guard hole is introduced. -/
def PairAssignment.holes (assignment : PairAssignment s)
    (registered : Side → Event s → Prop) (row : ValueRow s) : Prop :=
  ∃ side, registered side row.event ∧ row = assignment.row side row.event

theorem exact_pair_holes (assignment : PairAssignment s) (registered : Side → Event s → Prop)
    (row : ValueRow s) (hole : assignment.holes registered row) :
    (registered .first row.event ∧ row = assignment.row .first row.event) ∨
    (registered .second row.event ∧ row = assignment.row .second row.event) := by
  obtain ⟨side, licensed, same⟩ := hole
  cases side
  · exact .inl ⟨licensed, same⟩
  · exact .inr ⟨licensed, same⟩

def WorldRegistry.twoBindings (before : WorldRegistry s) (assignment : PairAssignment s)
    (guards : WorldGuards) : WorldRegistry s :=
  (before.rebind (assignment.object .first) guards).rebind (assignment.object .second) guards

/-- Full captured lexical environment: both newly installed members plus
every old lexical capture. The source `g` binding is the last extension,
matching the actual two-node native environment constructor. -/
def WorldRegistry.pairEnvironment (before : WorldRegistry s) (assignment : PairAssignment s)
    (guards : WorldGuards) (pair : SourcePair)
    (parent : Nat → Option (CaptureData before.bindings before.count)) :
    Nat → Option (CaptureData (before.twoBindings assignment guards).bindings
      (before.twoBindings assignment guards).count) := fun name =>
  if name = pair.name .second then
    some ⟨before.count + 1, by simp [WorldRegistry.twoBindings, WorldRegistry.rebind],
      assignment.object .second, by simp [WorldRegistry.twoBindings, WorldRegistry.rebind, extendBindings]⟩
  else if name = pair.name .first then
    some ⟨before.count, by simp [WorldRegistry.twoBindings, WorldRegistry.rebind]; omega,
      assignment.object .first, by simp [WorldRegistry.twoBindings, WorldRegistry.rebind, extendBindings]⟩
  else (parent name).map (fun captured =>
    (captured.extend (assignment.object .first)).extend (assignment.object .second))

/-- Fresh original providers both retain the entire original captured
environment. Other provider captures are copied without selecting an
alternative. Raw provider freshness is checked separately at installation. -/
noncomputable def WorldRegistry.pairRegistration (before : WorldRegistry s)
    (assignment : PairAssignment s) (guards : WorldGuards) (pair : SourcePair)
    (providers : Side → s.Provider)
    (parent : Nat → Option (CaptureData before.bindings before.count)) : WorldRegistry s := by
  classical
  exact {before.twoBindings assignment guards with
    captures := fun provider name =>
      if provider = providers .first ∨ provider = providers .second then
        before.pairEnvironment assignment guards pair parent name
      else (before.twoBindings assignment guards).captures provider name}

theorem pair_registration_bindings (before : WorldRegistry s) (assignment : PairAssignment s)
    (guards : WorldGuards) (pair : SourcePair) (providers : Side → s.Provider)
    (parent : Nat → Option (CaptureData before.bindings before.count)) :
    (before.pairRegistration assignment guards pair providers parent).bindings =
      (before.twoBindings assignment guards).bindings := rfl

theorem pair_registration_preserves_every_old (before : WorldRegistry s) (assignment : PairAssignment s)
    (guards : WorldGuards) (pair : SourcePair) (providers : Side → s.Provider)
    (parent : Nat → Option (CaptureData before.bindings before.count))
    (freshFirst : before.bindings before.count = none)
    (freshSecond : before.bindings (before.count + 1) = none)
    (index : Nat) (object : Installed s) (present : before.bindings index = some object) :
    (before.pairRegistration assignment guards pair providers parent).bindings index = some object := by
  have first := rebind_preserves_every_old (object := assignment.object .first) guards freshFirst index present
  apply rebind_preserves_every_old (object := assignment.object .second) guards _ index first
  simpa [WorldRegistry.rebind, extendBindings] using freshSecond

theorem pair_registration_other_provider (before : WorldRegistry s) (assignment : PairAssignment s)
    (guards : WorldGuards) (pair : SourcePair) (providers : Side → s.Provider)
    (parent : Nat → Option (CaptureData before.bindings before.count))
    (provider : s.Provider) (first : provider ≠ providers .first) (second : provider ≠ providers .second)
    (name : Nat) :
    (before.pairRegistration assignment guards pair providers parent).captures provider name =
      (before.twoBindings assignment guards).captures provider name := by
  classical
  simp [WorldRegistry.pairRegistration, first, second]

/-- The complete installed world is introduced inside B_H from the exact two
source holes and every existing background binding at this actual event.
Neither ordinary opposite membership nor a completed own-root W is a premise.
The data readout and independent immediate guards remain visibly required. -/
theorem pair_background_world (base : Inputs s) (registry : Event s → WorldRegistry s)
    (before : WorldRegistry s) (assignment : PairAssignment s) (guards : WorldGuards)
    (pair : SourcePair) (providers : Side → s.Provider)
    (parent : Nat → Option (CaptureData before.bindings before.count))
    (registered : Side → Event s → Prop) (event : Event s)
    (actualReadout : registry event = before.pairRegistration assignment guards pair providers parent)
    (coherent : base.eventCoherent event) (validGuards : guards.Valid)
    (licensed : ∀ side, registered side event)
    (old : ∀ index object, before.bindings index = some object →
      object.Valid (Background (worldInputs base registry) (assignment.holes registered)) event) :
    Background (worldInputs base registry) (assignment.holes registered) (.world event) := by
  let inputs := worldInputs base registry
  let background := Background inputs (assignment.holes registered)
  have members : ∀ side, (assignment.object side).Valid background event := by
    intro side
    exact background_value_hole inputs (assignment.holes registered) (assignment.row side event)
      ⟨side, licensed side, rfl⟩
  have fields := rebind_binding_fields
    (before.rebind (assignment.object .first) guards) (assignment.object .second) guards background event
    (rebind_binding_fields before (assignment.object .first) guards background event old (members .first))
    (members .second)
  have world : PhiW inputs background event := by
    apply canonical_world base registry background event coherent
    · simpa only [actualReadout, WorldRegistry.pairRegistration, WorldRegistry.twoBindings,
        WorldRegistry.rebind] using validGuards
    · rw [actualReadout]
      exact fields
  apply greatest_fold (RelativePhi inputs (assignment.holes registered))
    (relative_monotone inputs (assignment.holes registered))
  exact Or.inl world

/-- Actual returned parameter/result extension, in the same declared-hole
operator. The entire current old binding family and actual returned tuple
are retained; this is not a Value-only or bounded-store surrogate for W. -/
theorem returned_background_world (base : Inputs s) (registry : Event s → WorldRegistry s)
    (holes : ValueRow s → Prop) (event : Event s) (before : WorldRegistry s)
    (object : Installed s) (guards : WorldGuards)
    (actualReadout : registry event = before.rebind object guards)
    (coherent : base.eventCoherent event) (validGuards : guards.Valid)
    (old : ∀ index previous, before.bindings index = some previous →
      previous.Valid (Background (worldInputs base registry) holes) event)
    (returned : object.Valid (Background (worldInputs base registry) holes) event) :
    Background (worldInputs base registry) holes (.world event) := by
  apply greatest_fold (RelativePhi (worldInputs base registry) holes)
    (relative_monotone (worldInputs base registry) holes)
  exact Or.inl (rebind_world base registry event before object guards actualReadout
    (Background (worldInputs base registry) holes) coherent validGuards old returned)

structure FreshProviders (before : WorldRegistry s) (providers : Side → s.Provider) : Prop where
  distinct : providers .first ≠ providers .second
  absent : ∀ side name, before.captures (providers side) name = none

/-- No original capture is dropped when the provider identities are the
genuinely fresh source constructor outputs. -/
theorem pair_registration_old_capture (before : WorldRegistry s) (assignment : PairAssignment s)
    (guards : WorldGuards) (pair : SourcePair) (providers : Side → s.Provider)
    (parent : Nat → Option (CaptureData before.bindings before.count))
    (fresh : FreshProviders before providers)
    (provider : s.Provider) (name : Nat) (captured : CaptureData before.bindings before.count)
    (present : before.captures provider name = some captured) :
    (before.pairRegistration assignment guards pair providers parent).captures provider name =
      some ((captured.extend (assignment.object .first)).extend (assignment.object .second)) := by
  have first : provider ≠ providers .first := by
    intro same
    rw [same, fresh.absent .first name] at present
    cases present
  have second : provider ≠ providers .second := by
    intro same
    rw [same, fresh.absent .second name] at present
    cases present
  rw [pair_registration_other_provider before assignment guards pair providers parent provider first second name]
  simp only [WorldRegistry.twoBindings, WorldRegistry.rebind, present, Option.map_some]
  rfl

theorem world_readout_keeps_domains (base : Inputs s) (registry : Event s → WorldRegistry s)
    {row : ValueRow s} (challenge : Challenge row) :
    CheckedDomain (worldInputs base registry) challenge ↔ CheckedDomain base challenge := Iff.rfl

theorem world_readout_keeps_raw_execution (base : Inputs s) (registry : Event s → WorldRegistry s)
    (provider : s.Provider) (input : CallInput s) (observation : RawObservation s) :
    (worldInputs base registry).execute provider input observation ↔
      base.execute provider input observation := Iff.rfl

/-- Hereditary action for the exact declared holes is an independent source
scope/position action, not a typing or whole-observation premise. -/
theorem background_installed_restrict (inputs : Inputs s) (holes : ValueRow s → Prop)
    (holeFuture : ∀ row later, holes row → inputs.compatible row.event later → holes (row.atEvent later))
    (object : Installed s) (before after : Event s)
    (member : object.Valid (Background inputs holes) before)
    (later : inputs.compatible before after) :
    object.Valid (Background inputs holes) after := by
  cases object with
  | value descriptor value root =>
      have opened := greatest_unfold (RelativePhi inputs holes) (relative_monotone inputs holes)
        (.value ⟨descriptor, value, root, before⟩) member
      rcases opened with ordinary | hole
      · exact ordinary.2 after later
      · exact background_value_hole inputs holes _ (holeFuture _ after hole later)
  | carrier interface carrier root =>
      have opened := greatest_unfold (RelativePhi inputs holes) (relative_monotone inputs holes)
        (.carrier ⟨interface, carrier, root, before⟩) member
      rcases opened with ordinary | impossible
      · exact ordinary.2.2.2.2.2 after later
      · cases impossible

theorem pair_holes_future (assignment : PairAssignment s) (registered : Side → Event s → Prop)
    (inputs : Inputs s)
    (scopeAction : ∀ side before after, registered side before →
      inputs.compatible before after → registered side after)
    (row : ValueRow s) (after : Event s) (hole : assignment.holes registered row)
    (later : inputs.compatible row.event after) :
    assignment.holes registered (row.atEvent after) := by
  obtain ⟨side, licensed, same⟩ := hole
  refine ⟨side, scopeAction side row.event after licensed later, ?_⟩
  rw [same]
  rfl

/-- Apply the full independent B_H carrier clause at an arbitrary actual
Return, then construct the result-extended W at the actual later event.
The raw-to-decorated registry and Return readout equations are the precise
remaining source correspondence inputs. No new-world validity is assumed. -/
theorem world_after_actual_force_return (base : Inputs s) (registry : Event s → WorldRegistry s)
    (holes : ValueRow s → Prop)
    (holeFuture : ∀ row later, holes row → (worldInputs base registry).compatible row.event later →
      holes (row.atEvent later))
    (carrier : CarrierRow s)
    (wholeCarrier : Background (worldInputs base registry) holes (.carrier carrier))
    (demandEvent : Event s) (demanded : (worldInputs base registry).demand carrier demandEvent)
    (observation : RawObservation s)
    (executed : (worldInputs base registry).force carrier.input demandEvent observation)
    (returned : ValueRow s)
    (actualReturn : (worldInputs base registry).traceForm
      (observation.atInterface carrier.interface) = .pureReturn returned)
    (after : Event s) (later : (worldInputs base registry).compatible observation.event after)
    (guards : WorldGuards)
    (actualRegistry : registry after = (registry observation.event).rebind
      (.value returned.descriptor returned.value returned.root) guards)
    (coherent : base.eventCoherent after) (validGuards : guards.Valid) :
    Background (worldInputs base registry) holes (.world after) := by
  let inputs := worldInputs base registry
  let background := Background inputs holes
  have forced := background_force_prefix inputs holes carrier wholeCarrier demandEvent demanded observation executed
  have oldWorld := greatest_unfold (RelativePhi inputs holes) (relative_monotone inputs holes)
    (.world observation.event) forced.2.2
  have trace := greatest_unfold (RelativePhi inputs holes) (relative_monotone inputs holes)
    (.trace (observation.atInterface carrier.interface)) forced.2.1
  rcases oldWorld with oldWorld | impossible
  · rcases trace with trace | impossible
    · have returnedFields := trace.2.2.2.1
      change (match inputs.traceForm (observation.atInterface carrier.interface) with
        | .pureReturn value => value.event = observation.event ∧ background (.value value)
        | .unfinished => True) at returnedFields
      rw [actualReturn] at returnedFields
      have value : (Installed.value returned.descriptor returned.value returned.root).Valid
          background observation.event := by
        simpa only [Installed.Valid, ← returnedFields.1] using returnedFields.2
      apply returned_background_world base registry holes after (registry observation.event)
        (.value returned.descriptor returned.value returned.root) guards actualRegistry coherent validGuards
      · intro index object present
        exact background_installed_restrict inputs holes holeFuture object observation.event after
          (oldWorld.2.2.2.2.2 index object present) later
      · exact background_installed_restrict inputs holes holeFuture _ observation.event after value later
    · cases impossible
  · cases impossible

end Worlds

end YulangClosure.OriginalRecursivePair
