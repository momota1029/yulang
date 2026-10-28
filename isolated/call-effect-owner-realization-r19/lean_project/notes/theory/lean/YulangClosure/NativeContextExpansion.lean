import YulangClosure.NativeReplayCurrent

/-!
Construction-directed full Context decomposition.  The parser, inline checks,
child admission and residual placement below are executable projections of the
named native owners, not semantic subtyping definitions.  A successful result
contains every inline check and the exact consumed/unconsumed continuation.
Resource callbacks and native history readback remain explicit; neither an
admission memo nor `discharged` is treated as a completion certificate.
-/
namespace YulangClosure.NativeContextExpansion

open NativeMergeExpansion
open NativeReplayCurrent (Pair currentPair sourceContext admittedChild AdmissionTables)

inductive Expr where
  | prefix (weight input : Nat)
  | suffix (input weight : Nat)
  | swap (input : Nat)
  | both (input certificate : Nat)
  | replay (lower upper : Nat)
  | without (input : Nat)
  deriving DecidableEq, Repr

structure Weight where
  allowed : List Nat
  boundary : Nat
  owner : Nat
  position : Nat
  leftWord : List Nat := []
  rightPops : List Nat := []
  deriving DecidableEq, Repr

structure View where
  allowed : List Nat
  tail : Option Nat
  closedWeight : Option Nat
  owner : Nat
  position : Nat
  deriving DecidableEq, Repr

structure Tables where
  contexts : Nat → Option Expr
  weights : Nat → Option Weight
  views : Nat → Option View
  contributions : Nat → Option Nat
  prefixIdentity : Nat → Nat

def weightValid (t : Tables) (w : Nat) : Bool :=
  match t.weights w with
  | none => false
  | some p => match t.views p.boundary with
    | none => false
    | some v => p.leftWord.isEmpty && p.rightPops.isEmpty &&
        decide (p.owner = v.owner) && decide (p.position = v.position) &&
        decide (v.closedWeight = some w)

inductive Mode where
  | outer | replay | directed
  deriving DecidableEq, Repr

structure Scan where
  pending : List (Nat × Mode)
  visited : List (Nat × Mode) := []
  filters : List Nat := []
  residual : Nat
  replayFilters : Bool := false
  directed : Bool := false
  replayResidual : Bool := false
  deriving DecidableEq, Repr

/-- One exact native stack iteration. The ordered list is a set only where the
native operation uses `contains`; filter order remains first-discovery order. -/
def scanStep (t : Tables) (s : Scan) : Option Scan := do
  let (id, mode) :: rest := s.pending | none
  if id = 0 ∨ (id, mode) ∈ s.visited then
    return { s with pending := rest }
  let s := { s with pending := rest, visited := (id, mode) :: s.visited }
  let node ← t.contexts id
  match node with
  | .prefix w input =>
      if (mode = .outer ∨ (mode = .replay ∧ input = 0)) ∧ input < id ∧ weightValid t w then
        return { s with pending := (input, mode) :: rest
                        residual := if mode = .outer then input else s.residual
                        replayFilters := s.replayFilters || decide (mode = .replay)
                        filters := attach w s.filters }
      else none
  | .replay lower upper =>
      if lower < id ∧ upper < id then
        let childMode := if mode = .directed then Mode.directed else Mode.replay
        return { s with pending := (lower, childMode) :: (upper, childMode) :: rest
                        replayResidual := s.replayResidual || decide (mode = .outer) }
      else none
  | .swap input | .without input =>
      if input < id then
        return { s with pending := (input, .directed) :: rest, directed := true }
      else none
  | .suffix _ _ | .both _ _ => none

structure Parsed where
  filters : List Nat
  residual : Nat
  replayFilters : Bool
  directed : Bool
  replayResidual : Bool
  deriving DecidableEq, Repr

def finish (s : Scan) : Option Parsed :=
  if s.pending = [] ∧ ¬ (s.replayFilters = true ∧ s.directed = true) then
    some ⟨s.filters,
      if s.replayResidual && !s.directed then 0 else s.residual,
      s.replayFilters, s.directed, s.replayResidual⟩
  else none

/-- Fuel counts actual stack iterations; it is not a new supported-source cap.
`scan_run_computes` supplies fuel for every finite successful native transcript. -/
def scanLoop (t : Tables) : Nat → Scan → Option Parsed
  | 0, s => finish s
  | n + 1, s => if s.pending = [] then finish s
      else (scanStep t s).bind (scanLoop t n)

def parse (t : Tables) (fuel root : Nat) : Option Parsed :=
  scanLoop t fuel ⟨[(root, .outer)], [], [], root, false, false, false⟩

inductive ScanRun (t : Tables) : Scan → Parsed → Prop
  | done {s p} (result : finish s = some p) : ScanRun t s p
  | step {s u p} (pending : s.pending ≠ []) (next : scanStep t s = some u)
      (rest : ScanRun t u p) : ScanRun t s p

theorem scan_run_computes {t : Tables} {s : Scan} {p : Parsed}
    (h : ScanRun t s p) : ∃ fuel, scanLoop t fuel s = some p := by
  induction h with
  | done result => exact ⟨0, result⟩
  | step pending next rest ih =>
      obtain ⟨fuel, computed⟩ := ih
      exact ⟨fuel + 1, by simp [scanLoop, pending, next, computed]⟩

theorem finish_no_mixed {s : Scan} {p : Parsed} (h : finish s = some p) :
    ¬ (p.replayFilters = true ∧ p.directed = true) := by
  unfold finish at h
  split at h
  · rename_i allowed
    cases h
    exact allowed.2
  · cases h

theorem finish_pure_replay {s : Scan} {p : Parsed} (h : finish s = some p)
    (replay : s.replayResidual = true) (directed : s.directed = false) :
    p.residual = 0 := by
  unfold finish at h
  split at h
  · cases h
    simp [replay, directed]
  · cases h

theorem scan_computes_run {t : Tables} {s : Scan} {p : Parsed} {fuel : Nat}
    (h : scanLoop t fuel s = some p) : ScanRun t s p := by
  induction fuel generalizing s with
  | zero => exact .done h
  | succ fuel ih =>
      simp only [scanLoop] at h
      by_cases empty : s.pending = []
      · exact .done (by simpa [empty] using h)
      · simp only [empty, ↓reduceIte] at h
        cases next : scanStep t s with
        | none => simp [next] at h
        | some u =>
            exact .step empty next (ih (by simpa [next] using h))

theorem parsed_no_mixed {t : Tables} {s : Scan} {p : Parsed} {fuel : Nat}
    (h : scanLoop t fuel s = some p) : ¬ (p.replayFilters = true ∧ p.directed = true) := by
  have run := scan_computes_run h
  clear h
  induction run with
  | done finished => exact finish_no_mixed finished
  | step _ _ _ ih => exact ih

def admissionTables (t : Tables) : AdmissionTables :=
  ⟨fun view => (t.views view).bind View.closedWeight, t.prefixIdentity⟩

def effectTables (t : Tables) : Effect.Tables :=
  ⟨fun id => (t.views id).map fun v =>
    ⟨v.allowed, v.tail, v.closedWeight.bind (fun w => (t.weights w).map Weight.allowed)⟩,
    t.contributions⟩

/-- Successful child-local Context interning, including a nonzero ID and its
actual PrefixLeft(weight,Identity) node. No parent Context is substituted. -/
def sourceAvailable (t : Tables) (upper : Endpoint) : Bool :=
  match upper with
  | .allowance view => match t.views view with
    | none => false
    | some v => match v.closedWeight with
      | none => true
      | some w => decide (t.prefixIdentity w ≠ 0) &&
          decide (t.contexts (t.prefixIdentity w) = some (.prefix w 0))
  | _ => true

def relationGuard (key : Key) : Bool :=
  decide (key.transformer = 0 ∨ key.lower ≠ key.upper)

structure Availability where
  enter : Bool
  parser : Bool
  registered : Bound → Bool
  physical : Bound → Bool
  enqueue : Key → Bool
  boundOrigin : Fiber → Bool
  replay : Bound → Bool
  conflict : Pair → Bool
  publish : Bool

def admit (t : Tables) (a : Availability) (q : Nat → Nat) (parent : Key) (pair : Pair) : Option Key :=
  let child := admittedChild (admissionTables t) q parent pair
  if sourceAvailable t pair.2 && relationGuard child && a.enqueue child then some child else none

theorem admit_payload {t : Tables} {a : Availability} {q : Nat → Nat}
    {parent child : Key} {pair : Pair} (h : admit t a q parent pair = some child) :
    child = admittedChild (admissionTables t) q parent pair ∧
    child.context = sourceContext (admissionTables t) pair.2 ∧
    child.sources = parent.sources ∧ child.transformer = parent.transformer ∧
    (child.transformer = 0 ∨ child.lower ≠ child.upper) ∧ a.enqueue child = true := by
  simp only [admit] at h
  split at h
  · rename_i valid
    cases h
    have v := Bool.and_eq_true_iff.mp valid
    have guard := Bool.and_eq_true_iff.mp v.1
    exact ⟨rfl, rfl, rfl, rfl, of_decide_eq_true guard.2, v.2⟩
  · cases h

theorem nonzero_self_child_rejected (t : Tables) (a : Availability) (q : Nat → Nat)
    (parent : Key) (pair : Pair) (nonzero : parent.transformer ≠ 0)
    (same : renameEndpoint q pair.1 = renameEndpoint q pair.2) :
    admit t a q parent pair = none := by
  simp [admit, relationGuard, admittedChild, nonzero, same]

def collect {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | x :: xs => do
      let y ← f x
      let ys ← collect f xs
      pure (y :: ys)

inductive Aligned {α β : Type} (r : α → β → Prop) : List α → List β → Prop
  | nil : Aligned r [] []
  | cons {x y xs ys} : r x y → Aligned r xs ys → Aligned r (x :: xs) (y :: ys)

theorem collect_exact {α β : Type} (f : α → Option β) {xs : List α} {ys : List β}
    (h : collect f xs = some ys) :
    Aligned (fun x y => f x = some y) xs ys := by
  induction xs generalizing ys with
  | nil => simp [collect] at h; subst ys; exact .nil
  | cons x xs ih =>
      cases head : f x with
      | none => simp [collect, head] at h
      | some y =>
          cases tail : collect f xs with
          | none => simp [collect, head, tail] at h
          | some rest =>
              simp [collect, head, tail] at h
              subst ys
              exact .cons head (ih tail)

inductive Leaf where
  | localReturn
  | children (keys : List Key)
  | bound (fiber : Fiber)
  | conflict (pair : Pair)
  deriving DecidableEq, Repr

def Leaf.childKeys : Leaf → List Key
  | .children keys => keys
  | _ => []

def Leaf.fibers : Leaf → List Fiber
  | .bound fiber => [fiber]
  | _ => []

def Leaf.transport (q : Nat → Nat) (post : Key → Nat) : Leaf → Leaf
  | .bound fiber => .bound (carrier q post fiber)
  | .conflict pair => .conflict (Effect.renamePair q pair)
  | leaf => leaf

/-- Both row/row level branches, rigid-lower/row-upper, row-lower/rigid-upper.
The equality branch is handled before this function by `applyEffect`. -/
def placedBound (levels : Nat → Nat) : Endpoint → Endpoint → Option Bound
  | .row lower, .row upper =>
      if levels upper ≤ levels lower then some ⟨lower, .negative, .row upper⟩
      else some ⟨upper, .positive, .row lower⟩
  | lower, .row upper => some ⟨upper, .positive, lower⟩
  | .row lower, upper => some ⟨lower, .negative, upper⟩
  | _, _ => none

theorem placed_bound_pair {levels : Nat → Nat} {lower upper : Endpoint} {bound : Bound}
    (h : placedBound levels lower upper = some bound) : bound.pair = (lower, upper) := by
  cases lower <;> cases upper <;> simp only [placedBound] at h
  all_goals first
    | (split at h <;> cases h <;> rfl)
    | (cases h; rfl)
    | cases h

def operandAvailable (t : Tables) (lower upper : Endpoint) : Bool :=
  match lower, upper with
  | .contribution _, .allowance view | .annotationMember _ _, .allowance view => match t.views view with
    | none => false
    | some v => match v.closedWeight with
      | none => true
      | some weight => (t.weights weight).isSome
  | _, _ => true

/-- Inline callback, with the ORIGINAL processing parent retained for every
child. `context` is zero for an installed checked boundary, post-check otherwise.
The bound-origin and replay callbacks must both return successfully. -/
def applyEffect (t : Tables) (a : Availability) (levels q : Nat → Nat)
    (parent : Key) (context : Nat) (pair : Pair) : Option Leaf :=
  if pair.1 = pair.2 then some .localReturn
  else match placedBound levels pair.1 pair.2 with
    | some bound =>
        let fiber := exactFiber bound context parent.sources parent.transformer
        if relationGuard fiber.key && a.boundOrigin fiber && a.physical bound && a.replay bound
          then some (.bound fiber) else none
    | none =>
        if operandAvailable t pair.1 pair.2 then
          match Effect.checkOperand q (effectTables t) pair.1 pair.2 with
          | .localReturn => some .localReturn
          | .children pairs => (collect (admit t a q parent) pairs).map Leaf.children
          | .conflict lower upper =>
              if a.conflict (lower, upper) then some (.conflict (lower, upper)) else none
          | .unavailable => none
        else none

structure Check where
  weight : Nat
  view : Nat
  registered : Bool
  leaf : Leaf
  deriving DecidableEq, Repr

def filterRegistered (a : Availability) (q : Nat → Nat) (parent : Key) (view : Nat) : Bool :=
  match (currentPair q parent).1 with
  | .row owner => a.registered ⟨owner, .negative, .allowance view⟩
  | _ => false

/-- The already-registered branch calls origin attachment and Replay without
repeating physical insertion. The new-bound branch also requires insertion. -/
def applyFilter (t : Tables) (a : Availability) (levels q : Nat → Nat)
    (parent : Key) (view : Nat) : Option Leaf :=
  match (currentPair q parent).1 with
  | .row owner =>
      let fiber := allowanceFiber owner view parent.sources parent.transformer
      if a.registered fiber.bound then
        if relationGuard fiber.key && a.boundOrigin fiber && a.replay fiber.bound
          then some (.bound fiber) else none
      else applyEffect t a levels q parent 0 ((currentPair q parent).1, .allowance view)
  | _ => applyEffect t a levels q parent 0 ((currentPair q parent).1, .allowance view)

theorem registered_filter_constructed (t : Tables) (a : Availability) (levels q : Nat → Nat)
    (parent : Key) (owner view : Nat) (lower : (currentPair q parent).1 = .row owner)
    (registered : a.registered ⟨owner, .negative, .allowance view⟩ = true)
    (origin : a.boundOrigin (allowanceFiber owner view parent.sources parent.transformer) = true)
    (replay : a.replay ⟨owner, .negative, .allowance view⟩ = true) :
    applyFilter t a levels q parent view =
      some (.bound (allowanceFiber owner view parent.sources parent.transformer)) := by
  simp [applyFilter, lower, allowanceFiber, exactFiber, Bound.pair, relationGuard,
    registered, replay] at origin ⊢
  exact origin

def checkFilter (t : Tables) (a : Availability) (levels q : Nat → Nat)
    (parent : Key) (weight : Nat) : Option Check := do
  let payload ← t.weights weight
  if weightValid t weight then
    let leaf ← applyFilter t a levels q parent payload.boundary
    pure ⟨weight, payload.boundary, filterRegistered a q parent payload.boundary, leaf⟩
  else none

structure Body where
  parsed : Parsed
  checks : List Check
  postContext : Nat
  consumed : Bool
  continuation : Option Leaf
  deriving DecidableEq, Repr

def Body.leaves (b : Body) : List Leaf := b.checks.map Check.leaf ++ b.continuation.toList
def Body.children (b : Body) : List Key := b.leaves.flatMap Leaf.childKeys
def Body.fibers (b : Body) : List Fiber := b.leaves.flatMap Leaf.fibers

def consumed (upper : Endpoint) (checks : List Check) : Bool :=
  match upper with
  | .allowance view => checks.any (fun check => check.view == view)
  | _ => false

/-- Runs all callbacks in parser order. An empty filter list does NOT publish
and therefore preserves the stored Context, even if parsing computed zero. -/
def decompose (t : Tables) (a : Availability) (levels q : Nat → Nat)
    (parent : Key) (parsed : Parsed) : Option Body := do
  if relationGuard ⟨(currentPair q parent).1, (currentPair q parent).2,
      parent.context, parent.sources, parent.transformer⟩ then
    let checks ← collect (checkFilter t a levels q parent) parsed.filters
    let post := if parsed.filters = [] then parent.context else parsed.residual
    let eats := consumed (currentPair q parent).2 checks
    if parsed.filters ≠ [] ∧ a.publish = false then none
    else if eats then pure ⟨parsed, checks, post, true, none⟩
    else do
      let rest ← applyEffect t a levels q parent post (currentPair q parent)
      pure ⟨parsed, checks, post, false, some rest⟩
  else none

def expand (t : Tables) (a : Availability) (levels q : Nat → Nat)
    (fuel : Nat) (parent : Key) : Option Body :=
  let identity : Parsed := ⟨[], 0, false, false, false⟩
  if a.enter && decide (parent.lower = (currentPair q parent).1 ∧
      parent.upper = (currentPair q parent).2) then
    (if parent.context = 0 then some identity
      else if a.parser then parse t fuel parent.context else none).bind
      (decompose t a levels q parent)
  else none

/-- Value Context has exactly one successful route: identity or a parser result
with no filters. It forwards the STORED context to the indexed Value dispatcher.
This is an output to that owner, not a claimed proof of the Value dispatch. -/
structure ScopedDemand where
  originalCall : Nat
  useInstance : Nat
  root : Nat
  outputScope : Nat
  inputRoute : Nat
  deriving DecidableEq, Repr

structure ValueRequest (V : Type) where
  lower : V
  upper : V
  context : Nat
  sources : Option Nat
  transformer : Nat
  demand : Option ScopedDemand
  deriving DecidableEq, Repr

def valueContext {V : Type} (t : Tables) (fuel : Nat) (request : ValueRequest V) : Option (ValueRequest V) :=
  if request.transformer ≠ 0 then none
  else if request.context = 0 then some request
  else (parse t fuel request.context).bind fun p =>
    if p.filters = [] then some request else none

theorem value_context_exact {V : Type} {t : Tables} {fuel : Nat} {request output : ValueRequest V}
    (h : valueContext t fuel request = some output) :
    output = request ∧ request.transformer = 0 := by
  unfold valueContext at h
  split at h
  · cases h
  · rename_i identity
    have zero : request.transformer = 0 := by simpa using identity
    split at h
    · cases h; exact ⟨rfl, zero⟩
    · cases found : parse t fuel request.context with
      | none => simp [found] at h
      | some parsed =>
          simp only [found, Option.bind] at h
          split at h
          · cases h; exact ⟨rfl, zero⟩
          · cases h

theorem filtered_value_rejected {V : Type} (t : Tables) (fuel : Nat) (request : ValueRequest V)
    (p : Parsed) (nonidentity : request.context ≠ 0)
    (parsed : parse t fuel request.context = some p) (nonempty : p.filters ≠ []) :
    valueContext t fuel request = none := by
  simp [valueContext, nonidentity, parsed, nonempty]

inductive Request (V : Type) where
  | value (request : ValueRequest V)
  | effect (key : Key) (demand : Option ScopedDemand)

inductive ContextOutput (V : Type) where
  | value (request : ValueRequest V)
  | effect (body : Body)

def executeInput {V : Type} (t : Tables) (a : Availability) (levels q : Nat → Nat)
    (fuel : Nat) : Request V → Option (ContextOutput V)
  | .value request =>
      if a.enter && (decide (request.context = 0) || a.parser) then
        (valueContext t fuel request).map ContextOutput.value
      else none
  | .effect key demand =>
      if demand.isSome then none else (expand t a levels q fuel key).map ContextOutput.effect

theorem effect_demand_rejected {V : Type} (t : Tables) (a : Availability)
    (levels q : Nat → Nat) (fuel : Nat) (key : Key) (demand : ScopedDemand) :
    executeInput (V := V) t a levels q fuel (.effect key (some demand)) = none := rfl

theorem decompose_exact {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {parent : Key} {p : Parsed} {body : Body}
    (h : decompose t a levels q parent p = some body) :
    body.parsed = p ∧
    Aligned (fun w c => checkFilter t a levels q parent w = some c) p.filters body.checks ∧
    body.postContext = (if p.filters = [] then parent.context else p.residual) ∧
    body.consumed = consumed (currentPair q parent).2 body.checks ∧
    (body.consumed = true ↔ body.continuation = none) ∧
    (∀ leaf, body.continuation = some leaf →
      applyEffect t a levels q parent body.postContext (currentPair q parent) = some leaf) ∧
    (p.filters ≠ [] → a.publish = true) := by
  unfold decompose at h
  split at h
  · cases checks : collect (checkFilter t a levels q parent) p.filters with
    | none => simp [checks] at h
    | some cs =>
        simp only [checks] at h
        generalize postEq : (if p.filters = [] then parent.context else p.residual) = post at h
        split at h
        · cases h
        · rename_i available
          have published : p.filters ≠ [] → a.publish = true := by
            intro nonempty
            cases pub : a.publish
            · exact False.elim (available ⟨nonempty, pub⟩)
            · rfl
          dsimp at h
          split at h
          · rename_i eats
            cases h
            exact ⟨rfl, collect_exact _ checks, rfl, eats.symm, by simp, by simp, published⟩
          · rename_i eats
            cases rest : applyEffect t a levels q parent post (currentPair q parent) with
            | none => simp [rest] at h
            | some leaf =>
                simp only [rest, Option.bind, Option.some.injEq] at h
                subst body
                refine ⟨rfl, collect_exact _ checks, rfl, ?_, by simp, ?_, published⟩
                · cases con : consumed (currentPair q parent).2 cs
                  · rfl
                  · exact False.elim (eats con)
                · intro other same
                  cases same
                  exact rest
  · cases h

theorem aligned_length {α β : Type} {r : α → β → Prop} {xs : List α} {ys : List β}
    (h : Aligned r xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem aligned_member {α β : Type} {r : α → β → Prop} {xs : List α} {ys : List β}
    (h : Aligned r xs ys) {x : α} (mem : x ∈ xs) : ∃ y, y ∈ ys ∧ r x y := by
  induction h with
  | nil => cases mem
  | cons head tail ih =>
      rcases List.mem_cons.mp mem with same | old
      · subst x; exact ⟨_, by simp, head⟩
      · obtain ⟨y, member, related⟩ := ih old
        exact ⟨y, List.mem_cons_of_mem _ member, related⟩

theorem aligned_member_right {α β : Type} {r : α → β → Prop} {xs : List α} {ys : List β}
    (h : Aligned r xs ys) {y : β} (mem : y ∈ ys) : ∃ x, x ∈ xs ∧ r x y := by
  induction h with
  | nil => cases mem
  | cons head tail ih =>
      rcases List.mem_cons.mp mem with same | old
      · subst y; exact ⟨_, by simp, head⟩
      · obtain ⟨x, member, related⟩ := ih old
        exact ⟨x, List.mem_cons_of_mem _ member, related⟩

theorem check_filter_exact {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {parent : Key} {weight : Nat} {check : Check}
    (h : checkFilter t a levels q parent weight = some check) :
    check.weight = weight ∧ ∃ payload,
      t.weights weight = some payload ∧ check.view = payload.boundary ∧
      weightValid t weight = true ∧
      applyFilter t a levels q parent payload.boundary = some check.leaf := by
  unfold checkFilter at h
  cases found : t.weights weight with
  | none => simp [found] at h
  | some payload =>
      simp only [found] at h
      split at h
      · rename_i valid
        dsimp at h
        cases result : applyFilter t a levels q parent payload.boundary with
        | none => simp [result] at h
        | some leaf =>
            rw [result] at h
            change some (Check.mk weight payload.boundary (filterRegistered a q parent payload.boundary) leaf) = some check at h
            cases h
            exact ⟨rfl, payload, rfl, rfl, valid, result⟩
      · cases h

theorem every_filter_executed {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {parent : Key} {p : Parsed} {body : Body}
    (h : decompose t a levels q parent p = some body) :
    body.checks.length = p.filters.length ∧
    ∀ weight ∈ p.filters, ∃ check ∈ body.checks,
      check.weight = weight ∧ ∃ payload,
        t.weights weight = some payload ∧ check.view = payload.boundary ∧
        weightValid t weight = true ∧
        applyFilter t a levels q parent payload.boundary = some check.leaf := by
  have aligned := (decompose_exact h).2.1
  refine ⟨(aligned_length aligned).symm, ?_⟩
  intro weight present
  obtain ⟨check, member, result⟩ := aligned_member aligned present
  exact ⟨check, member, check_filter_exact result⟩

theorem empty_filters_keep_stored {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {parent : Key} {p : Parsed} {body : Body}
    (h : decompose t a levels q parent p = some body) (empty : p.filters = []) :
    body.postContext = parent.context := by
  simpa [empty] using (decompose_exact h).2.2.1

theorem apply_children_admitted {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {parent : Key} {context : Nat} {pair : Pair} {keys : List Key}
    (h : applyEffect t a levels q parent context pair = some (.children keys)) :
    ∃ pairs, Effect.checkOperand q (effectTables t) pair.1 pair.2 = .children pairs ∧
      Aligned (fun input child => admit t a q parent input = some child) pairs keys := by
  unfold applyEffect at h
  split at h
  · cases h
  · cases placed : placedBound levels pair.1 pair.2 with
    | some bound =>
        simp only [placed] at h
        split at h <;> cases h
    | none =>
        simp only [placed] at h
        split at h
        · cases outcome : Effect.checkOperand q (effectTables t) pair.1 pair.2 with
          | localReturn => simp [outcome] at h
          | unavailable => simp [outcome] at h
          | conflict lower upper => simp only [outcome] at h; split at h <;> cases h
          | children pairs =>
              simp only [outcome] at h
              cases children : collect (admit t a q parent) pairs with
              | none => simp [children] at h
              | some actual =>
                  simp only [children, Option.map_some, Option.some.injEq, Leaf.children.injEq] at h
                  subst keys
                  exact ⟨pairs, rfl, collect_exact _ children⟩
        · cases h

theorem whole_child_payload {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {parent : Key} {context : Nat} {pair : Pair} {keys : List Key}
    (h : applyEffect t a levels q parent context pair = some (.children keys)) :
    ∀ child ∈ keys,
      child.context = sourceContext (admissionTables t) child.upper ∧
      child.sources = parent.sources ∧ child.transformer = parent.transformer ∧
      (child.transformer = 0 ∨ child.lower ≠ child.upper) ∧ a.enqueue child = true := by
  obtain ⟨pairs, _, aligned⟩ := apply_children_admitted h
  intro child present
  obtain ⟨pair, _, admitted⟩ := aligned_member_right aligned present
  obtain ⟨same, ctx, sources, transformer, guard, enqueued⟩ := admit_payload admitted
  refine ⟨?_, sources, transformer, guard, enqueued⟩
  rw [same]
  simp [admittedChild, NativeReplayCurrent.sourceContext_rename]

theorem filter_children_from_apply {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {parent : Key} {view : Nat} {keys : List Key}
    (h : applyFilter t a levels q parent view = some (.children keys)) :
    applyEffect t a levels q parent 0 ((currentPair q parent).1, .allowance view) =
      some (.children keys) := by
  cases lower : (currentPair q parent).1 <;> simp only [applyFilter, lower] at h
  all_goals try exact h
  split at h
  · split at h <;> cases h
  · exact h

theorem full_body_child_payload {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {parent : Key} {p : Parsed} {body : Body}
    (h : decompose t a levels q parent p = some body) :
    ∀ child ∈ body.children,
      child.context = sourceContext (admissionTables t) child.upper ∧
      child.sources = parent.sources ∧ child.transformer = parent.transformer ∧
      (child.transformer = 0 ∨ child.lower ≠ child.upper) ∧ a.enqueue child = true := by
  have data := decompose_exact h
  intro child present
  obtain ⟨leaf, selected, member⟩ := List.mem_flatMap.mp present
  cases leaf with
  | localReturn => cases member
  | bound => cases member
  | conflict => cases member
  | children keys =>
      change Leaf.children keys ∈ body.checks.map Check.leaf ++ body.continuation.toList at selected
      rcases List.mem_append.mp selected with check | continuation
      · obtain ⟨c, chosen, same⟩ := List.mem_map.mp check
        obtain ⟨weight, _, result⟩ := aligned_member_right data.2.1 chosen
        obtain ⟨_, payload, _, _, _, applied⟩ := check_filter_exact result
        rw [same] at applied
        exact whole_child_payload (filter_children_from_apply applied) child member
      · have same := Option.mem_toList.mp continuation
        have applied := data.2.2.2.2.2.1 _ same
        exact whole_child_payload applied child member

theorem apply_bound_exact {t : Tables} {a : Availability} {levels q : Nat → Nat}
    {parent : Key} {context : Nat} {pair : Pair} {fiber : Fiber}
    (h : applyEffect t a levels q parent context pair = some (.bound fiber)) :
    fiber.bound.pair = pair ∧ fiber.key.context = context ∧
    fiber.key.sources = parent.sources ∧ fiber.key.transformer = parent.transformer ∧
    relationGuard fiber.key = true ∧ a.boundOrigin fiber = true ∧ a.physical fiber.bound = true ∧ a.replay fiber.bound = true := by
  unfold applyEffect at h
  split at h
  · cases h
  · cases placed : placedBound levels pair.1 pair.2 with
    | some bound =>
        simp only [placed] at h
        split at h
        · rename_i guards
          cases h
          have parts := Bool.and_eq_true_iff.mp guards
          have physical := Bool.and_eq_true_iff.mp parts.1
          have first := Bool.and_eq_true_iff.mp physical.1
          exact ⟨placed_bound_pair placed, rfl, rfl, rfl, first.1, first.2, physical.2, parts.2⟩
        · cases h
    | none =>
        simp only [placed] at h
        split at h
        · cases outcome : Effect.checkOperand q (effectTables t) pair.1 pair.2 with
          | localReturn => simp [outcome] at h
          | unavailable => simp [outcome] at h
          | conflict lower upper => simp only [outcome] at h; split at h <;> cases h
          | children pairs =>
              simp only [outcome] at h
              cases children : collect (admit t a q parent) pairs <;> simp [children] at h
        · cases h

def Body.transport (q : Nat → Nat) (post : Key → Nat) (b : Body) : Body :=
  { b with checks := b.checks.map (fun c => { c with leaf := c.leaf.transport q post })
           continuation := b.continuation.map (Leaf.transport q post) }

@[simp] theorem leaf_children_transport (q : Nat → Nat) (post : Key → Nat) (leaf : Leaf) :
    (leaf.transport q post).childKeys = leaf.childKeys := by cases leaf <;> rfl

@[simp] theorem leaf_fibers_transport (q : Nat → Nat) (post : Key → Nat) (leaf : Leaf) :
    (leaf.transport q post).fibers = leaf.fibers.map (carrier q post) := by cases leaf <;> rfl

theorem body_leaves_transport (q : Nat → Nat) (post : Key → Nat) (b : Body) :
    (b.transport q post).leaves = b.leaves.map (Leaf.transport q post) := by
  cases continuation : b.continuation <;>
    simp [Body.transport, Body.leaves, continuation, List.map_map]

@[simp] theorem body_children_transport (q : Nat → Nat) (post : Key → Nat) (b : Body) :
    (b.transport q post).children = b.children := by
  simp [Body.children, body_leaves_transport, List.flatMap_map]

theorem body_fibers_transport (q : Nat → Nat) (post : Key → Nat) (b : Body) :
    (b.transport q post).fibers = b.fibers.map (carrier q post) := by
  simp [Body.fibers, body_leaves_transport, List.flatMap_map, List.map_flatMap]

theorem body_factorization_transport (q : Nat → Nat) (post : Key → Nat) (b : Body) :
    (b.transport q post).parsed = b.parsed ∧
    (b.transport q post).checks.map (fun c => (c.weight, c.view, c.registered)) =
      b.checks.map (fun c => (c.weight, c.view, c.registered)) ∧
    (b.transport q post).consumed = b.consumed ∧
    (b.transport q post).continuation = b.continuation.map (Leaf.transport q post) := by
  simp [Body.transport, List.map_map]

/-- Exact constructor history of the installed body, including every merge.
There is no constructor accepting semantic coverage, `ClosedAt`, or a memo. -/
inductive Built (t : Tables) : (Nat → Nat) → Key → Body → Prop
  | computed (a : Availability) (levels q : Nat → Nat) (fuel : Nat) (key : Key) (body : Body)
      (result : expand t a levels q fuel key = some body) : Built t q key body
  | transported {old : Nat → Nat} {key : Key} {body : Body}
      (prior : Built t old key body) (q : Nat → Nat) (post : Key → Nat)
      (absorbs : ∀ row, q (old row) = q row) : Built t q key (body.transport q post)

inductive Pending where
  | retained | queued | active
  deriving DecidableEq, Repr

structure Graph where
  core : NativeReplayCurrent.Graph := {}
  bodies : Key → Option Body := fun _ => none
  pending : Key → Pending := fun _ => .retained
  returned : Key → Bool := fun _ => false
  discharges : List Discharge := []

def register (g : Graph) (keys : List Key) : Graph :=
  { g with
    core := NativeReplayCurrent.register g.core keys }

def install (g : Graph) (key : Key) (body : Body) : Graph :=
  { g with
    core := { g.core with
      vertices := attachAll (key :: body.children) g.core.vertices
      fibers := attachAll body.fibers g.core.fibers
      paths := g.core.paths ++ body.children.map (fun child => (key, child)) ++
        body.fibers.map (fun fiber => (key, fiber.key)) }
    bodies := fun other => if other = key then some body else g.bodies other
    returned := fun other => if other = key then false else g.returned other
    discharges := if body.parsed.filters = [] then g.discharges
      else g.discharges ++ [⟨key, body.parsed.filters, body.postContext⟩] }

def postContexts (g : Graph) : Key → Nat := postCheck (publications g.discharges [])

theorem identity_post_context (g : Graph) (key : Key) (identity : key.context = 0) :
    postContexts g key = 0 := identity_postCheck g.discharges key identity

def mergeGraph (g : Graph) (inputs : List Bound) (target index : Nat)
    (q : Nat → Nat) (post : Key → Nat) : Graph :=
  { g with
    core := NativeReplayCurrent.mergeGraph g.core inputs target index q post
    bodies := fun key => (g.bodies key).map (Body.transport q post) }

def Held (g : Graph) (key : Key) (body : Body) : Prop :=
  (∀ child ∈ body.children, child ∈ g.core.vertices ∧ DependencyPath g.core.paths key child) ∧
  (∀ fiber ∈ body.fibers, fiber ∈ g.core.fibers ∧ DependencyPath g.core.paths key fiber.key)

def Invariant (t : Tables) (g : Graph) : Prop :=
  ∀ key ∈ g.core.vertices, ∀ body, g.bodies key = some body →
    Built t g.core.q key body ∧ Held g key body

theorem held_install_old {g : Graph} {key target : Key} {body added : Body}
    (h : Held g key body) : Held (install g target added) key body := by
  constructor
  · intro child member
    obtain ⟨owned, route⟩ := h.1 child member
    exact ⟨(mem_attachAll _ _ _).mpr (Or.inl owned),
      route.weaken (fun _ he => List.mem_append_left _ (List.mem_append_left _ he))⟩
  · intro fiber member
    obtain ⟨owned, route⟩ := h.2 fiber member
    exact ⟨(mem_attachAll _ _ _).mpr (Or.inl owned),
      route.weaken (fun _ he => List.mem_append_left _ (List.mem_append_left _ he))⟩

theorem installed_held (g : Graph) (key : Key) (body : Body) :
    Held (install g key body) key body := by
  constructor
  · intro child member
    refine ⟨(mem_attachAll _ _ _).mpr (Or.inr (List.mem_cons_of_mem _ member)), ?_⟩
    exact .step (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨child, member, rfl⟩))) (.refl _)
  · intro fiber member
    refine ⟨(mem_attachAll _ _ _).mpr (Or.inr member), ?_⟩
    exact .step (List.mem_append_right _ (List.mem_map.mpr ⟨fiber, member, rfl⟩)) (.refl _)

theorem install_invariant {t : Tables} {g : Graph} (h : Invariant t g)
    (key : Key) (body : Body) (built : Built t g.core.q key body)
    (fresh : ∀ other, other ∉ g.core.vertices → g.bodies other = none) :
    Invariant t (install g key body) := by
  intro other member found result
  by_cases same : other = key
  · subst other
    simp only [install, ↓reduceIte, Option.some.injEq] at result
    subst found
    exact ⟨built, installed_held g key body⟩
  · simp only [install, same, ↓reduceIte] at result
    by_cases old : other ∈ g.core.vertices
    · obtain ⟨origin, held⟩ := h other old found result
      exact ⟨origin, held_install_old held⟩
    · rw [fresh other old] at result
      cases result

theorem held_merge {g : Graph} {key : Key} {body : Body} (h : Held g key body)
    (inputs : List Bound) (target index : Nat) (q : Nat → Nat) (post : Key → Nat) :
    Held (mergeGraph g inputs target index q post) key (body.transport q post) := by
  constructor
  · intro child member
    rw [body_children_transport] at member
    obtain ⟨owned, route⟩ := h.1 child member
    exact ⟨owned, route.weaken (fun _ he => List.mem_append_left _ he)⟩
  · intro fiber member
    rw [body_fibers_transport] at member
    obtain ⟨old, selected, same⟩ := List.mem_map.mp member
    subst fiber
    obtain ⟨owned, route⟩ := h.2 old selected
    have retained := copy_retains inputs target index post g.core.fibers old owned
    have carried := canonical_carrier_path q post _ old retained
    refine ⟨canonical_carrier q post _ old retained, ?_⟩
    apply NativeReplayCurrent.dependencyPath_trans
      (route.weaken (fun _ he => List.mem_append_left _ he))
    exact carried.weaken (fun _ he => List.mem_append_right _ (List.mem_append_right _ he))

theorem merge_invariant {t : Tables} {g : Graph} (h : Invariant t g)
    (inputs : List Bound) (target index : Nat) (q : Nat → Nat) (post : Key → Nat)
    (absorbs : ∀ row, q (g.core.q row) = q row) :
    Invariant t (mergeGraph g inputs target index q post) := by
  intro key member body result
  change (g.bodies key).map (Body.transport q post) = some body at result
  cases found : g.bodies key with
  | none => simp [found] at result
  | some old =>
      simp only [found, Option.map_some, Option.some.injEq] at result
      subst body
      obtain ⟨built, held⟩ := h key member old found
      exact ⟨.transported built q post absorbs, held_merge held inputs target index q post⟩

def Fresh (g : Graph) : Prop := ∀ key, key ∉ g.core.vertices → g.bodies key = none

inductive Step (t : Tables) : Graph → Graph → Prop
  | register (g : Graph) (keys : List Key) : Step t g (register g keys)
  | queue (g : Graph) (key : Key) (member : key ∈ g.core.vertices)
      (retained : g.pending key = .retained) :
      Step t g { g with pending := fun other => if other = key then .queued else g.pending other }
  | activate (g : Graph) (key : Key) (member : key ∈ g.core.vertices)
      (queued : g.pending key = .queued) :
      Step t g { g with pending := fun other => if other = key then .active else g.pending other }
  | expand (g : Graph) (a : Availability) (levels : Nat → Nat) (fuel : Nat)
      (key : Key) (body : Body) (member : key ∈ g.core.vertices)
      (active : g.pending key = .active)
      (result : expand t a levels g.core.q fuel key = some body) :
      Step t g (install g key body)
  /-- Reuse points to the same existing complete relation owner; it adds no
  body and certifies no completion. This covers an active back-reference too. -/
  | reuse (g : Graph) (key : Key) (registered : key ∈ g.core.vertices) : Step t g g
  | returned (g : Graph) (key : Key) (body : Body) (found : g.bodies key = some body) :
      Step t g { g with returned := fun other => if other = key then true else g.returned other }
  | merge (g : Graph) (inputs : List Bound) (target index : Nat)
      (q : Nat → Nat) (absorbs : ∀ row, q (g.core.q row) = q row) :
      Step t g (mergeGraph g inputs target index q (postContexts g))

inductive Reachable (t : Tables) : Graph → Prop
  | initial : Reachable t {}
  | step {g u} : Reachable t g → Step t g u → Reachable t u

theorem step_fresh {t : Tables} {g u : Graph} (step : Step t g u) (h : Fresh g) : Fresh u := by
  cases step with
  | register keys =>
      intro key absent
      exact h key (fun old => absent ((mem_attachAll _ _ _).mpr (Or.inl old)))
  | expand a levels fuel key body member active result =>
      intro other absent
      have notKey : other ≠ key := by
        intro same
        subst other
        exact absent ((mem_attachAll _ _ _).mpr (Or.inr (by simp)))
      simp only [install, notKey, ↓reduceIte]
      exact h other (fun old => absent ((mem_attachAll _ _ _).mpr (Or.inl old)))
  | queue => exact h
  | activate => exact h
  | reuse => exact h
  | returned => exact h
  | merge inputs target index q absorbs =>
      intro key absent
      simp [mergeGraph, h key absent]

theorem step_invariant {t : Tables} {g u : Graph} (step : Step t g u)
    (h : Invariant t g) (fresh : Fresh g) : Invariant t u := by
  cases step with
  | register keys =>
      intro key member body result
      by_cases old : key ∈ g.core.vertices
      · obtain ⟨built, held⟩ := h key old body result
        refine ⟨built, ?_, held.2⟩
        intro child selected
        obtain ⟨owned, route⟩ := held.1 child selected
        exact ⟨(mem_attachAll _ _ _).mpr (Or.inl owned), route⟩
      · change g.bodies key = some body at result
        rw [fresh key old] at result
        cases result
  | expand a levels fuel key body member active result =>
      exact install_invariant h key body (.computed a levels g.core.q fuel key body result) fresh
  | queue => exact h
  | activate => exact h
  | reuse => exact h
  | returned => exact h
  | merge inputs target index q absorbs =>
      exact merge_invariant h inputs target index q (postContexts g) absorbs

theorem reachable_invariant {t : Tables} {g : Graph} (h : Reachable t g) :
    Invariant t g ∧ Fresh g := by
  induction h with
  | initial =>
      constructor
      · intro key member; cases member
      · intro key _; rfl
  | step prior step ih => exact ⟨step_invariant step ih.1 ih.2, step_fresh step ih.2⟩

/-- This consumer unfolds precisely the installed body. Unlike the preceding
extensional `ClosedAt`, no other favorable key list can witness this predicate. -/
def InstalledAt (t : Tables) (g : Graph) : Nat → Key → Prop
  | 0, key => key ∈ g.core.vertices
  | depth + 1, key => key ∈ g.core.vertices ∧
      match g.bodies key with
      | none => g.pending key = .retained ∨ g.pending key = .queued ∨ g.pending key = .active
      | some body => Built t g.core.q key body ∧ Held g key body ∧
          ∀ child ∈ body.children, InstalledAt t g depth child

theorem installed_all_depths {t : Tables} {g : Graph} (h : Invariant t g)
    (depth : Nat) : ∀ key ∈ g.core.vertices, InstalledAt t g depth key := by
  induction depth with
  | zero => exact fun _ member => member
  | succ depth ih =>
      intro key member
      refine ⟨member, ?_⟩
      cases found : g.bodies key with
      | none => cases g.pending key <;> simp
      | some body =>
          obtain ⟨built, held⟩ := h key member body found
          exact ⟨built, held, fun child selected => ih child (held.1 child selected).1⟩

theorem construct_full_context {t : Tables} {g : Graph} (h : Reachable t g)
    (a : Availability) (levels : Nat → Nat) (fuel : Nat) (key : Key) (body : Body)
    (member : key ∈ g.core.vertices) (active : g.pending key = .active)
    (result : expand t a levels g.core.q fuel key = some body) :
    let next := install g key body
    Reachable t next ∧ next.bodies key = some body ∧ Held next key body ∧
      ∀ depth, InstalledAt t next depth key := by
  have reach := Reachable.step h (Step.expand g a levels fuel key body member active result)
  refine ⟨reach, by simp [install], installed_held g key body, ?_⟩
  intro depth
  exact installed_all_depths (reachable_invariant reach).1 depth key
    ((mem_attachAll _ _ _).mpr (Or.inr (by simp)))

theorem step_retains_vertex {t : Tables} {g u : Graph} (step : Step t g u)
    {key : Key} (member : key ∈ g.core.vertices) : key ∈ u.core.vertices := by
  cases step with
  | register keys => exact (mem_attachAll _ _ _).mpr (Or.inl member)
  | expand => exact (mem_attachAll _ _ _).mpr (Or.inl member)
  | queue => exact member
  | activate => exact member
  | reuse => exact member
  | returned => exact member
  | merge => exact member

structure ReplayState where
  replay : Replay.State Nat := {}
  graph : Graph := {}

inductive ReplayStep (t : Tables) (keyOf : Nat × Nat → Key) : ReplayState → ReplayState → Prop
  | lower (s : ReplayState) (id : Nat) : ReplayStep t keyOf s
      { s with replay := Replay.step s.replay (.lower id) }
  | upper (s : ReplayState) (id : Nat) : ReplayStep t keyOf s
      { s with replay := Replay.step s.replay (.upper id) }
  | replay (s : ReplayState) (incoming : Bool) : ReplayStep t keyOf s
      { replay := Replay.step s.replay (.replay incoming)
        graph := register s.graph ((Replay.children s.replay incoming).map keyOf) }
  | graph (s : ReplayState) (next : Graph) (step : Step t s.graph next) :
      ReplayStep t keyOf s { s with graph := next }

inductive ReplayReachable (t : Tables) (keyOf : Nat × Nat → Key) : ReplayState → Prop
  | initial : ReplayReachable t keyOf {}
  | step {s u} : ReplayReachable t keyOf s → ReplayStep t keyOf s u → ReplayReachable t keyOf u

structure ReplayInvariant (t : Tables) (keyOf : Nat × Nat → Key) (s : ReplayState) : Prop where
  origins : Replay.OriginInvariant s.replay
  graph : Invariant t s.graph
  fresh : Fresh s.graph
  roots : ∀ batch ∈ s.replay.operations, ∀ pair ∈ batch, keyOf pair ∈ s.graph.core.vertices

theorem replay_initial (t : Tables) (keyOf : Nat × Nat → Key) :
    ReplayInvariant t keyOf {} := by
  refine ⟨Replay.initial_origins, ?_, ?_, ?_⟩
  · intro key member; cases member
  · intro key _; rfl
  · intro batch member; cases member

theorem replay_step_invariant {t : Tables} {keyOf : Nat × Nat → Key} {s u : ReplayState}
    (step : ReplayStep t keyOf s u) (h : ReplayInvariant t keyOf s) :
    ReplayInvariant t keyOf u := by
  cases step with
  | lower id =>
      refine ⟨Replay.step_origins h.origins (.lower id), h.graph, h.fresh, ?_⟩
      simp only [Replay.step]; split <;> exact h.roots
  | upper id =>
      refine ⟨Replay.step_origins h.origins (.upper id), h.graph, h.fresh, ?_⟩
      simp only [Replay.step]; split <;> exact h.roots
  | replay incoming =>
      have step := Step.register (t := t) s.graph ((Replay.children s.replay incoming).map keyOf)
      refine ⟨Replay.step_origins h.origins (.replay incoming),
        step_invariant step h.graph h.fresh, step_fresh step h.fresh, ?_⟩
      intro batch member pair selected
      change batch ∈ s.replay.operations ++ [Replay.children s.replay incoming] at member
      rcases List.mem_append.mp member with old | new
      · exact (mem_attachAll _ _ _).mpr (Or.inl (h.roots batch old pair selected))
      · have same := List.mem_singleton.mp new
        subst batch
        exact (mem_attachAll _ _ _).mpr (Or.inr (List.mem_map.mpr ⟨pair, selected, rfl⟩))
  | graph next step =>
      refine ⟨h.origins, step_invariant step h.graph h.fresh, step_fresh step h.fresh, ?_⟩
      intro batch member pair selected
      exact step_retains_vertex step (h.roots batch member pair selected)

theorem replay_reachable_invariant {t : Tables} {keyOf : Nat × Nat → Key} {s : ReplayState}
    (h : ReplayReachable t keyOf s) : ReplayInvariant t keyOf s := by
  induction h with
  | initial => exact replay_initial t keyOf
  | step _ step ih => exact replay_step_invariant step ih

/-- Application to the unchanged historical Replay root. Full Context bodies
are constructed by `Step.expand`, not supplied as a recursive coverage premise. -/
theorem historical_full_context {t : Tables} {keyOf : Nat × Nat → Key} {s : ReplayState}
    (h : ReplayReachable t keyOf s) {operation index : Nat}
    {batch : List (Nat × Nat)} {pair : Nat × Nat}
    (owner : s.replay.operations[operation]? = some batch) (child : batch[index]? = some pair) :
    ∀ depth, InstalledAt t s.graph depth (keyOf pair) := by
  have inv := replay_reachable_invariant h
  have root := inv.roots batch (List.mem_of_getElem? owner) pair (List.mem_of_getElem? child)
  exact fun depth => installed_all_depths inv.graph depth _ root

theorem dependency_skip_full_context {t : Tables} {keyOf : Nat × Nat → Key} {s : ReplayState}
    (h : ReplayReachable t keyOf s) {pair : Nat × Nat} (seen : pair ∈ s.replay.dependencies) :
    pair ∉ Replay.children s.replay false ∧
      ∀ depth, InstalledAt t s.graph depth (keyOf pair) := by
  have inv := replay_reachable_invariant h
  obtain ⟨batch, member, selected⟩ := (inv.origins.dependencyOrigin pair).mp seen
  exact ⟨by simp [Replay.children, seen], fun depth =>
    installed_all_depths inv.graph depth _ (inv.roots batch member pair selected)⟩

theorem old_old_full_context {t : Tables} {keyOf : Nat × Nat → Key} {s : ReplayState}
    (h : ReplayReachable t keyOf s) {pair : Nat × Nat}
    (old : pair ∈ NativeReplayCoverage.product s.replay.oldLower s.replay.oldUpper) :
    ∀ depth, InstalledAt t s.graph depth (keyOf pair) :=
  (dependency_skip_full_context h ((replay_reachable_invariant h).origins.oldProduct pair old)).2

theorem full_product_context {t : Tables} {keyOf : Nat × Nat → Key} {s : ReplayState}
    (h : ReplayReachable t keyOf s) (incoming : Bool) (lower upper : Nat)
    (present : (lower, upper) ∈ NativeReplayCoverage.product s.replay.lower s.replay.upper) :
    let next : ReplayState :=
      { replay := Replay.step s.replay (.replay incoming)
        graph := register s.graph ((Replay.children s.replay incoming).map keyOf) }
    ∀ depth, InstalledAt t next.graph depth (keyOf (lower, upper)) := by
  have next := ReplayReachable.step h (ReplayStep.replay s incoming)
  have retained := Replay.replay_retains_all_products
    (replay_reachable_invariant h).origins incoming lower upper present
  exact (dependency_skip_full_context next retained).2

end YulangClosure.NativeContextExpansion
