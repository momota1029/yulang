import YulangClosure.NativeValuePorts

/-!
Outer native Value dispatch, complementary to `NativeValuePorts`.
The executable is a decoded, allocation-success projection of lib.rs
`dispatch_live_item`. A continuation is an operation request, never completion
or a semantic certificate. In particular duplicate, rewrite and row outcomes
still require their actual shared native history. Malformed Function store
reads are represented as native invariant violations, not accepted fallbacks.
-/
namespace YulangClosure.NativeValueStructure

open NativeValuePorts
open NativeContextExpansion (ScopedDemand ValueRequest)

abbrev Request := ValueRequest ValueEndpoint

structure ValuePair where
  lower : ValueEndpoint
  upper : ValueEndpoint
  deriving DecidableEq, Repr

def Request.pair (request : Request) : ValuePair := ⟨request.lower, request.upper⟩
def ValuePair.rename (q : Nat → Nat) (pair : ValuePair) : ValuePair :=
  ⟨pair.lower.rename q, pair.upper.rename q⟩
def Request.key (request : Request) : Key :=
  ⟨.value request.lower request.upper, request.context, request.sources,
    ⟨request.transformer, request.demand⟩⟩

theorem request_key_whole (request : Request) :
    request.key.pair = .value request.lower request.upper ∧
    request.key.context = request.context ∧ request.key.sources = request.sources ∧
    request.key.flow.transformer = request.transformer ∧
    request.key.flow.demand = request.demand := ⟨rfl, rfl, rfl, rfl, rfl⟩

inductive Shape where
  | bottom | int | unit | bool | str | function | record | variant
  | tuple (arity : Nat)
  deriving DecidableEq, Repr

def lowerShape : ValueEndpoint → Option Shape
  | .bottomPositive => some .bottom
  | .intPositive => some .int
  | .unitPositive => some .unit
  | .boolPositive => some .bool
  | .strPositive => some .str
  | .positiveFunction _ => some .function
  | .positiveRecord _ => some .record
  | .positiveVariant _ => some .variant
  | .positiveTuple _ arity => some (.tuple arity)
  | _ => none

def upperShape : ValueEndpoint → Option Shape
  | .bottomNegative => some .bottom
  | .intNegative => some .int
  | .unitNegative => some .unit
  | .boolNegative => some .bool
  | .strNegative => some .str
  | .negativeFunction _ => some .function
  | .negativeRecord _ => some .record
  | .negativeVariant _ => some .variant
  | .negativeTuple _ arity => some (.tuple arity)
  | _ => none

def incompatible (pair : ValuePair) : Option (Shape × Shape) := do
  let lower ← lowerShape pair.lower
  let upper ← upperShape pair.upper
  if lower ≠ .bottom ∧ lower ≠ upper then some (lower, upper) else none

theorem incompatible_exact {pair : ValuePair} {lower upper : Shape} :
    incompatible pair = some (lower, upper) ↔
      lowerShape pair.lower = some lower ∧ upperShape pair.upper = some upper ∧
      lower ≠ .bottom ∧ lower ≠ upper := by
  unfold incompatible
  cases lo : lowerShape pair.lower <;> cases hi : upperShape pair.upper <;>
    simp [Option.bind] <;> constructor <;> rintro ⟨a, b, c, d⟩ <;> subst_vars <;> try simp_all

theorem bottom_never_incompatible (upper : ValueEndpoint) :
    incompatible ⟨.bottomPositive, upper⟩ = none := by
  cases upper <;> rfl

theorem top_never_incompatible (lower : ValueEndpoint) :
    incompatible ⟨lower, .topNegative⟩ = none := by
  cases lower <;> rfl

/-- Raw store views retain the polarity-specific tags; malformed or absent
Function views correspond to `expect`/`unreachable`, not native Ok. -/
inductive TermView where
  | positiveFunction (ports : FunctionTerms)
  | negativeFunction (ports : FunctionTerms)
  | positiveTuple (elements : List Nat)
  | negativeTuple (elements : List Nat)
  | positiveRecord (fields : List (RecordBoundary.Field Nat))
  | negativeRecord (fields : List (RecordBoundary.Field Nat))
  | positiveVariant (alternatives : List Alternative)
  | negativeVariant (alternatives : List Alternative)
  | other
  deriving DecidableEq, Repr

structure Tables where
  term : Nat → Option TermView
  endpoints : TermEndpoints

inductive Diagnostic where
  | incompatible (lower upper : Shape)
  | recordMissing (upperIndex : Nat)
  | variantMissing (lowerIndex : Nat)
  deriving DecidableEq, Repr

inductive Failure where
  | receiptMismatch
  | identityExhausted
  | recordAdaptationUnavailable (lowerIndex upperIndex : Nat)
  | invariantViolation (positive : Bool) (term : Nat)
  deriving DecidableEq, Repr

inductive Family where
  | function | tuple | record | variant
  deriving DecidableEq, Repr

/-- This value does not execute extrusion or attest that its result is correct. -/
inductive ExtrusionRequest where
  | positive (endpoint : ValueEndpoint) (receivingRow level : Nat)
  | negative (endpoint : ValueEndpoint) (receivingRow level : Nat)
  deriving DecidableEq, Repr

inductive BoundPolarity where
  | positive | negative
  deriving DecidableEq, Repr

structure ValueBound where
  owner : Nat
  polarity : BoundPolarity
  endpoint : ValueEndpoint
  deriving DecidableEq, Repr

def ValueBound.pair (bound : ValueBound) : ValuePair :=
  match bound.polarity with
  | .positive => ⟨bound.endpoint, .row bound.owner⟩
  | .negative => ⟨.row bound.owner, bound.endpoint⟩

/-- `candidate_apply_value`, up to its actual insert/replay effects. -/
def selectBound (levels : Nat → Nat) (pair : ValuePair) : Option ValueBound :=
  if pair.lower = pair.upper then none else
  match pair.lower, pair.upper with
  | .row a, .row b =>
      if levels b ≤ levels a then some ⟨a, .negative, .row b⟩
      else some ⟨b, .positive, .row a⟩
  | lower, .row b => some ⟨b, .positive, lower⟩
  | .row a, upper => some ⟨a, .negative, upper⟩
  | _, _ => none

theorem selected_bound_exact {levels : Nat → Nat} {pair : ValuePair} {bound : ValueBound}
    (computed : selectBound levels pair = some bound) : bound.pair = pair := by
  rcases pair with ⟨lower, upper⟩
  unfold selectBound at computed
  split at computed
  · cases computed
  · cases lower <;> cases upper <;>
      simp only [Option.some.injEq] at computed
    all_goals first
      | (cases computed <;> rfl)
      | (split at computed <;> cases computed <;> rfl)

theorem selected_bound_rows {levels : Nat → Nat} {a b : Nat} (different : a ≠ b) :
    selectBound levels ⟨.row a, .row b⟩ =
      some (if levels b ≤ levels a then ⟨a, .negative, .row b⟩ else ⟨b, .positive, .row a⟩) := by
  by_cases order : levels b ≤ levels a <;> simp [selectBound, different, order]

def extrusionRequest (levels : Nat → Nat) (pair : ValuePair) : Option ExtrusionRequest :=
  match pair.lower, pair.upper with
  | .row _, .row _ => none
  | lower, .row row => some (.positive lower row (levels row))
  | .row row, upper => some (.negative upper row (levels row))
  | _, _ => none

/-- Actual post-extrusion control. `rewritten` is used only for candidate
copying; legacy extrusion ages the original endpoint in place. The current
canonical observation is supplied *after* that operation, as in apply_value_task. -/
inductive FallbackResult where
  | rewrite (target : ValuePair)
  | candidateApply (current : ValuePair) (bound : Option ValueBound)
  | legacyApply (original : ValuePair)
  deriving DecidableEq, Repr

def copiedPair (pair : ValuePair) (request : ExtrusionRequest) (copied : ValueEndpoint) : ValuePair :=
  match request with
  | .positive _ _ _ => { pair with lower := copied }
  | .negative _ _ _ => { pair with upper := copied }

def finishFallback (candidate : Bool) (current : Nat → Nat) (levels : Nat → Nat)
    (pair rewritten : ValuePair) : FallbackResult :=
  if candidate then
    if rewritten ≠ pair then .rewrite rewritten else
      let observed := pair.rename current
      .candidateApply observed (selectBound levels observed)
  else .legacyApply pair

theorem fallback_rewrite_iff (candidate : Bool) (current levels : Nat → Nat)
    (pair rewritten target : ValuePair) :
    finishFallback candidate current levels pair rewritten = .rewrite target ↔
      candidate = true ∧ rewritten ≠ pair ∧ rewritten = target := by
  unfold finishFallback
  split <;> try simp_all
  split <;> try simp_all

theorem fallback_candidate_apply_iff (candidate : Bool) (current levels : Nat → Nat)
    (pair rewritten observed : ValuePair) (bound : Option ValueBound) :
    finishFallback candidate current levels pair rewritten = .candidateApply observed bound ↔
      candidate = true ∧ rewritten = pair ∧ pair.rename current = observed ∧
        selectBound levels observed = bound := by
  unfold finishFallback
  split <;> try simp_all
  split <;> try simp_all

theorem fallback_selected_pair {candidate : Bool} {current levels : Nat → Nat}
    {pair rewritten observed : ValuePair} {bound : ValueBound}
    (computed : finishFallback candidate current levels pair rewritten = .candidateApply observed (some bound)) :
    observed = pair.rename current ∧ bound.pair = observed := by
  obtain ⟨_, _, same, selected⟩ := (fallback_candidate_apply_iff _ _ _ _ _ _ _).mp computed
  exact ⟨same.symm, selected_bound_exact selected⟩

inductive Local where
  | shortcut
  | diagnostic (reason : Diagnostic)
  | children (family : Family) (items : List Child)
  | fallback (extrude : Option ExtrusionRequest)
  | unavailable (failure : Failure)
  deriving DecidableEq, Repr

/-- Exact Function extraction; unlike non-Function endpoints, a bad tagged
Function does not silently enter the row fallback. -/
def readFunction (tables : Tables) (positive : Bool) (endpoint : ValueEndpoint) :
    Except Failure (Option FunctionTerms) :=
  match positive, endpoint with
  | true, .positiveFunction term =>
      match tables.term term with
      | some (.positiveFunction ports) => .ok (some ports)
      | _ => .error (.invariantViolation true term)
  | false, .negativeFunction term =>
      match tables.term term with
      | some (.negativeFunction ports) => .ok (some ports)
      | _ => .error (.invariantViolation false term)
  | _, _ => .ok none

def functionOrFallback (tables : Tables) (levels : Nat → Nat) (pair : ValuePair) : Local :=
  match readFunction tables true pair.lower with
  | .error failure => .unavailable failure
  | .ok lower =>
      match readFunction tables false pair.upper with
      | .error failure => .unavailable failure
      | .ok upper =>
          match lower, upper with
          | some lo, some hi => .children .function (functionChildren tables.endpoints lo hi)
          | _, _ => .fallback (extrusionRequest levels pair)

/-- Full local decision, after current/canonical/retained routing. A diagnostic
is a pending direct witness, not diagnostic acceptance or a successful typing. -/
def operand (tables : Tables) (levels : Nat → Nat) (request : Request) : Local :=
  let pair := request.pair
  match incompatible pair with
  | some (lo, hi) => .diagnostic (.incompatible lo hi)
  | none =>
    if pair.lower = .bottomPositive ∨ pair.upper = .topNegative then .shortcut else
    match pair.lower, pair.upper with
    | .positiveVariant lo, .negativeVariant hi =>
        match tables.term lo, tables.term hi with
        | some (.positiveVariant lower), some (.negativeVariant upper) =>
            match variantChildren tables.endpoints upper 0 lower with
            | .ok children => .children .variant children
            | .error index => .diagnostic (.variantMissing index)
        | _, _ => .unavailable .receiptMismatch
    | .positiveRecord lo, .negativeRecord hi =>
        match tables.term lo, tables.term hi with
        | some (.positiveRecord lower), some (.negativeRecord upper) =>
            match recordChildren tables.endpoints request.key lower upper with
            | .ok children => .children .record children
            | .error (.diagnosticMissing index) => .diagnostic (.recordMissing index)
            | .error (.unavailablePresence li ui) =>
                .unavailable (.recordAdaptationUnavailable li ui)
        | _, _ => .unavailable .receiptMismatch
    | .positiveTuple lo la, .negativeTuple hi ha =>
        if la ≠ ha then .unavailable .identityExhausted else
        match tables.term lo, tables.term hi with
        | some (.positiveTuple lower), some (.negativeTuple upper) =>
            match tupleChildren tables.endpoints la ha lower upper with
            | some children => .children .tuple children
            | none => .unavailable .identityExhausted
        | _, _ => .unavailable .identityExhausted
    | _, _ => functionOrFallback tables levels pair

structure Routing where
  current : ValuePair → Bool
  candidate : Bool
  canonical : Nat → Nat
  retained : ValuePair → Option ValuePair
  levels : Nat → Nat

inductive Route where
  | duplicate
  | canonical (rewritten : ValuePair)
  | retained (rewritten : ValuePair)
  | body (result : Local)
  deriving DecidableEq, Repr

/-- Native precedence is observable: duplicate before canonical, canonical
before retained, retained before incompatible/shortcut/structural dispatch. -/
def dispatch (tables : Tables) (routing : Routing) (request : Request) : Route :=
  if routing.current request.pair then .duplicate else
  if routing.candidate then
    let canonical := request.pair.rename routing.canonical
    if canonical ≠ request.pair then .canonical canonical else
    match routing.retained request.pair with
    | some rewritten => .retained rewritten
    | none => .body (operand tables routing.levels request)
  else .body (operand tables routing.levels request)

theorem dispatch_duplicate_iff (tables : Tables) (routing : Routing) (request : Request) :
    dispatch tables routing request = .duplicate ↔ routing.current request.pair = true := by
  unfold dispatch
  split <;> try simp_all
  split <;> try simp_all
  split <;> try simp_all
  cases routing.retained request.pair <;> try simp_all

theorem dispatch_canonical_iff (tables : Tables) (routing : Routing) (request : Request)
    (target : ValuePair) :
    dispatch tables routing request = .canonical target ↔
      routing.current request.pair = false ∧ routing.candidate = true ∧
      request.pair.rename routing.canonical ≠ request.pair ∧
      request.pair.rename routing.canonical = target := by
  unfold dispatch
  split <;> try simp_all
  split <;> try simp_all
  split <;> try simp_all
  cases routing.retained request.pair <;> try simp_all

theorem dispatch_retained_iff (tables : Tables) (routing : Routing) (request : Request)
    (target : ValuePair) :
    dispatch tables routing request = .retained target ↔
      routing.current request.pair = false ∧ routing.candidate = true ∧
      request.pair.rename routing.canonical = request.pair ∧
      routing.retained request.pair = some target := by
  unfold dispatch
  split <;> try simp_all
  split <;> try simp_all
  split <;> try simp_all
  cases h : routing.retained request.pair <;> try simp_all

theorem dispatch_body_iff (tables : Tables) (routing : Routing) (request : Request)
    (result : Local) :
    dispatch tables routing request = .body result ↔
      routing.current request.pair = false ∧
      (routing.candidate = false ∨
        request.pair.rename routing.canonical = request.pair ∧ routing.retained request.pair = none) ∧
      operand tables routing.levels request = result := by
  unfold dispatch
  split <;> try simp_all
  split <;> try simp_all
  split <;> try simp_all
  cases h : routing.retained request.pair <;> try simp_all

/-- The Context owner forwards the original entire request; this adapter does
not erase the demand, source or stored Context before native Value dispatch. -/
def afterContext (contexts : NativeContextExpansion.Tables) (fuel : Nat)
    (tables : Tables) (routing : Routing) (request : Request) : Option Route :=
  (NativeContextExpansion.valueContext contexts fuel request).map (dispatch tables routing)

theorem after_context_exact {contexts : NativeContextExpansion.Tables} {fuel : Nat}
    {tables : Tables} {routing : Routing} {request : Request} {route : Route}
    (computed : afterContext contexts fuel tables routing request = some route) :
    request.transformer = 0 ∧ route = dispatch tables routing request := by
  unfold afterContext at computed
  cases checked : NativeContextExpansion.valueContext contexts fuel request with
  | none => simp [checked] at computed
  | some forwarded =>
      have facts := NativeContextExpansion.value_context_exact checked
      exact ⟨facts.2, by simpa [checked, facts.1] using computed.symm⟩

/-- Structural execution consumes the actual computed branch and the exact
r4 native child loop. Other branches return None here because their *distinct*
owners must execute them; this adapter is not a reduced accepted language. -/
def executeChildren (tables : Tables) (routing : Routing) (request : Request)
    (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat) (post : Nat)
    (derived : Bool) (fuel : Nat) (arena : Arena) (queue : List NativeWork) : Option Cursor :=
  if routing.candidate then
    match dispatch tables routing request with
    | .body (.children _ items) =>
        drive views qv qe request.key post derived fuel (initialCursor arena items queue)
    | _ => none
  else none

theorem executed_children_readback {tables : Tables} {routing : Routing} {request : Request}
    {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat} {post : Nat}
    {derived : Bool} {fuel : Nat} {arena : Arena} {queue : List NativeWork} {cursor : Cursor}
    (computed : executeChildren tables routing request views qv qe post derived fuel arena queue = some cursor) :
    ∃ family items, dispatch tables routing request = .body (.children family items) ∧
      cursor.pending = none ∧
      ∃ jobs : List Work, jobs.map Work.source = items ∧
        cursor.queue = jobs.map Work.native ++ queue ∧
        (∀ work ∈ jobs, AdmissionResult cursor.arena views qv qe request.key post derived
          work.source work.receipt) ∧
        (∀ work ∈ jobs, work.native.replayAck = none) := by
  unfold executeChildren at computed
  split at computed
  next enabled =>
    cases branch : dispatch tables routing request with
    | duplicate | canonical | retained => simp [branch] at computed
    | body result =>
        cases result with
        | shortcut | diagnostic | fallback | unavailable => simp [branch] at computed
        | children family items =>
            simp only [branch] at computed
            obtain ⟨pending, jobs⟩ := drive_success_readback computed
            exact ⟨family, items, rfl, pending, jobs⟩
  next => cases computed

/-- Only the candidate typed-drain mode uses this port admission loop; the
noncandidate native path remains represented by dispatch and its own owner. -/
theorem executed_candidate {tables : Tables} {routing : Routing} {request : Request}
    {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat} {post : Nat}
    {derived : Bool} {fuel : Nat} {arena : Arena} {queue : List NativeWork} {cursor : Cursor}
    (computed : executeChildren tables routing request views qv qe post derived fuel arena queue = some cursor) :
    routing.candidate = true := by
  unfold executeChildren at computed
  split at computed
  next enabled => exact enabled
  next => cases computed

def executeAfterContext (contexts : NativeContextExpansion.Tables) (contextFuel : Nat)
    (tables : Tables) (routing : Routing) (request : Request)
    (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat) (post : Nat)
    (derived : Bool) (fuel : Nat) (arena : Arena) (queue : List NativeWork) : Option Cursor :=
  (NativeContextExpansion.valueContext contexts contextFuel request).bind fun forwarded =>
    executeChildren tables routing forwarded views qv qe post derived fuel arena queue

/-- Constructed composition: successful computed Context/Value/port execution
has one unchanged original full key and all resulting same-arena child receipts.
It does not turn these pending jobs into completed semantic bodies. -/
theorem context_value_children_readback
    {contexts : NativeContextExpansion.Tables} {contextFuel : Nat}
    {tables : Tables} {routing : Routing} {request : Request}
    {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat} {post : Nat}
    {derived : Bool} {fuel : Nat} {arena : Arena} {queue : List NativeWork} {cursor : Cursor}
    (computed : executeAfterContext contexts contextFuel tables routing request views qv qe post derived fuel arena queue = some cursor) :
    request.transformer = 0 ∧ routing.candidate = true ∧
    ∃ family items, dispatch tables routing request = .body (.children family items) ∧
      cursor.pending = none ∧
      ∃ jobs : List Work, jobs.map Work.source = items ∧
        cursor.queue = jobs.map Work.native ++ queue ∧
        (∀ work ∈ jobs, AdmissionResult cursor.arena views qv qe request.key post derived
          work.source work.receipt) ∧
        (∀ work ∈ jobs, work.native.replayAck = none) := by
  unfold executeAfterContext at computed
  cases checked : NativeContextExpansion.valueContext contexts contextFuel request with
  | none => simp [checked] at computed
  | some forwarded =>
      have facts := NativeContextExpansion.value_context_exact checked
      simp only [checked, Option.bind_some, facts.1] at computed
      exact ⟨facts.2, executed_candidate computed, executed_children_readback computed⟩


theorem operand_incompatible {tables : Tables} {levels : Nat → Nat} {request : Request}
    {lower upper : Shape} (bad : incompatible request.pair = some (lower, upper)) :
    operand tables levels request = .diagnostic (.incompatible lower upper) := by
  simp [operand, bad]

theorem operand_bottom {tables : Tables} {levels : Nat → Nat} {request : Request}
    (bottom : request.lower = .bottomPositive) : operand tables levels request = .shortcut := by
  simp [operand, Request.pair, bottom, bottom_never_incompatible]

theorem operand_top {tables : Tables} {levels : Nat → Nat} {request : Request}
    (top : request.upper = .topNegative) : operand tables levels request = .shortcut := by
  simp [operand, Request.pair, top, top_never_incompatible]

theorem operand_function {tables : Tables} {levels : Nat → Nat} {request : Request}
    {lo hi : Nat} {lower upper : FunctionTerms}
    (lowEndpoint : request.lower = .positiveFunction lo)
    (highEndpoint : request.upper = .negativeFunction hi)
    (lowRead : tables.term lo = some (.positiveFunction lower))
    (highRead : tables.term hi = some (.negativeFunction upper)) :
    operand tables levels request = .children .function (functionChildren tables.endpoints lower upper) := by
  simp [operand, Request.pair, lowEndpoint, highEndpoint, incompatible, lowerShape, upperShape,
    functionOrFallback, readFunction, lowRead, highRead]

theorem operand_variant {tables : Tables} {levels : Nat → Nat} {request : Request}
    {lo hi : Nat} {lower upper : List Alternative}
    (lowEndpoint : request.lower = .positiveVariant lo)
    (highEndpoint : request.upper = .negativeVariant hi)
    (lowRead : tables.term lo = some (.positiveVariant lower))
    (highRead : tables.term hi = some (.negativeVariant upper)) :
    operand tables levels request =
      match variantChildren tables.endpoints upper 0 lower with
      | .ok children => .children .variant children
      | .error index => .diagnostic (.variantMissing index) := by
  simp [operand, Request.pair, lowEndpoint, highEndpoint, incompatible, lowerShape, upperShape,
    lowRead, highRead]

theorem operand_record {tables : Tables} {levels : Nat → Nat} {request : Request}
    {lo hi : Nat} {lower upper : List (RecordBoundary.Field Nat)}
    (lowEndpoint : request.lower = .positiveRecord lo)
    (highEndpoint : request.upper = .negativeRecord hi)
    (lowRead : tables.term lo = some (.positiveRecord lower))
    (highRead : tables.term hi = some (.negativeRecord upper)) :
    operand tables levels request =
      match recordChildren tables.endpoints request.key lower upper with
      | .ok children => .children .record children
      | .error (.diagnosticMissing index) => .diagnostic (.recordMissing index)
      | .error (.unavailablePresence li ui) => .unavailable (.recordAdaptationUnavailable li ui) := by
  simp [operand, Request.pair, lowEndpoint, highEndpoint, incompatible, lowerShape, upperShape,
    lowRead, highRead]

theorem operand_tuple {tables : Tables} {levels : Nat → Nat} {request : Request}
    {lo hi arity : Nat} {lower upper : List Nat}
    (lowEndpoint : request.lower = .positiveTuple lo arity)
    (highEndpoint : request.upper = .negativeTuple hi arity)
    (lowRead : tables.term lo = some (.positiveTuple lower))
    (highRead : tables.term hi = some (.negativeTuple upper)) :
    operand tables levels request =
      match tupleChildren tables.endpoints arity arity lower upper with
      | some children => .children .tuple children
      | none => .unavailable .identityExhausted := by
  simp [operand, Request.pair, lowEndpoint, highEndpoint, incompatible, lowerShape, upperShape,
    lowRead, highRead]

/-- Tuple endpoint arity mismatch is caught by the earlier shape diagnostic;
the inner IdentityExhausted guard is not a way to accept differing tuples. -/
theorem operand_tuple_arity_mismatch {tables : Tables} {levels : Nat → Nat} {request : Request}
    {lo hi la ha : Nat} (low : request.lower = .positiveTuple lo la)
    (high : request.upper = .negativeTuple hi ha) (different : la ≠ ha) :
    operand tables levels request = .diagnostic (.incompatible (.tuple la) (.tuple ha)) := by
  apply operand_incompatible
  simp [incompatible, Request.pair, low, high, lowerShape, upperShape, different]

/-- A successful Variant domain scan entails a matching tag/arity for every
positive alternative, including alternatives with no payload children. -/
theorem variant_domain_iff (terms : TermEndpoints) (upper lower : List Alternative) (start : Nat) :
    (∃ children, variantChildren terms upper start lower = .ok children) ↔
      ∀ actual ∈ lower, upper.any (matching actual) = true := by
  induction lower generalizing start with
  | nil => simp [variantChildren]
  | cons actual rest ih =>
      by_cases found : upper.any (matching actual) = true
      · simp only [variantChildren, found, ↓reduceIte]
        constructor
        · rintro ⟨children, computed⟩
          cases tail : variantChildren terms upper (start + 1) rest with
          | error failure => simp [tail, Except.map] at computed
          | ok following =>
              have remaining := (ih (start + 1)).mp ⟨following, tail⟩
              simpa using And.intro found remaining
        · intro all
          have remaining : ∀ candidate ∈ rest, upper.any (matching candidate) = true :=
            fun candidate member => all candidate (List.mem_cons_of_mem _ member)
          obtain ⟨following, tail⟩ := (ih (start + 1)).mpr remaining
          exact ⟨variantArmChildren terms start actual upper ++ following, by simp [tail, Except.map]⟩
      · constructor
        · rintro ⟨children, computed⟩
          simp [variantChildren, found] at computed
        · intro all
          exact False.elim (found (all actual List.mem_cons_self))

/-- Every matching negative alternative contributes every payload obligation.
This combines actual domain acceptance with r4's full index-preserving scan. -/
theorem variant_all_payloads {terms : TermEndpoints} {upper lower : List Alternative}
    {children : List Child} (computed : variantChildren terms upper 0 lower = .ok children)
    {li ui pi : Nat} {actual expected : Alternative} {lo hi : Nat}
    (actualAt : lower[li]? = some actual) (expectedAt : upper[ui]? = some expected)
    (same : matching actual expected = true)
    (low : actual.payloads[pi]? = some lo) (high : expected.payloads[pi]? = some hi) :
    Child.mk (.variant li ui pi) (.value (terms.positiveValue lo) (terms.negativeValue hi)) ∈ children := by
  apply variant_children_no_omission computed li actual actualAt
  simpa using variant_arm_all_matches (terms := terms) (lowerIndex := li) expectedAt same low high

structure DirectWitness where
  terminal : ValuePair
  kind : Diagnostic
  distance : Nat
  firstField : Option FunctionField
  firstTupleIndex : Option Nat
  deriving DecidableEq, Repr

structure DiagnosticEdge where
  parent : ValuePair
  child : ValuePair
  field : Option FunctionField
  tupleIndex : Option Nat
  deriving DecidableEq, Repr

/-- These are actual diagnostic-edge *calls*, before native edge interning.
Effect children do not enter the Value diagnostic graph. Record/Variant indexes
remain in typed port dependencies, not fabricated diagnostic tuple indexes. -/
def edgeFor (parent : ValuePair) (child : Child) : Option DiagnosticEdge :=
  match child.task with
  | .effect _ _ => none
  | .value lo hi =>
      let field := match child.port with | .function field => some field | _ => none
      let tupleIndex := match child.port with | .tuple index => some index | _ => none
      some ⟨parent, ⟨lo, hi⟩, field, tupleIndex⟩

def diagnosticEdges (parent : ValuePair) (items : List Child) : List DiagnosticEdge :=
  items.filterMap (edgeFor parent)

theorem diagnostic_edge_iff (parent : ValuePair) (items : List Child) (edge : DiagnosticEdge) :
    edge ∈ diagnosticEdges parent items ↔ ∃ child ∈ items, edgeFor parent child = some edge := by
  exact List.mem_filterMap

theorem effect_child_no_diagnostic (parent : ValuePair) (port : Port)
    (lower upper : NativeMergeExpansion.Endpoint) :
    edgeFor parent ⟨port, .effect lower upper⟩ = none := rfl

theorem structural_diagnostic_metadata (parent : ValuePair) (lo hi li ui pi : Nat)
    (lower upper : ValueEndpoint) :
    edgeFor parent ⟨.record li ui, .value lower upper⟩ = some ⟨parent, ⟨lower, upper⟩, none, none⟩ ∧
    edgeFor parent ⟨.variant li ui pi, .value lower upper⟩ = some ⟨parent, ⟨lower, upper⟩, none, none⟩ ∧
    edgeFor parent ⟨.tuple lo, .value lower upper⟩ = some ⟨parent, ⟨lower, upper⟩, none, some lo⟩ ∧
    edgeFor parent ⟨.tuple hi, .value lower upper⟩ = some ⟨parent, ⟨lower, upper⟩, none, some hi⟩ :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Pending admission is not completed diagnostic acceptance. The fallback
must finish extrusion before its separate memo-publication owner is reached. -/
inductive Publication where
  | pending (direct : Option DirectWitness) (edgeCalls : List DiagnosticEdge)
  | awaitFallback
  | unavailable
  deriving DecidableEq, Repr

def publication (request : Request) : Local → Publication
  | .shortcut => .pending none []
  | .diagnostic reason => .pending (some ⟨request.pair, reason, 0, none, none⟩) []
  | .children _ items => .pending none (diagnosticEdges request.pair items)
  | .fallback _ => .awaitFallback
  | .unavailable _ => .unavailable

theorem diagnostic_publication_exact (request : Request) (reason : Diagnostic) :
    publication request (.diagnostic reason) =
      .pending (some ⟨request.pair, reason, 0, none, none⟩) [] := rfl

theorem function_diagnostic_edges (parent : ValuePair) (terms : TermEndpoints)
    (lower upper : FunctionTerms) :
    diagnosticEdges parent (functionChildren terms lower upper) =
      [⟨parent, ⟨terms.positiveValue upper.argument, terms.negativeValue lower.argument⟩, some .argument, none⟩,
       ⟨parent, ⟨terms.positiveValue lower.result, terms.negativeValue upper.result⟩, some .result, none⟩] := rfl

/-- Original payload values survive Context-to-Value adaptation in full; no
Call/use/root/output/input field is inferred from an endpoint-only identity. -/
theorem scoped_demand_whole (request : Request) (demand : ScopedDemand)
    (present : request.demand = some demand) :
    request.key.flow.demand = some demand ∧
    (request.key.flow.demand.map ScopedDemand.originalCall) = some demand.originalCall ∧
    (request.key.flow.demand.map ScopedDemand.useInstance) = some demand.useInstance ∧
    (request.key.flow.demand.map ScopedDemand.root) = some demand.root ∧
    (request.key.flow.demand.map ScopedDemand.outputScope) = some demand.outputScope ∧
    (request.key.flow.demand.map ScopedDemand.inputRoute) = some demand.inputRoute := by
  simp [Request.key, present]

end YulangClosure.NativeValueStructure
