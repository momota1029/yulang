import YulangClosure.ProviderNativeContextR57

/-! Source-indexed relation for candidate_receiver.rs certified_lower_paths.
Checked readers and allocation outcomes are explicit primitive inputs. This
does not assert that a borrowed Rust projection instantiates these functions. -/
namespace YulangClosure.ReachedSlotSearchR58

inductive Mode where | catchSearch | entrySearch deriving DecidableEq
inductive Gap where
  | searchLimit | ambiguousPath | boundMismatch | missingCommonEndpoint
  | missingUseAncestry | missingInternal | missingEmission | missingAdmission
  | missingRelation | foreignRelation | missingRoot | ambiguousRoot | invalidRelation
  | wrongEntrySlot | ambiguousPhysicalSlot | missingCatchFact | ambiguousCatchFact
  | missingProviderOrigin | ambiguousProviderOrigin
  deriving DecidableEq
inductive Site where
  | initialSeen | initialPending | popWork | resultCapacity | viewLookup | supportTail
  | memberWork | memberOrdinal | rowLookup | slotWork | physicalOwner | firstEntry
  | laterAncestry | useRoot | stepsCapacity | seenCapacity | pendingCapacity
  | relationIndex | relationCount
  deriving DecidableEq
inductive Reason where | nativeRead | allocation | overflow | workLimit deriving DecidableEq
structure Failure where
  site : Site
  gap : Gap
  reason : Reason
  deriving DecidableEq
def nativeFailure (site : Site) (gap : Gap) : Failure := ⟨site, gap, .nativeRead⟩

structure Limits where
  work : Nat
  usizeMax : Nat
  ordinalMax : Nat
  deriving DecidableEq
def nativeLimits : Limits := ⟨65536, 2^64-1, 2^32-1⟩
structure Resource where
  work : Nat
  allocations : List Bool
  deriving DecidableEq

def checkedAdd (limits : Limits) (site : Site) (a b : Nat) : Except Failure Nat :=
  if a+b ≤ limits.usizeMax then .ok (a+b) else .error ⟨site, .searchLimit, .overflow⟩
def charge (limits : Limits) (site : Site) (amount : Nat) (r : Resource) : Except Failure Resource := do
  let work ← checkedAdd limits site r.work amount
  if work ≤ limits.work then .ok { r with work } else .error ⟨site, .searchLimit, .workLimit⟩
def reserve (site : Site) (_amount : Nat) (r : Resource) : Except Failure Resource :=
  match r.allocations with
  | true :: rest => .ok { r with allocations := rest }
  | _ => .error ⟨site, .searchLimit, .allocation⟩

variable {S T : Type} [DecidableEq S] [DecidableEq T]
abbrev Endpoint := ProviderNativeContextR57.EffectEndpoint
abbrev PathStep (S T : Type) := ProviderNativeContextR57.Step S T
structure Branch (S T : Type) where
  endpoint : Endpoint
  steps : List (PathStep S T)
  seen : List Endpoint
  useRoot : Option Nat
  deriving DecidableEq
structure Query where
  root : Endpoint
  target : Endpoint
  mode : Mode
  deriving DecidableEq
inductive LowerLane where | row | atom deriving DecidableEq
structure Cell where
  lane : LowerLane
  index : Nat
  target : Endpoint
  deriving DecidableEq
def cells (bounds : ProviderNativeContextR57.Bounds Endpoint) : List Cell :=
  bounds.lowerRows.zipIdx.map (fun (item, index) => ⟨.row, index, .row item⟩) ++
    bounds.lowerAtoms.zipIdx.map (fun (item, index) => ⟨.atom, index, item⟩)
structure InternalReceipt (T : Type) where
  emissionIndex : Nat
  admissionIndex : Nat
  slot : ProviderNativeContextR57.Slot
  bound : ProviderNativeContextR57.Bound T
  relation : Nat
  useRoot : Nat
  deriving DecidableEq

/-- These are independently owned checked-reader calls, not an assumed
Context/native interpretation. Their Rust instantiation remains explicit. -/
structure Readers (S T : Type) where
  state : Nat
  relationCount : Nat
  rows : Nat → Except Failure (ProviderNativeContextR57.Bounds Endpoint)
  views : Nat → Except Failure (ProviderNativeContextR57.View S)
  physical : Nat → Cell → Except Failure (ProviderNativeContextR57.Physical T)
  /-- Identity/fact/drain portion of current_internal_emission, before its
  final require_relation_ancestry call; that call is explicit in policy. -/
  internalRoot : ProviderNativeContextR57.Physical T → Except Failure (InternalReceipt T)
  ancestry : Nat → Nat → Except Failure Unit

/-- require_relation_ancestry checks both indices, then rejects an oversized
relation inventory BEFORE reserving/visiting or accepting even equal nodes.
The independent inner visitor retains its own work/allocation failure. -/
def ancestryRead (e : Readers S T) (descendant ancestor : Nat) : Except Failure Unit :=
  if descendant < e.relationCount ∧ ancestor < e.relationCount then
    if e.relationCount ≤ 65536 then e.ancestry descendant ancestor
    else .error ⟨.relationCount, .searchLimit, .workLimit⟩
  else .error (nativeFailure .relationIndex .invalidRelation)

def policy (e : Readers S T) (mode : Mode) (b : Branch S T)
    (p : ProviderNativeContextR57.Physical T) : Except Failure (Option Nat) :=
  match mode, b.useRoot, b.steps with
  | .catchSearch, _, _ => .ok none
  | .entrySearch, none, [] => do
      let receipt ← e.internalRoot p
      let _ ← ancestryRead e receipt.relation receipt.useRoot
      if receipt.emissionIndex = p.emissionIndex ∧ receipt.admissionIndex = p.admissionIndex ∧
        receipt.slot = p.emission.physical ∧ receipt.bound = p.emission.bound
      then .ok (some receipt.useRoot)
      else .error (nativeFailure .firstEntry .boundMismatch)
  | .entrySearch, some root, _ :: _ => do
      let _ ← ancestryRead e p.relation root
      .ok (some root)
  | _, _, _ => .error (nativeFailure .useRoot .missingUseAncestry)

def initial (q : Query) : Branch S T := ⟨q.root, [], [q.root], none⟩
def child (b : Branch S T) (target : Endpoint) (step : PathStep S T) (useRoot : Option Nat) : Branch S T :=
  ⟨target, b.steps ++ [step], target :: b.seen, useRoot⟩
def supportStep (e : Readers S T) (v : ProviderNativeContextR57.View S) (family : S) (ordinal : Nat) : PathStep S T :=
  .support ⟨e.state, v.index, ordinal, family, v⟩
def popCharge (limits : Limits) (b : Branch S T) (r : Resource) : Except Failure Resource := do
  let sum ← checkedAdd limits .popWork b.steps.length b.seen.length
  let amount ← checkedAdd limits .popWork sum 1
  charge limits .popWork amount r
def pushReserve (limits : Limits) (b : Branch S T) (r : Resource) : Except Failure Resource := do
  let steps ← checkedAdd limits .stepsCapacity b.steps.length 1
  let r ← reserve .stepsCapacity steps r
  let seen ← checkedAdd limits .seenCapacity b.seen.length 1
  let r ← reserve .seenCapacity seen r
  reserve .pendingCapacity 1 r
def initializeSearch (q : Query) (r : Resource) : Except Failure (Resource × Branch S T) := do
  let r ← reserve .initialSeen 1 r
  let r ← reserve .initialPending 1 r
  .ok (r, initial q)

inductive Phase (S T : Type) where
  | pop
  | support (b : Branch S T) (view : ProviderNativeContextR57.View S) (remaining : List (S × Nat))
  | physical (b : Branch S T) (row : Nat) (remaining : List Cell)
structure Live (S T : Type) where
  resource : Resource
  pending : List (Branch S T)
  results : List (Branch S T)
  phase : Phase S T
inductive State (S T : Type) where
  | live (state : Live S T)
  | success (results : List (Branch S T))
  | failure (error : Failure)

/-- Exact checked reached prefixes, independent of the work/allocation budget.
The machine must prove that it creates only these prefixes. -/
inductive Checked (e : Readers S T) (q : Query) : Branch S T → Prop where
  | root : Checked e q (initial q)
  | support {b v index family ordinal}
      (prior : Checked e q b) (atSupport : b.endpoint = .support index)
      (read : e.views index = .ok v) (owned : v.state = e.state ∧ v.index = index)
      (closed : v.tail = none) (member : (family, ordinal) ∈ v.allowed.zipIdx)
      (ordinalFits : ordinal ≤ (2^32-1))
      (fresh : ProviderNativeContextR57.EffectEndpoint.annotationMember index ordinal ∉ b.seen) :
      Checked e q (child b (.annotationMember index ordinal) (supportStep e v family ordinal) b.useRoot)
  | physical {b row c p root bounds}
      (prior : Checked e q b) (atRow : b.endpoint = .row row)
      (read : e.rows row = .ok bounds) (member : c ∈ cells bounds)
      (fresh : c.target ∉ b.seen) (edge : e.physical row c = .ok p)
      (ownerPolicy : policy e q.mode b p = .ok root) :
      Checked e q (child b c.target (.physical p) root)

/-- Successful local source transitions. Pending is written with its top at
the head: each ascending-index loop push conses a child, exactly Vec::push/pop. -/
inductive Move (e : Readers S T) (q : Query) (limits : Limits) : Live S T → State S T → Prop where
  | done {r results} : Move e q limits ⟨r, [], results, .pop⟩ (.success results)
  | target {r r' r'' b pending}
      (atTarget : b.endpoint = q.target) (charged : popCharge limits b r = .ok r')
      (allocated : reserve .resultCapacity 1 r' = .ok r'') :
      Move e q limits ⟨r, b :: pending, [], .pop⟩ (.live ⟨r'', pending, [b], .pop⟩)
  | support {r r' b pending results index v}
      (different : b.endpoint ≠ q.target) (atSupport : b.endpoint = .support index)
      (charged : popCharge limits b r = .ok r') (read : e.views index = .ok v)
      (owned : v.state = e.state ∧ v.index = index) (closed : v.tail = none) :
      Move e q limits ⟨r, b :: pending, results, .pop⟩
        (.live ⟨r', pending, results, .support b v v.allowed.zipIdx⟩)
  | row {r r' b pending results index bounds}
      (different : b.endpoint ≠ q.target) (atRow : b.endpoint = .row index)
      (charged : popCharge limits b r = .ok r') (read : e.rows index = .ok bounds) :
      Move e q limits ⟨r, b :: pending, results, .pop⟩
        (.live ⟨r', pending, results, .physical b index (cells bounds)⟩)
  | leaf {r r' b pending results}
      (different : b.endpoint ≠ q.target)
      (notRow : ∀ index, b.endpoint ≠ .row index)
      (notSupport : ∀ index, b.endpoint ≠ .support index)
      (charged : popCharge limits b r = .ok r') :
      Move e q limits ⟨r, b :: pending, results, .pop⟩ (.live ⟨r', pending, results, .pop⟩)
  | supportDone {r b v pending results} :
      Move e q limits ⟨r, pending, results, .support b v []⟩ (.live ⟨r, pending, results, .pop⟩)
  | supportSkip {r r' b v f index rest pending results}
      (charged : charge limits .memberWork 1 r = .ok r') (fits : index ≤ limits.ordinalMax)
      (seen : ProviderNativeContextR57.EffectEndpoint.annotationMember v.index index ∈ b.seen) :
      Move e q limits ⟨r, pending, results, .support b v ((f,index)::rest)⟩
        (.live ⟨r', pending, results, .support b v rest⟩)
  | supportPush {r r' r'' b v f index rest pending results}
      (charged : charge limits .memberWork 1 r = .ok r')
      (fits : index ≤ limits.ordinalMax) (nativeFits : index ≤ 2^32-1)
      (fresh : ProviderNativeContextR57.EffectEndpoint.annotationMember v.index index ∉ b.seen)
      (allocated : pushReserve limits b r' = .ok r'') :
      Move e q limits ⟨r, pending, results, .support b v ((f,index)::rest)⟩
        (.live ⟨r'', child b (.annotationMember v.index index) (supportStep e v f index) b.useRoot :: pending,
          results, .support b v rest⟩)
  | rowDone {r b row pending results} :
      Move e q limits ⟨r, pending, results, .physical b row []⟩ (.live ⟨r, pending, results, .pop⟩)
  | rowSkip {r r' b row c rest pending results}
      (charged : charge limits .slotWork 1 r = .ok r') (seen : c.target ∈ b.seen) :
      Move e q limits ⟨r, pending, results, .physical b row (c::rest)⟩
        (.live ⟨r', pending, results, .physical b row rest⟩)
  | rowPush {r r' r'' b row c rest pending results p root}
      (charged : charge limits .slotWork 1 r = .ok r') (fresh : c.target ∉ b.seen)
      (edge : e.physical row c = .ok p) (ownerPolicy : policy e q.mode b p = .ok root)
      (allocated : pushReserve limits b r' = .ok r'') :
      Move e q limits ⟨r, pending, results, .physical b row (c::rest)⟩
        (.live ⟨r'', child b c.target (.physical p) root :: pending, results, .physical b row rest⟩)

/-- Fatal errors retain source program points, including late failure after a
target was already found. No rule resumes a failed search. -/
inductive Fault (e : Readers S T) (q : Query) (limits : Limits) : Live S T → Failure → Prop where
  | popCharge {r b pending results error}
      (failed : popCharge limits b r = .error error) : Fault e q limits ⟨r,b::pending,results,.pop⟩ error
  | targetReserve {r r' b pending results error}
      (atTarget : b.endpoint = q.target) (charged : popCharge limits b r = .ok r')
      (failed : reserve .resultCapacity 1 r' = .error error) : Fault e q limits ⟨r,b::pending,results,.pop⟩ error
  | secondTarget {r r' r'' b pending previous rest}
      (atTarget : b.endpoint = q.target) (charged : popCharge limits b r = .ok r')
      (allocated : reserve .resultCapacity 1 r' = .ok r'') :
      Fault e q limits ⟨r,b::pending,previous::rest,.pop⟩ (nativeFailure .resultCapacity .ambiguousPath)
  | view {r r' b pending results index error}
      (different : b.endpoint ≠ q.target) (atSupport : b.endpoint = .support index)
      (charged : popCharge limits b r = .ok r') (failed : e.views index = .error error) :
      Fault e q limits ⟨r,b::pending,results,.pop⟩ error
  | tail {r r' b pending results index v}
      (different : b.endpoint ≠ q.target) (atSupport : b.endpoint = .support index)
      (charged : popCharge limits b r = .ok r') (read : e.views index = .ok v) (openTail : v.tail ≠ none) :
      Fault e q limits ⟨r,b::pending,results,.pop⟩ (nativeFailure .supportTail .missingCommonEndpoint)
  | foreignView {r r' b pending results index v}
      (different : b.endpoint ≠ q.target) (atSupport : b.endpoint = .support index)
      (charged : popCharge limits b r = .ok r') (read : e.views index = .ok v)
      (foreign : ¬ (v.state = e.state ∧ v.index = index)) :
      Fault e q limits ⟨r,b::pending,results,.pop⟩ (nativeFailure .viewLookup .boundMismatch)
  | row {r r' b pending results index error}
      (different : b.endpoint ≠ q.target) (atRow : b.endpoint = .row index)
      (charged : popCharge limits b r = .ok r') (failed : e.rows index = .error error) :
      Fault e q limits ⟨r,b::pending,results,.pop⟩ error
  | supportCharge {r b v f index rest pending results error}
      (failed : charge limits .memberWork 1 r = .error error) :
      Fault e q limits ⟨r,pending,results,.support b v ((f,index)::rest)⟩ error
  | ordinal {r r' b v f index rest pending results}
      (charged : charge limits .memberWork 1 r = .ok r') (overflow : limits.ordinalMax < index) :
      Fault e q limits ⟨r,pending,results,.support b v ((f,index)::rest)⟩ ⟨.memberOrdinal,.searchLimit,.overflow⟩
  | supportReserve {r r' b v f index rest pending results error}
      (charged : charge limits .memberWork 1 r = .ok r') (fits : index ≤ limits.ordinalMax)
      (fresh : ProviderNativeContextR57.EffectEndpoint.annotationMember v.index index ∉ b.seen)
      (failed : pushReserve limits b r' = .error error) :
      Fault e q limits ⟨r,pending,results,.support b v ((f,index)::rest)⟩ error
  | rowCharge {r b row c rest pending results error}
      (failed : charge limits .slotWork 1 r = .error error) :
      Fault e q limits ⟨r,pending,results,.physical b row (c::rest)⟩ error
  | physical {r r' b row c rest pending results error}
      (charged : charge limits .slotWork 1 r = .ok r') (fresh : c.target ∉ b.seen)
      (failed : e.physical row c = .error error) :
      Fault e q limits ⟨r,pending,results,.physical b row (c::rest)⟩ error
  | ancestry {r r' b row c rest pending results p error}
      (charged : charge limits .slotWork 1 r = .ok r') (fresh : c.target ∉ b.seen)
      (edge : e.physical row c = .ok p) (failed : policy e q.mode b p = .error error) :
      Fault e q limits ⟨r,pending,results,.physical b row (c::rest)⟩ error
  | physicalReserve {r r' b row c rest pending results p root error}
      (charged : charge limits .slotWork 1 r = .ok r') (fresh : c.target ∉ b.seen)
      (edge : e.physical row c = .ok p) (ownerPolicy : policy e q.mode b p = .ok root)
      (failed : pushReserve limits b r' = .error error) :
      Fault e q limits ⟨r,pending,results,.physical b row (c::rest)⟩ error

inductive Step (e : Readers S T) (q : Query) (limits : Limits) : State S T → State S T → Prop where
  | move {s t} : Move e q limits s t → Step e q limits (.live s) t
  | failure {s error} : Fault e q limits s error → Step e q limits (.live s) (.failure error)
inductive Run (e : Readers S T) (q : Query) (limits : Limits) : State S T → State S T → Prop where
  | refl (s) : Run e q limits s s
  | next {s t u} : Step e q limits s t → Run e q limits t u → Run e q limits s u

def AllChecked (e : Readers S T) (q : Query) (branches : List (Branch S T)) : Prop :=
  ∀ b ∈ branches, Checked e q b
def ResultsChecked (e : Readers S T) (q : Query) (branches : List (Branch S T)) : Prop :=
  ∀ b ∈ branches, Checked e q b ∧ b.endpoint = q.target
def ActiveChecked (e : Readers S T) (q : Query) : Phase S T → Prop
  | .pop => True
  | .support b v rest => Checked e q b ∧ ∃ index,
      b.endpoint = .support index ∧ e.views index = .ok v ∧
      (v.state = e.state ∧ v.index = index) ∧ v.tail = none ∧ rest ⊆ v.allowed.zipIdx
  | .physical b row rest => Checked e q b ∧ b.endpoint = .row row ∧
      ∃ bounds, e.rows row = .ok bounds ∧ rest ⊆ cells bounds
def Invariant (e : Readers S T) (q : Query) : State S T → Prop
  | .live s => AllChecked e q s.pending ∧ ResultsChecked e q s.results ∧ ActiveChecked e q s.phase
  | .success results => ResultsChecked e q results
  | .failure _ => True

omit [DecidableEq S] in
theorem checked_seen_nodup (e : Readers S T) (q : Query) (b : Branch S T) (h : Checked e q b) : b.seen.Nodup := by
  induction h with
  | root => simp [initial]
  | support prior atSupport read owned closed member ordinalFits fresh ih =>
      exact List.nodup_cons.mpr ⟨fresh, ih⟩
  | physical prior atRow read member fresh edge ownerPolicy ih =>
      exact List.nodup_cons.mpr ⟨fresh, ih⟩

omit [DecidableEq S] in
theorem checked_seen_length (e : Readers S T) (q : Query) (b : Branch S T) (h : Checked e q b) :
    b.seen.length = b.steps.length + 1 := by
  induction h with
  | root => rfl
  | support prior atSupport read owned closed member ordinalFits fresh ih =>
      simpa [child, List.length_append] using ih
  | physical prior atRow read member fresh edge ownerPolicy ih =>
      simpa [child, List.length_append] using ih

omit [DecidableEq S] in
theorem move_preserves_checked (e : Readers S T) (q : Query) (limits : Limits)
    (s : Live S T) (t : State S T) (h : Move e q limits s t)
    (valid : Invariant e q (.live s)) : Invariant e q t := by
  cases h with
  | done => exact valid.2.1
  | target atTarget charged allocated =>
      refine ⟨fun b member => valid.1 b (List.mem_cons_of_mem _ member), ?_, trivial⟩
      intro b member
      have same := List.mem_singleton.mp member
      subst b
      exact ⟨valid.1 _ (List.mem_cons_self), atTarget⟩
  | support different atSupport charged read owned closed =>
      exact ⟨fun b member => valid.1 b (List.mem_cons_of_mem _ member), valid.2.1,
        valid.1 _ (by simp), _, atSupport, read, owned, closed, List.Subset.refl _⟩
  | row different atRow charged read =>
      exact ⟨fun b member => valid.1 b (List.mem_cons_of_mem _ member), valid.2.1,
        valid.1 _ (by simp), atRow, _, read, List.Subset.refl _⟩
  | leaf different notRow notSupport charged =>
      exact ⟨fun b member => valid.1 b (List.mem_cons_of_mem _ member), valid.2.1, trivial⟩
  | supportDone => exact ⟨valid.1, valid.2.1, trivial⟩
  | supportSkip charged fits seen =>
      rcases valid.2.2 with ⟨prior, index, atSupport, read, owned, closed, subset⟩
      exact ⟨valid.1, valid.2.1, prior, index, atSupport, read, owned, closed,
        fun x member => subset (List.mem_cons_of_mem _ member)⟩
  | supportPush charged fits nativeFits fresh allocated =>
      rename_i r r' r'' b v f ordinal rest pending results
      rcases valid.2.2 with ⟨prior, index, atSupport, read, owned, closed, subset⟩
      have next : Checked e q (child b (.annotationMember v.index ordinal) (supportStep e v f ordinal) b.useRoot) := by
        have member := subset (List.mem_cons_self)
        have fresh' : ProviderNativeContextR57.EffectEndpoint.annotationMember index ordinal ∉ b.seen := by
          simpa only [owned.2] using fresh
        have check := Checked.support prior atSupport read owned closed member nativeFits fresh'
        simpa only [owned.2] using check
      refine ⟨?_, valid.2.1, prior, index, atSupport, read, owned, closed,
        fun x member => subset (List.mem_cons_of_mem _ member)⟩
      intro b member
      rcases List.mem_cons.mp member with same | later
      · subst b; exact next
      · exact valid.1 b later
  | rowDone => exact ⟨valid.1, valid.2.1, trivial⟩
  | rowSkip charged seen =>
      rcases valid.2.2 with ⟨prior, atRow, bounds, read, subset⟩
      exact ⟨valid.1, valid.2.1, prior, atRow, bounds, read,
        fun x member => subset (List.mem_cons_of_mem _ member)⟩
  | rowPush charged fresh edge ownerPolicy allocated =>
      rcases valid.2.2 with ⟨prior, atRow, bounds, read, subset⟩
      have next := Checked.physical prior atRow read (subset (List.mem_cons_self)) fresh edge ownerPolicy
      refine ⟨?_, valid.2.1, prior, atRow, bounds, read,
        fun x member => subset (List.mem_cons_of_mem _ member)⟩
      intro b member
      rcases List.mem_cons.mp member with same | later
      · subst b; exact next
      · exact valid.1 b later

omit [DecidableEq S] in
theorem step_preserves_checked (e : Readers S T) (q : Query) (limits : Limits)
    (s t : State S T) (h : Step e q limits s t) (valid : Invariant e q s) : Invariant e q t := by
  cases h with
  | move h => exact move_preserves_checked e q limits _ _ h valid
  | failure h => trivial

omit [DecidableEq S] in
theorem run_preserves_checked (e : Readers S T) (q : Query) (limits : Limits)
    (s t : State S T) (h : Run e q limits s t) (valid : Invariant e q s) : Invariant e q t := by
  induction h with
  | refl => exact valid
  | next first rest ih => exact ih (step_preserves_checked e q limits _ _ first valid)

omit [DecidableEq S] in
theorem successful_results_checked (e : Readers S T) (q : Query) (limits : Limits)
    (r : Resource) (results : List (Branch S T))
    (run : Run e q limits (.live ⟨r,[initial q],[],.pop⟩) (.success results)) :
    ∀ b ∈ results, Checked e q b ∧ b.endpoint = q.target := by
  apply run_preserves_checked e q limits _ _ run
  constructor
  · intro b member
    have same : b = initial q := List.mem_singleton.mp member
    subst b
    exact .root
  constructor
  · intro b member
    cases member
  · trivial

/-- Once a checked target branch is queued, successful exhaustion cannot lose
it. Reached failures remain failure; this theorem never converts them to Ok. -/
def Present (b : Branch S T) : State S T → Prop
  | .live s => b ∈ s.pending ∨ b ∈ s.results
  | .success results => b ∈ results
  | .failure _ => True

omit [DecidableEq S] [DecidableEq T] in
theorem remove_non_target {head b : Branch S T} {pending : List (Branch S T)} {target : Endpoint}
    (terminal : b.endpoint = target) (different : head.endpoint ≠ target) (present : b ∈ head :: pending) : b ∈ pending := by
  rcases List.mem_cons.mp present with same | later
  · subst b; exact False.elim (different terminal)
  · exact later

omit [DecidableEq S] in
theorem step_preserves_queued_target (e : Readers S T) (q : Query) (limits : Limits)
    (s t : State S T) (h : Step e q limits s t) (b : Branch S T)
    (terminal : b.endpoint = q.target) (present : Present b s) : Present b t := by
  cases h with
  | failure h => trivial
  | move h =>
    cases h with
    | done => exact present.resolve_left (by simp)
    | target atTarget charged allocated =>
        rcases present with before | impossible
        · rcases List.mem_cons.mp before with same | later
          · exact Or.inr (List.mem_singleton.mpr same)
          · exact Or.inl later
        · simp at impossible
    | support different atSupport charged read owned closed =>
        exact present.elim (fun before => Or.inl (remove_non_target terminal different before)) Or.inr
    | row different atRow charged read =>
        exact present.elim (fun before => Or.inl (remove_non_target terminal different before)) Or.inr
    | leaf different notRow notSupport charged =>
        exact present.elim (fun before => Or.inl (remove_non_target terminal different before)) Or.inr
    | supportDone => exact present
    | supportSkip charged fits seen => exact present
    | supportPush charged fits nativeFits fresh allocated =>
        exact present.elim (fun before => Or.inl (List.mem_cons_of_mem _ before)) Or.inr
    | rowDone => exact present
    | rowSkip charged seen => exact present
    | rowPush charged fresh edge ownerPolicy allocated =>
        exact present.elim (fun before => Or.inl (List.mem_cons_of_mem _ before)) Or.inr

omit [DecidableEq S] in
theorem run_preserves_queued_target (e : Readers S T) (q : Query) (limits : Limits)
    (s t : State S T) (run : Run e q limits s t)
    (b : Branch S T) (terminal : b.endpoint = q.target) (queued : Present b s) : Present b t := by
  induction run with
  | refl => exact queued
  | next first rest ih => exact ih (step_preserves_queued_target e q limits _ _ first b terminal queued)

omit [DecidableEq S] in
theorem successful_exhaustion_complete_for_queued_targets (e : Readers S T) (q : Query) (limits : Limits)
    (s : State S T) (results : List (Branch S T)) (run : Run e q limits s (.success results))
    (b : Branch S T) (terminal : b.endpoint = q.target) (queued : Present b s) : b ∈ results :=
  run_preserves_queued_target e q limits s (.success results) run b terminal queued

omit [DecidableEq S] in
theorem failure_cannot_resume (e : Readers S T) (q : Query) (limits : Limits)
    (error : Failure) (t : State S T) : ¬ Step e q limits (.failure error) t := by
  intro impossible; cases impossible

omit [DecidableEq S] in
theorem failed_run_has_no_success (e : Readers S T) (q : Query) (limits : Limits)
    (error : Failure) (results : List (Branch S T)) : ¬ Run e q limits (.failure error) (.success results) := by
  intro impossible
  cases impossible with
  | next first rest => cases first

omit [DecidableEq S] in
theorem catch_policy_preserves_no_root (e : Readers S T) (b : Branch S T) (p : ProviderNativeContextR57.Physical T) :
    policy e .catchSearch b p = .ok none := rfl

omit [DecidableEq S] in
theorem entry_after_support_without_root_fails (e : Readers S T) (b : Branch S T)
    (p : ProviderNativeContextR57.Physical T) (noRoot : b.useRoot = none) (notFirst : b.steps ≠ []) :
    policy e .entrySearch b p = .error (nativeFailure .useRoot .missingUseAncestry) := by
  cases steps : b.steps with
  | nil => exact False.elim (notFirst steps)
  | cons head rest => simp [policy, noRoot, steps]

omit [DecidableEq S] [DecidableEq T] in
theorem oversized_relation_inventory_rejects_self (e : Readers S T) (root : Nat)
    (valid : root < e.relationCount) (tooLarge : 65536 < e.relationCount) :
    ancestryRead e root root = .error ⟨.relationCount, .searchLimit, .workLimit⟩ := by
  simp [ancestryRead, valid, Nat.not_le.mpr tooLarge]

omit [DecidableEq S] [DecidableEq T] in
theorem invalid_relation_precedes_size_guard (e : Readers S T) (descendant ancestor : Nat)
    (invalid : ¬ (descendant < e.relationCount ∧ ancestor < e.relationCount)) :
    ancestryRead e descendant ancestor = .error (nativeFailure .relationIndex .invalidRelation) := by
  simp [ancestryRead, invalid]

def AtMostOne : State S T → Prop
  | .live s => s.results.length ≤ 1
  | .success results => results.length ≤ 1
  | .failure _ => True

omit [DecidableEq S] in
theorem step_preserves_at_most_one (e : Readers S T) (q : Query) (limits : Limits)
    (s t : State S T) (step : Step e q limits s t) (unique : AtMostOne s) : AtMostOne t := by
  cases step with
  | failure h => trivial
  | move h => cases h <;> simp_all [AtMostOne]

omit [DecidableEq S] in
theorem run_preserves_at_most_one (e : Readers S T) (q : Query) (limits : Limits)
    (s t : State S T) (run : Run e q limits s t) (unique : AtMostOne s) : AtMostOne t := by
  induction run with
  | refl => exact unique
  | next first rest ih => exact ih (step_preserves_at_most_one e q limits _ _ first unique)

omit [DecidableEq S] in
theorem successful_results_never_ambiguous (e : Readers S T) (q : Query) (limits : Limits)
    (r : Resource) (results : List (Branch S T))
    (run : Run e q limits (.live ⟨r,[initial q],[],.pop⟩) (.success results)) : results.length ≤ 1 :=
  run_preserves_at_most_one e q limits _ _ run (by simp [AtMostOne])

def observed : State S T → Option (Except Failure (List (List (PathStep S T))))
  | .live _ => none
  | .success results => some (.ok (results.map Branch.steps))
  | .failure error => some (.error error)

theorem mode_is_part_of_query_identity (root target : Endpoint) :
    (Query.mk root target .catchSearch) ≠ Query.mk root target .entrySearch := by
  intro equal
  have impossible := congrArg Query.mode equal
  cases impossible

def encodedEndpoint (e : Readers S T) (p : Endpoint) : CurrentEmissionOwnershipR47.Endpoint (ProviderNativeContextR57.Key S T) :=
  ProviderNativeContextR57.endpoint e.state (.effect p)

theorem path_check_append
    (m : AuthenticatedResidualConsumerR49.Inputs Nat (ProviderNativeContextR57.Key S T) ProviderNativeContextR57.Fact)
    (root middle target : CurrentEmissionOwnershipR47.Endpoint (ProviderNativeContextR57.Key S T))
    (first last : List (AuthenticatedResidualConsumerR49.Step (ProviderNativeContextR57.Key S T)))
    (firstChecked : AuthenticatedResidualConsumerR49.pathCheck m root first middle = true)
    (lastChecked : AuthenticatedResidualConsumerR49.pathCheck m middle last target = true) :
    AuthenticatedResidualConsumerR49.pathCheck m root (first ++ last) target = true := by
  induction first generalizing root with
  | nil =>
    have equal : root = middle := of_decide_eq_true firstChecked
    subst root
    exact lastChecked
  | cons head tail ih =>
    have checked : AuthenticatedResidualConsumerR49.StepReads m root head ∧
        AuthenticatedResidualConsumerR49.pathCheck m (AuthenticatedResidualConsumerR49.next head) tail middle = true := by
      simpa [AuthenticatedResidualConsumerR49.pathCheck] using firstChecked
    simp only [List.cons_append, AuthenticatedResidualConsumerR49.pathCheck]
    simp [checked.1, ih _ checked.2]

/-- Per-reader commutation obligations, not a whole Context interpretation.
No concrete instance of these obligations is assumed to have been extracted
from Rust. Successful source paths use them only after the machine checks. -/
structure LocalDecode (e : Readers S T)
    (m : AuthenticatedResidualConsumerR49.Inputs Nat (ProviderNativeContextR57.Key S T) ProviderNativeContextR57.Fact) : Prop where
  physical : ∀ row cell p, e.physical row cell = .ok p →
    AuthenticatedResidualConsumerR49.StepReads m (encodedEndpoint e (.row row)) (ProviderNativeContextR57.step (.physical p)) ∧
    AuthenticatedResidualConsumerR49.next (ProviderNativeContextR57.step (.physical p)) = encodedEndpoint e cell.target
  support : ∀ index v family ordinal, e.views index = .ok v →
    v.state = e.state ∧ v.index = index → v.tail = none →
    (family, ordinal) ∈ v.allowed.zipIdx →
    AuthenticatedResidualConsumerR49.SupportReads m
      (ProviderNativeContextR57.support ⟨e.state,v.index,ordinal,family,v⟩)

theorem checked_paths_decode (e : Readers S T) (q : Query)
    (m : AuthenticatedResidualConsumerR49.Inputs Nat (ProviderNativeContextR57.Key S T) ProviderNativeContextR57.Fact)
    (decode : LocalDecode e m) (b : Branch S T) (checked : Checked e q b) :
    AuthenticatedResidualConsumerR49.pathCheck m (encodedEndpoint e q.root)
      (b.steps.map ProviderNativeContextR57.step) (encodedEndpoint e b.endpoint) = true := by
  induction checked with
  | root => simp [initial, AuthenticatedResidualConsumerR49.pathCheck]
  | support prior atSupport read owned closed member ordinalFits fresh ih =>
    rename_i b v index family ordinal
    have sr := decode.support _ _ _ _ read owned closed member
    have reads : AuthenticatedResidualConsumerR49.StepReads m (encodedEndpoint e b.endpoint)
        (ProviderNativeContextR57.step (supportStep e v family ordinal)) := by
      change encodedEndpoint e b.endpoint = _ ∧ _
      exact ⟨by simp [encodedEndpoint, atSupport, ProviderNativeContextR57.endpoint,
        ProviderNativeContextR57.support, owned.2], sr⟩
    have last : AuthenticatedResidualConsumerR49.pathCheck m (encodedEndpoint e b.endpoint)
        [ProviderNativeContextR57.step (supportStep e v family ordinal)] (encodedEndpoint e (.annotationMember index ordinal)) = true := by
      have next : AuthenticatedResidualConsumerR49.next
          (ProviderNativeContextR57.step (supportStep e v family ordinal)) = encodedEndpoint e (.annotationMember index ordinal) := by
        simp [AuthenticatedResidualConsumerR49.next,
        ProviderNativeContextR57.step, supportStep, ProviderNativeContextR57.support,
        encodedEndpoint, ProviderNativeContextR57.endpoint, owned.2]
      simp [AuthenticatedResidualConsumerR49.pathCheck, reads, next]
    simpa [child, List.map_append] using path_check_append m _ _ _ _ _ ih last
  | physical prior atRow read member fresh edge ownerPolicy ih =>
    rename_i b row c p root bounds
    have decoded := decode.physical _ _ _ edge
    have reads : AuthenticatedResidualConsumerR49.StepReads m (encodedEndpoint e b.endpoint)
        (ProviderNativeContextR57.step (.physical p)) := by simpa [atRow] using decoded.1
    have last : AuthenticatedResidualConsumerR49.pathCheck m (encodedEndpoint e b.endpoint)
        [ProviderNativeContextR57.step (.physical p)] (encodedEndpoint e c.target) = true := by
      simp [AuthenticatedResidualConsumerR49.pathCheck, reads, decoded.2]
    simpa [child, List.map_append] using path_check_append m _ _ _ _ _ ih last

theorem successful_paths_refine_existing_consumer (e : Readers S T) (q : Query) (limits : Limits)
    (r : Resource) (results : List (Branch S T))
    (run : Run e q limits (.live ⟨r,[initial q],[],.pop⟩) (.success results))
    (m : AuthenticatedResidualConsumerR49.Inputs Nat (ProviderNativeContextR57.Key S T) ProviderNativeContextR57.Fact)
    (decode : LocalDecode e m) (b : Branch S T) (member : b ∈ results) :
    AuthenticatedResidualConsumerR49.pathCheck m (encodedEndpoint e q.root)
      (b.steps.map ProviderNativeContextR57.step) (encodedEndpoint e q.target) = true ∧
    AuthenticatedResidualConsumerR49.Arrival m (encodedEndpoint e q.target) (encodedEndpoint e q.root) := by
  obtain ⟨checked, terminal⟩ := successful_results_checked e q limits r results run b member
  have path := checked_paths_decode e q m decode b checked
  rw [terminal] at path
  exact ⟨path, AuthenticatedResidualConsumerR49.lower_path_arrival _ _ _
    (AuthenticatedResidualConsumerR49.path_sound _ _ _ _ path)⟩

def fixtureCell : Cell := ⟨.atom,0,.annotationMember 0 0⟩
def fixtureBounds : ProviderNativeContextR57.Bounds Endpoint := ⟨[],[],[.annotationMember 0 0],[]⟩
def fixtureEdge : ProviderNativeContextR57.Physical Nat := ProviderNativeContextR57.fixturePhysical 6 1 1 []
def fixtureReaders : Readers Nat Nat :=
  { state := 1, relationCount := 3
    rows := fun index => if index = 6 ∨ index = 4 then .ok fixtureBounds else
      if index = 77 then .ok ⟨[],[],[.contribution 99],[]⟩ else .error (nativeFailure .rowLookup .boundMismatch)
    views := fun index => if index = 0 then .ok ProviderNativeContextR57.fixtureView
      else .error (nativeFailure .viewLookup .boundMismatch)
    physical := fun row cell => if row = 6 ∧ cell = fixtureCell then .ok fixtureEdge else
      if row = 4 ∧ cell = fixtureCell then .ok (ProviderNativeContextR57.fixturePhysical 4 0 0 [0])
      else .error (nativeFailure .physicalOwner .missingEmission)
    internalRoot := fun p => if p.emissionIndex = 0 then
      .ok ⟨0,0,ProviderNativeContextR57.fixtureSlot 4,ProviderNativeContextR57.fixtureBound 4,0,2⟩
      else .error (nativeFailure .firstEntry .wrongEntrySlot)
    ancestry := fun descendant ancestor => if descendant = ancestor ∨ (descendant = 0 ∧ ancestor = 2) then .ok ()
      else .error (nativeFailure .laterAncestry .missingUseAncestry) }
def fixtureCatchQuery : Query := ⟨.row 6,.annotationMember 0 0,.catchSearch⟩
def fixtureEntryQuery : Query := ⟨.row 6,.annotationMember 0 0,.entrySearch⟩
def resourceAt (work allocations : Nat) : Resource := ⟨work,List.replicate allocations true⟩
def fixtureBranch : Branch Nat Nat := initial fixtureCatchQuery
def fixtureChild : Branch Nat Nat := child fixtureBranch (.annotationMember 0 0) (.physical fixtureEdge) none
def fixtureStart : State Nat Nat := .live ⟨resourceAt 0 8,[fixtureBranch],[],.pop⟩
def fixtureRowPhase : State Nat Nat := .live ⟨resourceAt 2 8,[],[],.physical fixtureBranch 6 [fixtureCell]⟩
def fixturePushed : State Nat Nat := .live ⟨resourceAt 3 5,[fixtureChild],[],.physical fixtureBranch 6 []⟩
def fixturePending : State Nat Nat := .live ⟨resourceAt 3 5,[fixtureChild],[],.pop⟩
def fixtureRecorded : State Nat Nat := .live ⟨resourceAt 7 4,[],[fixtureChild],.pop⟩

theorem concrete_catch_success :
    Run fixtureReaders fixtureCatchQuery nativeLimits fixtureStart (.success [fixtureChild]) := by
  refine .next (t := fixtureRowPhase) (.move ?_) ?_
  · exact .row (index := 6) (bounds := fixtureBounds) (by decide) rfl rfl rfl
  refine .next (t := fixturePushed) (.move ?_) ?_
  · exact .rowPush (p := fixtureEdge) (root := none) (r' := resourceAt 3 8) rfl (by decide) rfl rfl rfl
  refine .next (t := fixturePending) (.move .rowDone) ?_
  refine .next (t := fixtureRecorded) (.move ?_) ?_
  · exact .target (r' := resourceAt 7 5) rfl rfl rfl
  exact .next (.move .done) (.refl _)

theorem concrete_entry_same_query_fails :
    Run fixtureReaders fixtureEntryQuery nativeLimits fixtureStart
      (.failure (nativeFailure .firstEntry .wrongEntrySlot)) := by
  refine .next (t := fixtureRowPhase) (.move ?_) ?_
  · exact .row (index := 6) (bounds := fixtureBounds) (by decide) rfl rfl rfl
  refine .next (.failure ?_) (.refl _)
  exact .ancestry (p := fixtureEdge) (r' := resourceAt 3 8) rfl (by decide) rfl rfl

theorem no_mode_free_table_for_these_outcomes :
    ¬ ∃ table : Endpoint → Endpoint → Except Failure (List (List (PathStep Nat Nat))),
      table fixtureCatchQuery.root fixtureCatchQuery.target = .ok [[.physical fixtureEdge]] ∧
      table fixtureEntryQuery.root fixtureEntryQuery.target = .error (nativeFailure .firstEntry .wrongEntrySlot) := by
  rintro ⟨table, success, failure⟩
  rw [show fixtureEntryQuery.root = fixtureCatchQuery.root from rfl,
    show fixtureEntryQuery.target = fixtureCatchQuery.target from rfl, success] at failure
  cases failure

def malformedUnreachable : ProviderNativeContextR57.Native Nat Nat :=
  { ProviderNativeContextR57.fixtureNative with effectRows := ProviderNativeContextR57.fixtureNative.effectRows ++
    [⟨1,77,77,⟨[],[],[.contribution 99],[]⟩⟩] }

theorem conservative_all_slot_failure_but_reached_success :
    ProviderNativeContextR57.derivedEdges malformedUnreachable = none ∧
    Run fixtureReaders fixtureCatchQuery nativeLimits fixtureStart (.success [fixtureChild]) :=
  ⟨by decide, concrete_catch_success⟩

theorem concrete_r57_consumer_path :
    AuthenticatedResidualConsumerR49.pathCheck ProviderNativeContextR57.fixtureContext.inputs
      (encodedEndpoint fixtureReaders fixtureCatchQuery.root)
      (fixtureChild.steps.map ProviderNativeContextR57.step)
      (encodedEndpoint fixtureReaders fixtureCatchQuery.target) = true := by decide

theorem concrete_resource_boundaries :
    charge ⟨2,100,100⟩ .slotWork 1 (resourceAt 1 0) = .ok (resourceAt 2 0) ∧
    charge ⟨2,100,100⟩ .slotWork 1 (resourceAt 2 0) = .error ⟨.slotWork,.searchLimit,.workLimit⟩ ∧
    checkedAdd ⟨100,2,100⟩ .popWork 2 1 = .error ⟨.popWork,.searchLimit,.overflow⟩ ∧
    reserve .stepsCapacity 2 ⟨0,[false]⟩ = .error ⟨.stepsCapacity,.searchLimit,.allocation⟩ ∧
    initializeSearch (S := Nat) (T := Nat) fixtureCatchQuery (resourceAt 0 10) =
      .ok (resourceAt 0 8,fixtureBranch) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem concrete_relation_guard_even_for_reflexivity :
    ancestryRead { fixtureReaders with relationCount := 65537 } 0 0 =
      .error ⟨.relationCount,.searchLimit,.workLimit⟩ ∧
    ancestryRead fixtureReaders 0 0 = .ok () := ⟨rfl,rfl⟩

theorem concrete_second_target_is_fatal :
    Fault fixtureReaders fixtureCatchQuery nativeLimits
      ⟨resourceAt 3 5,[fixtureChild],[fixtureChild],.pop⟩
      (nativeFailure .resultCapacity .ambiguousPath) :=
  .secondTarget (r' := resourceAt 7 5) (r'' := resourceAt 7 4) rfl rfl rfl

theorem concrete_reached_malformed_alternative_is_fatal :
    Fault fixtureReaders fixtureCatchQuery nativeLimits
      ⟨resourceAt 7 4,[],[fixtureChild],.physical fixtureBranch 77 [⟨.atom,0,.contribution 99⟩]⟩
      (nativeFailure .physicalOwner .missingEmission) :=
  .physical (r' := resourceAt 8 4) rfl (by decide) rfl

theorem concrete_cycle_skip_precedes_malformed_owner :
    fixtureReaders.physical 6 ⟨.row,0,.row 6⟩ = .error (nativeFailure .physicalOwner .missingEmission) ∧
    Move fixtureReaders fixtureCatchQuery nativeLimits
      ⟨resourceAt 2 8,[],[],.physical fixtureBranch 6 [⟨.row,0,.row 6⟩]⟩
      (.live ⟨resourceAt 3 8,[],[],.physical fixtureBranch 6 []⟩) :=
  ⟨rfl,.rowSkip rfl (by decide)⟩

theorem concrete_open_support_is_fatal :
    Fault { fixtureReaders with views := fun _ => .ok { ProviderNativeContextR57.fixtureView with tail := some 9 } }
      ⟨.support 0,.annotationMember 0 0,.catchSearch⟩ nativeLimits
      ⟨resourceAt 0 8,[⟨.support 0,[],[.support 0],none⟩],[],.pop⟩
      (nativeFailure .supportTail .missingCommonEndpoint) :=
  .tail (r' := resourceAt 2 8) (index := 0) (v := { ProviderNativeContextR57.fixtureView with tail := some 9 })
    (by decide) rfl rfl rfl (by decide)


/-- Concrete reader commutation for the finite R57 fixture; this is not a
Rust-to-Lean interpretation or a general projection correspondence claim. -/
theorem concrete_fixture_decoder : LocalDecode fixtureReaders ProviderNativeContextR57.fixtureContext.inputs := by
  constructor
  · intro row cell p read
    change (if row = 6 ∧ cell = fixtureCell then Except.ok fixtureEdge else
      if row = 4 ∧ cell = fixtureCell then Except.ok (ProviderNativeContextR57.fixturePhysical 4 0 0 [0])
      else Except.error (nativeFailure .physicalOwner .missingEmission)) = Except.ok p at read
    split at read
    next yes =>
      rcases yes with ⟨rfl,rfl⟩
      cases read
      exact ⟨by decide,rfl⟩
    next no =>
      split at read
      next yes =>
        rcases yes with ⟨rfl,rfl⟩
        cases read
        exact ⟨by decide,rfl⟩
      next no => cases read
  · intro index v family ordinal read owned closed member
    change (if index = 0 then Except.ok ProviderNativeContextR57.fixtureView else
      Except.error (nativeFailure .viewLookup .boundMismatch)) = Except.ok v at read
    split at read
    next yes =>
      subst index
      cases read
      have equal : family = 7 ∧ ordinal = 0 := by
        simpa [ProviderNativeContextR57.fixtureView] using member
      rcases equal with ⟨rfl,rfl⟩
      decide
    next no => cases read

theorem concrete_success_applied_to_r57_context :
    AuthenticatedResidualConsumerR49.Arrival ProviderNativeContextR57.fixtureContext.inputs
      (encodedEndpoint fixtureReaders fixtureCatchQuery.target)
      (encodedEndpoint fixtureReaders fixtureCatchQuery.root) :=
  (successful_paths_refine_existing_consumer fixtureReaders fixtureCatchQuery nativeLimits
    (resourceAt 0 8) [fixtureChild] concrete_catch_success
    ProviderNativeContextR57.fixtureContext.inputs concrete_fixture_decoder fixtureChild (by simp)).2

/-- The Internal reader's ancestry is checked before the caller compares the
returned identity/slot/bound. An invalid root cannot become BoundMismatch. -/
theorem concrete_first_internal_ancestry_precedes_mismatch :
    policy { fixtureReaders with internalRoot := (fun _ => .ok ⟨99,99,ProviderNativeContextR57.fixtureSlot 4,ProviderNativeContextR57.fixtureBound 4,0,99⟩) }
      .entrySearch fixtureBranch fixtureEdge = .error (nativeFailure .relationIndex .invalidRelation) := rfl

def fixtureSupportBranch : Branch Nat Nat := ⟨.support 0,[],[.support 0],none⟩
def fixtureOrderedView : ProviderNativeContextR57.View Nat :=
  { ProviderNativeContextR57.fixtureView with allowed := [7,11] }
def fixtureMember0 : Branch Nat Nat := child fixtureSupportBranch (.annotationMember 0 0)
  (supportStep fixtureReaders fixtureOrderedView 7 0) none
def fixtureMember1 : Branch Nat Nat := child fixtureSupportBranch (.annotationMember 0 1)
  (supportStep fixtureReaders fixtureOrderedView 11 1) none

theorem concrete_ascending_pushes_reverse_pending_order :
    Run fixtureReaders ⟨.support 0,.row 900,.catchSearch⟩ nativeLimits
      (.live ⟨resourceAt 2 8,[],[],.support fixtureSupportBranch fixtureOrderedView [(7,0),(11,1)]⟩)
      (.live ⟨resourceAt 4 2,[fixtureMember1,fixtureMember0],[],.pop⟩) := by
  refine .next (t := .live ⟨resourceAt 3 5,[fixtureMember0],[],
    .support fixtureSupportBranch fixtureOrderedView [(11,1)]⟩) (.move ?_) ?_
  · exact .supportPush (r' := resourceAt 3 8) rfl (by decide) (by decide) (by decide) rfl
  refine .next (t := .live ⟨resourceAt 4 2,[fixtureMember1,fixtureMember0],[],
    .support fixtureSupportBranch fixtureOrderedView []⟩) (.move ?_) ?_
  · exact .supportPush (r' := resourceAt 4 5) rfl (by decide) (by decide) (by decide) rfl
  exact .next (.move .supportDone) (.refl _)

theorem concrete_late_entry_ancestry_failure :
    Fault fixtureReaders fixtureEntryQuery nativeLimits
      ⟨resourceAt 7 4,[],[fixtureChild],.physical { fixtureChild with seen := [.row 6,.row 4], useRoot := some 2 } 6 [fixtureCell]⟩
      (nativeFailure .laterAncestry .missingUseAncestry) :=
  .ancestry (p := fixtureEdge) (r' := resourceAt 8 4) rfl (by decide) rfl rfl


/-- R2 generation attempt: compute a complete physical expansion, preserving
all primitive reader and resource failures. This is one source loop, not an
assumed whole-search candidate/result correspondence. -/
def expandRows (e : Readers S T) (q : Query) (limits : Limits) (b : Branch S T) (row : Nat) :
    List Cell → Resource → Except Failure (Resource × List (Branch S T))
  | [], r => .ok (r,[])
  | c::rest, r => do
      let r' ← charge limits .slotWork 1 r
      if c.target ∈ b.seen then expandRows e q limits b row rest r'
      else do
        let p ← e.physical row c
        let root ← policy e q.mode b p
        let r'' ← pushReserve limits b r'
        let (final, later) ← expandRows e q limits b row rest r''
        .ok (final,later ++ [child b c.target (.physical p) root])

omit [DecidableEq S] in
theorem row_expansion_schedules_all (e : Readers S T) (q : Query) (limits : Limits)
    (b : Branch S T) (row : Nat) (cs : List Cell) (r final : Resource)
    (children pending results : List (Branch S T))
    (expanded : expandRows e q limits b row cs r = .ok (final,children)) :
    Run e q limits (.live ⟨r,pending,results,.physical b row cs⟩)
      (.live ⟨final,children ++ pending,results,.pop⟩) := by
  induction cs generalizing r children pending with
  | nil =>
    cases expanded
    exact .next (.move .rowDone) (.refl _)
  | cons c rest ih =>
    simp only [expandRows] at expanded
    cases charged : charge limits .slotWork 1 r with
    | error error => simp [charged, Bind.bind, Except.bind] at expanded
    | ok r' =>
      simp only [charged, Bind.bind, Except.bind] at expanded
      by_cases seen : c.target ∈ b.seen
      · simp only [seen, ↓reduceIte] at expanded
        exact .next (.move (.rowSkip charged seen)) (ih r' children pending expanded)
      · simp only [seen, ↓reduceIte] at expanded
        cases edge : e.physical row c with
        | error error => simp [edge] at expanded
        | ok p =>
          simp only [edge] at expanded
          cases owner : policy e q.mode b p with
          | error error => simp [owner] at expanded
          | ok root =>
            simp only [owner] at expanded
            cases allocated : pushReserve limits b r' with
            | error error => simp [allocated] at expanded
            | ok r'' =>
              simp only [allocated] at expanded
              cases later : expandRows e q limits b row rest r'' with
              | error error => simp [later] at expanded
              | ok pair =>
                rcases pair with ⟨final',children'⟩
                simp only [later, Except.ok.injEq, Prod.mk.injEq] at expanded
                rcases expanded with ⟨rfl,rfl⟩
                have next := ih r'' children' (child b c.target (.physical p) root :: pending) later
                simpa [List.append_assoc] using
                  Run.next (.move (.rowPush charged seen edge owner allocated)) next

omit [DecidableEq S] in
theorem row_expansion_contains_selected_child (e : Readers S T) (q : Query) (limits : Limits)
    (b : Branch S T) (row : Nat) (cs : List Cell) (r final : Resource)
    (children : List (Branch S T))
    (expanded : expandRows e q limits b row cs r = .ok (final,children))
    (c : Cell) (member : c ∈ cs) (fresh : c.target ∉ b.seen)
    (p : ProviderNativeContextR57.Physical T) (edge : e.physical row c = .ok p)
    (root : Option Nat) (owner : policy e q.mode b p = .ok root) :
    child b c.target (.physical p) root ∈ children := by
  induction cs generalizing r children with
  | nil => cases member
  | cons head rest ih =>
    simp only [expandRows] at expanded
    cases charged : charge limits .slotWork 1 r with
    | error error => simp [charged, Bind.bind, Except.bind] at expanded
    | ok r' =>
      simp only [charged, Bind.bind, Except.bind] at expanded
      by_cases seen : head.target ∈ b.seen
      · simp only [seen, ↓reduceIte] at expanded
        have later : c ∈ rest := by
          rcases List.mem_cons.mp member with same | later
          · subst head; exact False.elim (fresh seen)
          · exact later
        exact ih r' children expanded later
      · simp only [seen, ↓reduceIte] at expanded
        cases headEdge : e.physical row head with
        | error error => simp [headEdge] at expanded
        | ok hp =>
          simp only [headEdge] at expanded
          cases headOwner : policy e q.mode b hp with
          | error error => simp [headOwner] at expanded
          | ok hr =>
            simp only [headOwner] at expanded
            cases allocated : pushReserve limits b r' with
            | error error => simp [allocated] at expanded
            | ok r'' =>
              simp only [allocated] at expanded
              cases later : expandRows e q limits b row rest r'' with
              | error error => simp [later] at expanded
              | ok pair =>
                rcases pair with ⟨final',children'⟩
                simp only [later, Except.ok.injEq, Prod.mk.injEq] at expanded
                rcases expanded with ⟨rfl,rfl⟩
                rcases List.mem_cons.mp member with same | remaining
                · subst head
                  have peq := Except.ok.inj (headEdge.symm.trans edge)
                  subst hp
                  have req := Except.ok.inj (headOwner.symm.trans owner)
                  subst hr
                  exact List.mem_append.mpr (Or.inr (by simp))
                · exact List.mem_append.mpr (Or.inl (ih r'' children' later remaining))

/- Genuine generated-child reflection: membership is derived from the source
cell loop and its primitive/resource success, not assumed Present. The general
multi-edge Checked-path converse is still a separate open obligation. -/
omit [DecidableEq S] in
theorem generated_physical_target_reflected (e : Readers S T) (q : Query) (limits : Limits)
    (b : Branch S T) (row : Nat) (cs : List Cell) (r final : Resource)
    (children pending results : List (Branch S T))
    (expanded : expandRows e q limits b row cs r = .ok (final,children))
    (c : Cell) (member : c ∈ cs) (fresh : c.target ∉ b.seen)
    (p : ProviderNativeContextR57.Physical T) (edge : e.physical row c = .ok p)
    (root : Option Nat) (owner : policy e q.mode b p = .ok root)
    (terminal : c.target = q.target)
    (completed : Run e q limits (.live ⟨final,children ++ pending,[],.pop⟩) (.success results)) :
    child b c.target (.physical p) root ∈ results := by
  have generated := row_expansion_contains_selected_child e q limits b row cs r final children
    expanded c member fresh p edge root owner
  exact successful_exhaustion_complete_for_queued_targets e q limits _ results completed _ terminal
    (Or.inl (List.mem_append.mpr (Or.inl generated)))


/-- The old soundness invariant alone permits omitted expansion members.
This local state is not claimed reachable from the proper initialized search.
It refutes using that invariant as a substitute for the missing converse. -/
theorem soundness_invariant_allows_omitted_candidate :
    Invariant fixtureReaders fixtureCatchQuery
      (.live ⟨resourceAt 0 8,[],[],.physical fixtureBranch 6 []⟩) ∧
    Checked fixtureReaders fixtureCatchQuery fixtureChild ∧
    Run fixtureReaders fixtureCatchQuery nativeLimits
      (.live ⟨resourceAt 0 8,[],[],.physical fixtureBranch 6 []⟩) (.success []) ∧
    fixtureChild ∉ ([] : List (Branch Nat Nat)) := by
  refine ⟨?_,?_,?_,by simp⟩
  · refine ⟨?_,?_,?_⟩
    · intro x impossible; cases impossible
    · intro x impossible; cases impossible
    · exact ⟨Checked.root,rfl,fixtureBounds,rfl,by simp⟩
  · exact .physical (b := fixtureBranch) (c := fixtureCell) (p := fixtureEdge) (root := none) (bounds := fixtureBounds) Checked.root rfl rfl (by decide) (by decide) rfl rfl
  · exact .next (.move .rowDone) (.next (.move .done) (.refl _))

end YulangClosure.ReachedSlotSearchR58
