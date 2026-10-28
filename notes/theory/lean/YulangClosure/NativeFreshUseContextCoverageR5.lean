import YulangClosure.Contracts

/-!
R5 CANDIDATE TERMS, CONSTRUCTED BUT UNCHECKED. The contract forbids Lean/Lake
and axiom queries before independent acceptance and primary authorization.
No R3/R4 theorem or other concurrent R5 result is imported.

Source interpretation: candidate_context.rs:1566--1677 (successful rename
branches), :2629--2661 (constructor interning), :3062--3101 (relation
interning), :3297--3303 (effective root), :1167--1237 (readback selection),
:3799--3887 (discharge), :4278--4294 (FreshUse transport).

This file makes the payload and storage actions explicit, instead of treating
children as an arbitrary supplied traversal. It also separates immutable raw
relation keys, mutable discharge state, and selection through Transport edges.
Its whole Rust-driver interpretation and restoration observation obligation
remain OPEN. An abstract configuration below is deliberately NOT asserted
reachable from a source program. No theorem here closes InferenceSoundness.
-/
namespace YulangClosure.NativeFreshUseContextCoverageR5

inductive Expr where
  | prefixLeft (weight input : Nat)
  | suffixRightPops (input weight : Nat)
  | swap (input : Nat)
  | bothFromRight (input certificate : Nat)
  | replay (lower upper : Nat)
  | withoutLeftFilter (input : Nat)
  deriving DecidableEq

def Expr.children : Expr → List Nat
  | .prefixLeft _ input | .suffixRightPops input _ | .swap input
  | .bothFromRight input _ | .withoutLeftFilter input => [input]
  | .replay lower upper => [lower, upper]

def Expr.weight : Expr → Option Nat
  | .prefixLeft weight _ | .suffixRightPops _ weight => some weight
  | _ => none

abbrev Map := Nat → Option Nat
abbrev Table := Nat → Option Expr

def put {α : Type} (table : Nat → Option α) (key : Nat) (value : α) :
    Nat → Option α := fun other => if other = key then some value else table other

theorem put_same {α : Type} (table : Nat → Option α) (key : Nat) (value : α) :
    put table key value key = some value := by simp [put]

theorem put_other {α : Type} (table : Nat → Option α) (key other : Nat) (value : α)
    (different : other ≠ key) : put table key value other = table other := by
  simp [put, different]

/-- The outer Option distinguishes bad handles from logical identity. A
successful source read is bounded by the original checkpoint, even after append. -/
def readAt (cutoff : Nat) (table : Table) (id : Nat) : Option (Option Expr) :=
  if id > cutoff then none else if id = 0 then some none else
    (table id).map some

/-- Mirrors weight(token): validate original and replacement payload indices,
and require the caller's exact substitution. No weight-selection conclusion
is supplied as a premise. -/
def weightCopy (valid : Nat → Bool) (weights : Map) (token : Nat) : Option Nat := do
  if !valid token then none else
    let copy ← weights token
    if valid copy then some copy else none

def rebuild (remap weights certificates : Map) (validWeight : Nat → Bool) :
    Option Expr → Option (Option Expr)
  | none => some none
  | some (.prefixLeft token input) => do
      let copy ← weightCopy validWeight weights token
      let child ← remap input
      pure (some (.prefixLeft copy child))
  | some (.suffixRightPops input token) => do
      let child ← remap input
      let copy ← weightCopy validWeight weights token
      pure (some (.suffixRightPops child copy))
  | some (.swap input) => do
      let child ← remap input
      pure (some (.swap child))
  | some (.bothFromRight input certificate) => do
      let child ← remap input
      let copiedCertificate ← certificates certificate
      pure (some (.bothFromRight child copiedCertificate))
  | some (.replay lower upper) => do
      let lowerCopy ← remap lower
      let upperCopy ← remap upper
      pure (some (.replay lowerCopy upperCopy))
  | some (.withoutLeftFilter input) => do
      let child ← remap input
      pure (some (.withoutLeftFilter child))

theorem rebuild_identity (remap weights certificates : Map) (valid : Nat → Bool) :
    rebuild remap weights certificates valid none = some none := rfl

theorem rebuild_prefix (remap weights certificates : Map) (valid : Nat → Bool)
    (weight input copiedWeight copiedInput : Nat)
    (payload : weightCopy valid weights weight = some copiedWeight)
    (child : remap input = some copiedInput) :
    rebuild remap weights certificates valid (some (.prefixLeft weight input)) =
      some (some (.prefixLeft copiedWeight copiedInput)) := by
  simp [rebuild, payload, child]

theorem rebuild_suffix (remap weights certificates : Map) (valid : Nat → Bool)
    (input weight copiedInput copiedWeight : Nat)
    (child : remap input = some copiedInput)
    (payload : weightCopy valid weights weight = some copiedWeight) :
    rebuild remap weights certificates valid (some (.suffixRightPops input weight)) =
      some (some (.suffixRightPops copiedInput copiedWeight)) := by
  simp [rebuild, payload, child]

theorem rebuild_swap (remap weights certificates : Map) (valid : Nat → Bool)
    (input copiedInput : Nat) (child : remap input = some copiedInput) :
    rebuild remap weights certificates valid (some (.swap input)) =
      some (some (.swap copiedInput)) := by simp [rebuild, child]

theorem rebuild_both (remap weights certificates : Map) (valid : Nat → Bool)
    (input certificate copiedInput copiedCertificate : Nat)
    (child : remap input = some copiedInput)
    (token : certificates certificate = some copiedCertificate) :
    rebuild remap weights certificates valid (some (.bothFromRight input certificate)) =
      some (some (.bothFromRight copiedInput copiedCertificate)) := by
  simp [rebuild, child, token]

theorem rebuild_replay (remap weights certificates : Map) (valid : Nat → Bool)
    (lower upper lowerCopy upperCopy : Nat)
    (one : remap lower = some lowerCopy) (two : remap upper = some upperCopy) :
    rebuild remap weights certificates valid (some (.replay lower upper)) =
      some (some (.replay lowerCopy upperCopy)) := by simp [rebuild, one, two]

theorem rebuild_without (remap weights certificates : Map) (valid : Nat → Bool)
    (input copiedInput : Nat) (child : remap input = some copiedInput) :
    rebuild remap weights certificates valid (some (.withoutLeftFilter input)) =
      some (some (.withoutLeftFilter copiedInput)) := by simp [rebuild, child]

/-- FreshUse passes an empty certificate map. BothFromRight remains a represented
constructor; successful FreshUse cannot rebuild it under that argument. -/
theorem fresh_both_fails (remap weights : Map) (valid : Nat → Bool)
    (input certificate : Nat) :
    rebuild remap weights (fun _ => none) valid
      (some (.bothFromRight input certificate)) = none := by
  cases child : remap input <;> simp [rebuild, child]

structure Store where
  table : Table
  next : Nat

/-- Explicit successful interner actions, including reuse of an OLD ID.
There is deliberately no disjoint-output or injectivity hypothesis. Identifying
the native context_keys lookup with these table facts requires the native
table/interner coherence invariant; that interpretation is not claimed here. -/
inductive Intern (expression : Expr) : Store → Nat → Store → Prop where
  | reuse (store : Store) (id : Nat) (positive : 0 < id)
      (found : store.table id = some expression) :
      Intern expression store id store
  | append (store : Store) (positive : 0 < store.next)
      (fresh : store.table store.next = none)
      (missing : ∀ id, store.table id ≠ some expression) :
      Intern expression store store.next
        ⟨put store.table store.next expression, store.next + 1⟩

theorem intern_reads {expression : Expr} {before after : Store} {id : Nat}
    (step : Intern expression before id after) : after.table id = some expression := by
  cases step with
  | reuse _ _ _ found => exact found
  | append => exact put_same _ _ _

theorem intern_old_table {expression : Expr} {before after : Store} {id old : Nat}
    (step : Intern expression before id after) (earlier : old < before.next) :
    after.table old = before.table old := by
  cases step with
  | reuse => rfl
  | append => exact put_other _ _ _ _ (Nat.ne_of_lt earlier)

theorem intern_next {expression : Expr} {before after : Store} {id : Nat}
    (step : Intern expression before id after) : before.next ≤ after.next := by
  cases step <;> simp

/-- The source-read cutoff is a genuine read/write frame: output allocation
cannot retroactively make an invalid source handle valid. -/
theorem intern_checkpoint_read {expression : Expr} {before after : Store} {copy : Nat}
    (step : Intern expression before copy after) (cutoff id : Nat)
    (room : cutoff < before.next) :
    readAt cutoff after.table id = readAt cutoff before.table id := by
  by_cases outside : id > cutoff
  · simp [readAt, outside]
  · have earlier : id < before.next := Nat.lt_of_le_of_lt (Nat.le_of_not_gt outside) room
    have same := intern_old_table step earlier
    simp only [readAt, same]

/-- Logical ID 0 is never an allocated ContextExpr row. -/
def emitted (expression : Option Expr) (before : Store) (copy : Nat) (after : Store) : Prop :=
  match expression with
  | none => copy = 0 ∧ after = before
  | some node => Intern node before copy after

structure Scan where
  roots : List Nat
  pending : List (Nat × Bool)
  verified : List Nat
  remap : Map
  store : Store

def schedule (children verified : List Nat) : List (Nat × Bool) :=
  (children.filter (fun child => !(decide (child ∈ verified)))).map (fun child => (child, false))

def childrenOf : Option Expr → List Nat
  | none => []
  | some node => node.children

/-- Every constructor corresponds to an actual successful branch. Resource
reservation success is erased, while all semantic reads are retained. The
existing-map branch validates a target against the ORIGINAL cutoff. -/
inductive RenameStep (cutoff : Nat) (weights certificates : Map) (valid : Nat → Bool) :
    Scan → Scan → Prop where
  | root (root : Nat) (roots verified : List Nat) (remap : Map) (store : Store) :
      RenameStep cutoff weights certificates valid
        ⟨root :: roots, [], verified, remap, store⟩
        ⟨roots, [(root, false)], verified, remap, store⟩
  | skip (state : Scan) (id : Nat) (ready : Bool) (rest : List (Nat × Bool))
      (pending : state.pending = (id, ready) :: rest) (seen : id ∈ state.verified) :
      RenameStep cutoff weights certificates valid state {state with pending := rest}
  | descend (state : Scan) (id : Nat) (rest : List (Nat × Bool)) (node : Option Expr)
      (pending : state.pending = (id, false) :: rest) (unseen : id ∉ state.verified)
      (read : readAt cutoff state.store.table id = some node)
      (nonempty : childrenOf node ≠ [])
      (decreases : ∀ child ∈ childrenOf node, child < id) :
      RenameStep cutoff weights certificates valid state
        {state with pending := schedule (childrenOf node) state.verified ++ (id, true) :: rest}
  | existing (state : Scan) (id copy : Nat) (ready : Bool) (rest : List (Nat × Bool))
      (node renamed : Option Expr)
      (pending : state.pending = (id, ready) :: rest) (unseen : id ∉ state.verified)
      (read : readAt cutoff state.store.table id = some node)
      (decreases : ∀ child ∈ childrenOf node, child < id)
      (finish : ready = true ∨ childrenOf node = [])
      (rebuilt : rebuild state.remap weights certificates valid node = some renamed)
      (mapped : state.remap id = some copy)
      (actual : readAt cutoff state.store.table copy = some renamed) :
      RenameStep cutoff weights certificates valid state
        {state with pending := rest, verified := id :: state.verified}
  | publish (state : Scan) (id copy : Nat) (ready : Bool) (rest : List (Nat × Bool))
      (node renamed : Option Expr) (after : Store)
      (pending : state.pending = (id, ready) :: rest) (unseen : id ∉ state.verified)
      (read : readAt cutoff state.store.table id = some node)
      (decreases : ∀ child ∈ childrenOf node, child < id)
      (finish : ready = true ∨ childrenOf node = [])
      (rebuilt : rebuild state.remap weights certificates valid node = some renamed)
      (absent : state.remap id = none) (interned : emitted renamed state.store copy after) :
      RenameStep cutoff weights certificates valid state
        {state with pending := rest, verified := id :: state.verified,
          remap := put state.remap id copy, store := after}

def ExactVerified (state : Scan) : Prop :=
  ∀ key, (∃ value, state.remap key = some value) ↔ key ∈ state.verified

/-- Local map-domain invariant derived from the actual insert/validation writes.
No seed-inclusion, reachability-domain or observability assumption is used. -/
theorem step_exact_verified {cutoff : Nat} {weights certificates : Map} {valid : Nat → Bool}
    {before after : Scan} (step : RenameStep cutoff weights certificates valid before after)
    (exactBefore : ExactVerified before) : ExactVerified after := by
  cases step with
  | root root roots verified remap store => exact exactBefore
  | skip state id ready rest pending seen => exact exactBefore
  | descend state id rest node pending unseen read nonempty decreases => exact exactBefore
  | existing state id copy ready rest node renamed pending unseen read decreases finish rebuilt mapped actual =>
      have impossible : id ∈ state.verified := (exactBefore id).mp ⟨copy, mapped⟩
      exact False.elim (unseen impossible)
  | publish state id copy ready rest node renamed store pending unseen read decreases finish rebuilt absent interned =>
      intro key
      by_cases equal : key = id
      · subst key
        simp [put]
      · simpa [put, equal] using exactBefore key

inductive RenameRun (cutoff : Nat) (weights certificates : Map) (valid : Nat → Bool) :
    Scan → Scan → Prop where
  | refl (state : Scan) : RenameRun cutoff weights certificates valid state state
  | snoc {first middle last : Scan} :
      RenameRun cutoff weights certificates valid first middle →
      RenameStep cutoff weights certificates valid middle last →
      RenameRun cutoff weights certificates valid first last

theorem run_exact_verified {cutoff : Nat} {weights certificates : Map} {valid : Nat → Bool}
    {first last : Scan} (run : RenameRun cutoff weights certificates valid first last)
    (initial : ExactVerified first) : ExactVerified last := by
  induction run with
  | refl => exact initial
  | snoc prefix step ih => exact step_exact_verified step ih

theorem fresh_initial_exact (roots : List Nat) (store : Store) :
    ExactVerified ⟨roots, [], [], fun _ => none, store⟩ := by
  intro key
  simp

/-- In a fresh run, the seeded-map validation branch is unreachable: every
already mapped key is verified and therefore taken by the earlier skip. -/
theorem fresh_no_unverified_seed {state : Scan} (invariant : ExactVerified state)
    {id copy : Nat} (unseen : id ∉ state.verified) (mapped : state.remap id = some copy) :
    False := unseen ((invariant id).mp ⟨copy, mapped⟩)

/-! Restoration footprint. Full RelationKey includes canonical endpoint pair,
raw context, source set and scoped flow. Canonical-owner changes do not mutate
that existing key. Interning may reuse it. Discharge is a separate table. -/
structure RelationKey where
  pair : Nat
  context : Nat
  sources : Nat
  scoped : Nat
  deriving DecidableEq

structure Evidence where
  context : Table
  relation : Nat → RelationKey
  discharged : Nat → Bool
  residual : Nat → Option Nat
  transport : Nat → Nat → Prop

def postCheck (state : Evidence) (relation : Nat) : Nat :=
  if state.discharged relation then (state.residual relation).getD 0
  else (state.relation relation).context

def discharge (state : Evidence) (relation residual : Nat) : Evidence :=
  {state with
    discharged := fun other => if other = relation then true else state.discharged other
    residual := if residual = 0 then state.residual else put state.residual relation residual}

theorem discharge_raw_key (state : Evidence) (relation residual other : Nat) :
    (discharge state relation residual).relation other = state.relation other := rfl

theorem discharge_context (state : Evidence) (relation residual id : Nat) :
    (discharge state relation residual).context id = state.context id := rfl

theorem discharge_effective_nonzero (state : Evidence) (relation residual : Nat)
    (nonzero : residual ≠ 0) : postCheck (discharge state relation residual) relation = residual := by
  simp [postCheck, discharge, nonzero, put]

/-- A fresh discharge cannot inherit a stale residual: that premise belongs to
the native discharged/residual journaling invariant, not to context storage. -/
theorem discharge_effective_zero (state : Evidence) (relation : Nat)
    (noOldResidual : state.residual relation = none) :
    postCheck (discharge state relation 0) relation = 0 := by
  simp [postCheck, discharge, noOldResidual]

theorem discharge_other_effective (state : Evidence) (relation residual other : Nat)
    (different : other ≠ relation) :
    postCheck (discharge state relation residual) other = postCheck state other := by
  by_cases zero : residual = 0 <;> simp [postCheck, discharge, zero, different, put]

/-- Only the field reads used by retained_input's selection loop. This is the
least closure projection; the native finite-mask loop interpretation is OPEN. -/
inductive SelectedRelation (state : Evidence) (roots : List Nat) : Nat → Prop where
  | root {id : Nat} : id ∈ roots → SelectedRelation state roots id
  | parent {child parent : Nat} : SelectedRelation state roots child →
      state.transport child parent → SelectedRelation state roots parent
  | child {child parent : Nat} : SelectedRelation state roots parent →
      state.transport child parent → SelectedRelation state roots child

inductive SelectedContext (state : Evidence) (roots : List Nat) : Nat → Prop where
  | relation {relation : Nat} : SelectedRelation state roots relation →
      SelectedContext state roots (state.relation relation).context
  | child {parent child : Nat} {node : Expr} : SelectedContext state roots parent →
      state.context parent = some node → child ∈ node.children →
      SelectedContext state roots child

def StoredSelected (state : Evidence) (roots : List Nat) (id : Nat) : Prop :=
  id ≠ 0 ∧ SelectedContext state roots id

def SelectedWeight (state : Evidence) (roots : List Nat) (weight : Nat) : Prop :=
  ∃ id node, StoredSelected state roots id ∧ state.context id = some node ∧
    node.weight = some weight

theorem identity_not_stored (state : Evidence) (roots : List Nat) :
    ¬ StoredSelected state roots 0 := by
  intro selected
  exact selected.1 rfl

theorem selected_relation_discharge_iff (state : Evidence) (roots : List Nat)
    (relation residual id : Nat) :
    SelectedRelation (discharge state relation residual) roots id ↔ SelectedRelation state roots id := by
  constructor
  · intro selected
    induction selected with
    | root member => exact .root member
    | parent selected edge ih => exact .parent ih edge
    | child selected edge ih => exact .child ih edge
  · intro selected
    induction selected with
    | root member => exact .root member
    | parent selected edge ih => exact .parent ih edge
    | child selected edge ih => exact .child ih edge

theorem selected_context_discharge_iff (state : Evidence) (roots : List Nat)
    (relation residual id : Nat) :
    SelectedContext (discharge state relation residual) roots id ↔ SelectedContext state roots id := by
  constructor
  · intro selected
    induction selected with
    | relation selected =>
        exact .relation ((selected_relation_discharge_iff state roots relation residual _).mp selected)
    | child selected found member ih => exact .child ih found member
  · intro selected
    induction selected with
    | relation selected =>
        exact .relation ((selected_relation_discharge_iff state roots relation residual _).mpr selected)
    | child selected found member ih => exact .child ih found member

/-- A required weight follows from an attached raw root, without assuming that
the weight or child was already selected. -/
theorem attached_prefix_weight (state : Evidence) (roots : List Nat)
    (relation root weight input : Nat) (member : relation ∈ roots)
    (raw : (state.relation relation).context = root) (nonzero : root ≠ 0)
    (node : state.context root = some (.prefixLeft weight input)) :
    SelectedWeight state roots weight := by
  refine ⟨root, .prefixLeft weight input, ⟨nonzero, ?_⟩, node, rfl⟩
  rw [← raw]
  exact .relation (.root member)

/-- Transport includes a retained parent irrespective of its discharge status. -/
theorem transport_keeps_parent_raw (state : Evidence) (roots : List Nat)
    (child parent : Nat) (member : child ∈ roots) (edge : state.transport child parent) :
    SelectedContext state roots (state.relation parent).context :=
  .relation (.parent (.root member) edge)

/-- Full-key relation reuse identifies CONTEXT fields. Equality only of the
canonical endpoint pair cannot justify this result. -/
theorem reused_key_context (first second : RelationKey) (same : first = second) :
    first.context = second.context := congrArg RelationKey.context same

/-! A concrete local mismatch of two read APIs, not a reachable trace and not
a Yulang counterexample. Even append-only context storage and unchanged raw
keys do not make later effective roots equal their pre-discharge roots. -/
def mismatch : Evidence :=
  { context := fun id => if id = 1 then some (.prefixLeft 0 0) else none
    relation := fun _ => ⟨0, 1, 0, 0⟩
    discharged := fun _ => false
    residual := fun _ => none
    transport := fun _ _ => False }

theorem effective_root_can_change :
    postCheck mismatch 0 = 1 ∧ postCheck (discharge mismatch 0 0) 0 = 0 := by
  simp [postCheck, mismatch, discharge]

theorem raw_root_survives_that_change :
    SelectedContext (discharge mismatch 0 0) [0] 1 := by
  change SelectedContext (discharge mismatch 0 0) [0]
    ((discharge mismatch 0 0).relation 0).context
  exact .relation (.root (by simp))

/-! Parent application: these declarations reduce local payload reconstruction
and a PURE DISCHARGE selection frame. They do not instantiate SourceProblem,
its sourceJudgment/sameScoped, or OriginalSourceInterpretation.Inputs.

First remaining native premise: before every captured bound's later
begin_candidate_fresh_bound, determine which original parent relations earlier
restoration children can discharge (including full-key interning aliases).
For any root change, show the originally prepared image is still attached to
a relation selected by the authentic final consumer, or supply a reachable
successful execution where it is not. The already-read raw parent context does
not by itself equal that separately prepared image when weights changed.

Also OPEN: interpretation of the full successful Rust rename driver into
RenameRun, transitive source-reachability exact domain, and interpretation of
the native mask loop into SelectedContext. No proposition definition or these
candidate terms establish any of those premises. Owner: primary native/proof
integration lane. InferenceSoundness, A/B, effect hygiene, principality,
termination and production promotion remain OPEN.
-/
end YulangClosure.NativeFreshUseContextCoverageR5
