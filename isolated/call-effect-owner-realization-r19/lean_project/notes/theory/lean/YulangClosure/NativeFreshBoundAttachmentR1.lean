import Std
import YulangClosure.Contracts

/-!
PROVISIONAL, CONSTRUCTED BUT NOT CHECKED. R1 is ineligible for acceptance after
the pin-order deviation recorded by Amendment 01. This is a successful local
action projection, not an interpretation of every successful native execution.

Native owners: candidate_scheme.rs prepare_candidate_fresh_use and
begin_candidate_fresh_bound; candidate_context.rs relation_with_scoped,
candidate_context_fresh_transport_scoped, retained_input, post_check_context;
candidate_effect.rs candidate_bound_origin_with_evidence. Full-key lookup below
derives the stored raw Context; it does not assume the interner lookup law.

The final theorem isolates a necessary condition for missing preparation-time
images. It does not establish the required temporal restoration invariant.
All original source, inference, effect and production gates remain OPEN.
-/
namespace YulangClosure.NativeFreshBoundAttachmentR1

def rowAt {α : Type} : List α → Nat → Option α
  | [], _ => none
  | head :: _, 0 => some head
  | _ :: rest, n + 1 => rowAt rest n

def findKey {α : Type} [DecidableEq α] : List α → α → Option Nat
  | [], _ => none
  | head :: rest, key =>
      if head = key then some 0 else (findKey rest key).map Nat.succ

theorem findKey_sound {α : Type} [DecidableEq α] (rows : List α)
    (key : α) (index : Nat) (found : findKey rows key = some index) :
    rowAt rows index = some key := by
  induction rows generalizing index with
  | nil => simp [findKey] at found
  | cons head rest ih =>
      by_cases equal : head = key
      · simp [findKey, equal] at found
        subst index
        simp [rowAt, equal]
      · cases next : findKey rest key with
        | none => simp [findKey, equal, next] at found
        | some n =>
            simp [findKey, equal, next] at found
            subst index
            exact ih n next

theorem rowAt_append_length {α : Type} (rows : List α) (key : α) :
    rowAt (rows ++ [key]) rows.length = some key := by
  induction rows with
  | nil => rfl
  | cons head rest ih => simpa [rowAt] using ih

theorem rowAt_append_old {α : Type} (rows extra : List α) (index : Nat)
    (key : α) (old : rowAt rows index = some key) :
    rowAt (rows ++ extra) index = some key := by
  induction rows generalizing index with
  | nil => simp [rowAt] at old
  | cons head rest ih =>
      cases index with
      | zero => exact old
      | succ n => exact ih n old

/-- Successful reuse or append, including full-key aliasing. -/
def intern {α : Type} [DecidableEq α] (rows : List α) (key : α) : List α × Nat :=
  match findKey rows key with
  | some id => (rows, id)
  | none => (rows ++ [key], rows.length)

theorem intern_raw {α : Type} [DecidableEq α] (rows : List α) (key : α) :
    rowAt (intern rows key).1 (intern rows key).2 = some key := by
  cases found : findKey rows key with
  | none => simpa [intern, found] using rowAt_append_length rows key
  | some index => simpa [intern, found] using findKey_sound rows key index found

theorem intern_preserves {α : Type} [DecidableEq α]
    (rows : List α) (key old : α) (index : Nat)
    (stored : rowAt rows index = some old) :
    rowAt (intern rows key).1 index = some old := by
  cases found : findKey rows key with
  | none => simpa [intern, found] using rowAt_append_old rows [key] index old stored
  | some id => simpa [intern, found] using stored

structure BoundKey where
  owner : Nat
  positive : Bool
  item : Nat
  deriving DecidableEq

/-- pair is the encoded canonical TypedPairKey; sources and scoped encode the
interned optional source set and ScopedFlowId. Use origin is NOT in this key. -/
structure RelationKey where
  pair : Nat
  context : Nat
  sources : Option Nat
  scoped : Nat
  deriving DecidableEq

/-- Multiplicity is an occurrence index, not a set of roots or parent IDs. -/
structure Capture where
  route : Nat
  index : Nat
  antecedent : Nat
  useOrigin : Nat
  sourceBound : BoundKey
  parent : Nat
  preparedRoot : Nat

structure Transport where
  capture : Capture
  destination : BoundKey
  child : Nat

structure Attachment where
  bound : BoundKey
  relation : Nat

structure Admission where
  capture : Capture
  destination : BoundKey
  mapped : Nat
  relation : Nat

structure State where
  relations : List RelationKey
  discharged : Nat → Bool
  residual : Nat → Option Nat
  transports : List Transport
  attachments : List Attachment
  admissions : List Admission

def effective (state : State) (relation : Nat) : Option Nat :=
  if state.discharged relation then some ((state.residual relation).getD 0)
  else (rowAt state.relations relation).map RelationKey.context

/-- Pure discharge/residual writes preserve allocated raw Contexts. -/
def discharge (state : State) (relation residual : Nat) : State :=
  { state with
    discharged := fun old => if old = relation then true else state.discharged old
    residual := fun old => if old = relation then
      (if residual = 0 then state.residual old else some residual)
      else state.residual old }

theorem discharge_raw (state : State) (relation residual index : Nat) :
    rowAt (discharge state relation residual).relations index =
      rowAt state.relations index := rfl

/-- This projection records the end of a successful physical admission. In
scoped mode `admitted` is the transported child; in unscoped mode the ordinary
bound constructor may choose another relation. Both are registered on `to`.
The latter distinction is essential: admission.relation need not equal mapped.
Physical append/readback and restoration completion are NOT interpreted here. -/
def publish (state : State) (capture : Capture) (to : BoundKey)
    (key : RelationKey) (admitted : Nat) : State × Nat :=
  let result := intern state.relations key
  ({ state with relations := result.1
                transports := ⟨capture, to, result.2⟩ :: state.transports
                attachments := ⟨to, result.2⟩ :: ⟨to, admitted⟩ :: state.attachments
                admissions := ⟨capture, to, result.2, admitted⟩ :: state.admissions }, result.2)

/-- Membership closure of the native borrowed relation mask. Native replay
and view-driven closure add more rows; this subrelation omits those additions.
No seed-membership premise is supplied: seeds are computed from admissions. -/
inductive Selected (state : State) : Nat → Prop
  | admission (record) : record ∈ state.admissions → Selected state record.relation
  | sameBound (one two) : one ∈ state.attachments → two ∈ state.attachments →
      one.bound = two.bound → Selected state one.relation → Selected state two.relation
  | transportParent (record) : record ∈ state.transports →
      Selected state record.child → Selected state record.capture.parent
  | transportChild (record) : record ∈ state.transports →
      Selected state record.capture.parent → Selected state record.child

/-- Logical identity is observable without a fabricated physical Context row.
For nonidentity, this is a relation-root fragment of contexts() readback. -/
def Observed (state : State) (context : Nat) : Prop :=
  context = 0 ∨ ∃ relation key, Selected state relation ∧
    rowAt state.relations relation = some key ∧ key.context = context

theorem published_child_selected (state : State) (capture : Capture)
    (to : BoundKey) (key : RelationKey) (admitted : Nat) :
    Selected (publish state capture to key admitted).1
      (publish state capture to key admitted).2 := by
  let child := (intern state.relations key).2
  let record : Admission := ⟨capture, to, child, admitted⟩
  have seed : Selected (publish state capture to key admitted).1 admitted :=
    Selected.admission record (by simp [publish, record, child])
  exact Selected.sameBound ⟨to, admitted⟩ ⟨to, child⟩
    (by simp [publish]) (by simp [publish, child]) rfl seed

theorem published_raw (state : State) (capture : Capture)
    (to : BoundKey) (key : RelationKey) (admitted : Nat) :
    rowAt (publish state capture to key admitted).1.relations
      (publish state capture to key admitted).2 = some key :=
  intern_raw state.relations key

theorem published_context_observed (state : State) (capture : Capture)
    (to : BoundKey) (key : RelationKey) (admitted : Nat) :
    Observed (publish state capture to key admitted).1 key.context := by
  exact Or.inr ⟨(publish state capture to key admitted).2, key,
    published_child_selected state capture to key admitted,
    published_raw state capture to key admitted, rfl⟩

structure FreshResult where
  state : State
  child : Nat
  admissionRoot : Nat
  admissionImage : Nat

/-- Lookup failure is preserved. No identity fallback or all-image premise.
This omits native guards, scope interning, attachments bundles, physical
emission and restoration, and therefore is only a local successful projection. -/
def beginFresh (state : State) (capture : Capture) (to : BoundKey)
    (pair : Nat) (sources : Option Nat) (scoped admitted : Nat)
    (remap : Nat → Option Nat) : Option FreshResult :=
  match effective state capture.parent with
  | none => none
  | some root => match remap root with
    | none => none
    | some image =>
        let output := publish state capture to ⟨pair, image, sources, scoped⟩ admitted
        some ⟨output.1, output.2, root, image⟩

theorem beginFresh_current_image (state : State) (capture : Capture)
    (to : BoundKey) (pair : Nat) (sources : Option Nat) (scoped admitted : Nat)
    (remap : Nat → Option Nat) (output : FreshResult)
    (success : beginFresh state capture to pair sources scoped admitted remap = some output) :
    effective state capture.parent = some output.admissionRoot ∧
    remap output.admissionRoot = some output.admissionImage ∧
    rowAt output.state.relations output.child =
      some ⟨pair, output.admissionImage, sources, scoped⟩ ∧
    Selected output.state output.child ∧
    Observed output.state output.admissionImage := by
  cases root : effective state capture.parent with
  | none => simp [beginFresh, root] at success
  | some current =>
      cases image : remap current with
      | none => simp [beginFresh, root, image] at success
      | some copied =>
          simp only [beginFresh, root, image] at success
          cases success
          exact ⟨root, image,
            published_raw state capture to ⟨pair, copied, sources, scoped⟩ admitted,
            published_child_selected state capture to ⟨pair, copied, sources, scoped⟩ admitted,
            published_context_observed state capture to ⟨pair, copied, sources, scoped⟩ admitted⟩

/-- These map reads are precisely the successful preparation and later native
lookup branches. Equality of the reads or observability is not a hypothesis.
The alternative is the exact still-open temporal branch, NOT a counterexample.
The key's Context is built from the later lookup image; no supplied exact-map
relation or supplied interner law is used. -/
theorem prepared_observed_or_temporal_change
    (state : State) (capture : Capture) (to : BoundKey)
    (pair : Nat) (sources : Option Nat) (scoped admitted : Nat)
    (remap : Nat → Option Nat) (laterRoot preparedImage laterImage : Nat)
    (prepared : remap capture.preparedRoot = some preparedImage)
    (later : remap laterRoot = some laterImage) :
    let key : RelationKey := ⟨pair, laterImage, sources, scoped⟩
    Observed (publish state capture to key admitted).1 preparedImage ∨
      laterRoot ≠ capture.preparedRoot := by
  by_cases same : laterRoot = capture.preparedRoot
  · left
    have images : preparedImage = laterImage := by
      rw [same, prepared] at later
      exact Option.some.inj later
    rw [images]
    exact published_context_observed state capture to
      ⟨pair, laterImage, sources, scoped⟩ admitted
  · exact Or.inr same

/- No theorem here instantiates SourceProblem.InferenceSoundness. First open
native premise: interpret every admitted restoration step and prove that an
effective-root change before a later admission either preserves observation
of that same bound's prepared image, or yields an authentic completed native
counterexample. Prefix/Suffix/Swap/Both/Replay/Without Context renaming, all
image observability, complete readback-loop interpretation, completion and
source/native correspondence are deliberately NOT asserted by these terms.
-/
end YulangClosure.NativeFreshBoundAttachmentR1
