import YulangClosure.WholePublicationResidualR53

/-!
R54 finite owner-qualified interpretation. Native keys are retained whole;
ordinals are local inventory positions, never global or canonical identities.
The finite mathematics below is not a theorem identifying Rust borrows with
Lean values. No FaithfulExtraction or equivalent whole-target premise is used.
-/
namespace YulangClosure.OwnedResidualProjectionR54

variable {State Batch Kind Key Value : Type}

/-- State identity is distinct from the shared collected batch identity. The
State parameter denotes the identity of the live borrowed object. -/
structure Owner (State Batch : Type) where
  state : State
  batch : Batch
  deriving DecidableEq

structure Handle (State Batch Kind : Type) where
  owner : Owner State Batch
  kind : Kind
  ordinal : Nat
  deriving DecidableEq

/-- A finite mathematical interpretation of an owning collection. Keys are
complete typed native keys, not their erased numeric ordinals. No candidate
predicate is applied while constructing this inventory. -/
structure Table (State Batch Kind Key Value : Type) where
  owner : Owner State Batch
  kind : Kind
  entries : List (Key × Value)

def keys (table : Table State Batch Kind Key Value) : List Key := table.entries.map Prod.fst

def locate [DecidableEq Key] (key : Key) : List Key → Option Nat
  | [] => none
  | head :: rest => if key = head then some 0 else (locate key rest).map Nat.succ

theorem locate_sound [DecidableEq Key] (key : Key) (xs : List Key) (index : Nat)
    (found : locate key xs = some index) : xs[index]? = some key := by
  induction xs generalizing index with
  | nil => simp [locate] at found
  | cons head rest ih =>
    by_cases same : key = head
    · subst key
      simp [locate] at found
      subst index
      rfl
    · cases tail : locate key rest with
      | none => simp [locate, same, tail] at found
      | some n =>
        simp [locate, same, tail] at found
        subst index
        exact ih n tail

theorem locate_coverage [DecidableEq Key] (key : Key) (xs : List Key) (member : key ∈ xs) :
    ∃ index, locate key xs = some index := by
  induction xs with
  | nil => cases member
  | cons head rest ih =>
    by_cases same : key = head
    · exact ⟨0, by simp [locate, same]⟩
    · have later : key ∈ rest := (List.mem_cons.mp member).resolve_left same
      obtain ⟨index, found⟩ := ih later
      exact ⟨index + 1, by simp [locate, same, found]⟩

theorem locate_complete_index [DecidableEq Key] (xs : List Key) (unique : xs.Nodup)
    (index : Nat) (key : Key) (atIndex : xs[index]? = some key) : locate key xs = some index := by
  induction xs generalizing index with
  | nil => simp at atIndex
  | cons head rest ih =>
    have nodup := List.nodup_cons.mp unique
    cases index with
    | zero =>
      have same : head = key := Option.some.inj atIndex
      subst key
      simp [locate]
    | succ index =>
      have inTail : key ∈ rest := List.mem_iff_getElem?.mpr ⟨index, atIndex⟩
      have different : key ≠ head := by
        intro same
        exact nodup.1 (same ▸ inTail)
      have tail := ih nodup.2 index atIndex
      simp [locate, different, tail]

def valid (table : Table State Batch Kind Key Value) : Prop := (keys table).Nodup

instance [DecidableEq Key] (table : Table State Batch Kind Key Value) : Decidable (valid table) := by
  unfold valid; infer_instance

def encodeLocal [DecidableEq Key] (table : Table State Batch Kind Key Value) (key : Key) :
    Option (Handle State Batch Kind) :=
  (locate key (keys table)).map (fun index => ⟨table.owner, table.kind, index⟩)

def encode [DecidableEq State] [DecidableEq Batch] [DecidableEq Kind] [DecidableEq Key]
    (table : Table State Batch Kind Key Value) (owner : Owner State Batch) (kind : Kind) (key : Key) :
    Option (Handle State Batch Kind) :=
  if owner = table.owner ∧ kind = table.kind then encodeLocal table key else none

def decode [DecidableEq State] [DecidableEq Batch] [DecidableEq Kind]
    (table : Table State Batch Kind Key Value) (handle : Handle State Batch Kind) : Option Key :=
  if handle.owner = table.owner ∧ handle.kind = table.kind then
    (table.entries[handle.ordinal]?).map Prod.fst else none

def read [DecidableEq State] [DecidableEq Batch] [DecidableEq Kind]
    (table : Table State Batch Kind Key Value) (handle : Handle State Batch Kind) : Option Value :=
  if handle.owner = table.owner ∧ handle.kind = table.kind then
    (table.entries[handle.ordinal]?).map Prod.snd else none

def nativeRead [DecidableEq Key] (table : Table State Batch Kind Key Value) (key : Key) : Option Value :=
  (locate key (keys table)).bind (fun index => (table.entries[index]?).map Prod.snd)

theorem decode_encode [DecidableEq State] [DecidableEq Batch] [DecidableEq Kind] [DecidableEq Key]
    (table : Table State Batch Kind Key Value) (key : Key) (handle : Handle State Batch Kind)
    (encoded : encode table table.owner table.kind key = some handle) : decode table handle = some key := by
  cases found : locate key (keys table) with
  | none => simp [encode, encodeLocal, found] at encoded
  | some index =>
    have same : (⟨table.owner, table.kind, index⟩ : Handle State Batch Kind) = handle := by
      simpa [encode, encodeLocal, found] using encoded
    subst handle
    have lookup := locate_sound key (keys table) index found
    simpa [decode, keys, List.getElem?_map] using lookup

theorem encode_decode [DecidableEq State] [DecidableEq Batch] [DecidableEq Kind] [DecidableEq Key]
    (table : Table State Batch Kind Key Value) (unique : valid table) (index : Nat) (key : Key)
    (atIndex : (keys table)[index]? = some key) :
    encode table table.owner table.kind key = some ⟨table.owner, table.kind, index⟩ := by
  have found := locate_complete_index (keys table) unique index key atIndex
  simp [encode, encodeLocal, found]

theorem inventory_coverage [DecidableEq State] [DecidableEq Batch] [DecidableEq Kind] [DecidableEq Key]
    (table : Table State Batch Kind Key Value) (key : Key) (member : key ∈ keys table) :
    ∃ handle, encode table table.owner table.kind key = some handle ∧ decode table handle = some key := by
  obtain ⟨index, found⟩ := locate_coverage key (keys table) member
  have encoded : encode table table.owner table.kind key = some ⟨table.owner, table.kind, index⟩ := by
    simp [encode, encodeLocal, found]
  exact ⟨_, encoded, decode_encode table key _ encoded⟩

theorem encoding_distinguishes [DecidableEq State] [DecidableEq Batch] [DecidableEq Kind] [DecidableEq Key]
    (table : Table State Batch Kind Key Value) (a b : Key) (handle : Handle State Batch Kind)
    (ea : encode table table.owner table.kind a = some handle)
    (eb : encode table table.owner table.kind b = some handle) : a = b :=
  Option.some.inj ((decode_encode table a handle ea).symm.trans (decode_encode table b handle eb))

theorem lookup_commutes [DecidableEq State] [DecidableEq Batch] [DecidableEq Kind] [DecidableEq Key]
    (table : Table State Batch Kind Key Value) (key : Key) (handle : Handle State Batch Kind)
    (encoded : encode table table.owner table.kind key = some handle) : read table handle = nativeRead table key := by
  cases found : locate key (keys table) with
  | none => simp [encode, encodeLocal, found] at encoded
  | some index =>
    have same : (⟨table.owner, table.kind, index⟩ : Handle State Batch Kind) = handle := by
      simpa [encode, encodeLocal, found] using encoded
    subst handle
    simp [read, nativeRead, found]

theorem foreign_state_rejected [DecidableEq State] [DecidableEq Batch] [DecidableEq Kind]
    (table : Table State Batch Kind Key Value) (handle : Handle State Batch Kind)
    (foreignState : handle.owner.state ≠ table.owner.state) : read table handle = none ∧ decode table handle = none := by
  have different : handle.owner ≠ table.owner := fun same => foreignState (congrArg Owner.state same)
  simp [read, decode, different]

theorem foreign_kind_rejected [DecidableEq State] [DecidableEq Batch] [DecidableEq Kind]
    (table : Table State Batch Kind Key Value) (handle : Handle State Batch Kind)
    (different : handle.kind ≠ table.kind) : read table handle = none ∧ decode table handle = none := by
  simp [read, decode, different]

/-- Complete keys are checked before a query is allowed to use the table. -/
def covers [DecidableEq Key] (table : Table State Batch Kind Key Value) (required : List Key) : Bool :=
  required.all (fun key => (locate key (keys table)).isSome)

theorem covers_complete [DecidableEq State] [DecidableEq Batch] [DecidableEq Kind] [DecidableEq Key]
    (table : Table State Batch Kind Key Value) (required : List Key) (checked : covers table required = true)
    (key : Key) (member : key ∈ required) : ∃ handle, decode table handle = some key := by
  have present := List.all_eq_true.mp checked key member
  cases found : locate key (keys table) with
  | none => simp [found] at present
  | some index =>
    have encoded : encode table table.owner table.kind key = some ⟨table.owner, table.kind, index⟩ := by
      simp [encode, encodeLocal, found]
    exact ⟨_, decode_encode table key _ encoded⟩

/-- Owner-checked composition reuses the exact objects; no copied projection
or target-correspondence premise is introduced. -/
structure Owned (State Batch Value : Type) where
  owner : Owner State Batch
  value : Value

def join [DecidableEq State] [DecidableEq Batch] {A B : Type}
    (left : Owned State Batch A) (right : Owned State Batch B) : Option (Owned State Batch (A × B)) :=
  if left.owner = right.owner then some ⟨left.owner, (left.value, right.value)⟩ else none

theorem same_owner_composition [DecidableEq State] [DecidableEq Batch] {A B : Type}
    (left : Owned State Batch A) (right : Owned State Batch B) (same : left.owner = right.owner) :
    join left right = some ⟨left.owner, (left.value, right.value)⟩ := by simp [join, same]

theorem join_rejects_foreign_state [DecidableEq State] [DecidableEq Batch] {A B : Type}
    (left : Owned State Batch A) (right : Owned State Batch B)
    (foreignState : left.owner.state ≠ right.owner.state) : join left right = none := by
  have different : left.owner ≠ right.owner := fun same => foreignState (congrArg Owner.state same)
  simp [join, different]

/-- Raw and canonical coordinates are retained together, never identified by
the finite encoding. The canonical function is an actual owner read. -/
structure Coordinates (Key : Type) where
  raw : Key
  canonical : Key
  deriving DecidableEq

def coordinatesCheck [DecidableEq Key] (canonicalAt : Key → Option Key) (pair : Coordinates Key) : Bool :=
  decide (canonicalAt pair.raw = some pair.canonical)

theorem raw_canonical_distinctions [DecidableEq State] [DecidableEq Batch] [DecidableEq Kind] [DecidableEq Key]
    (table : Table State Batch Kind Key Value) (pair : Coordinates Key) (different : pair.raw ≠ pair.canonical)
    (raw canonical : Handle State Batch Kind)
    (er : encode table table.owner table.kind pair.raw = some raw)
    (ec : encode table table.owner table.kind pair.canonical = some canonical) : raw ≠ canonical := by
  intro same
  subst canonical
  exact different (encoding_distinguishes table pair.raw pair.canonical raw er ec)

/-- A finite actual table read transports arbitrary properties of the SAME
retained value. The property is not an input equivalence/extraction axiom. -/
theorem read_preserves_property [DecidableEq State] [DecidableEq Batch] [DecidableEq Kind] [DecidableEq Key]
    (table : Table State Batch Kind Key Value) (key : Key) (handle : Handle State Batch Kind)
    (value : Value) (encoded : encode table table.owner table.kind key = some handle)
    (native : nativeRead table key = some value) (property : Value → Prop) (proved : property value) :
    ∃ retained, read table handle = some retained ∧ property retained := by
  exact ⟨value, (lookup_commutes table key handle encoded).trans native, proved⟩

def inventoryHandles (table : Table State Batch Kind Key Value) : List (Handle State Batch Kind) :=
  (List.range table.entries.length).map (fun index => ⟨table.owner, table.kind, index⟩)

theorem every_native_index_enumerated (table : Table State Batch Kind Key Value) (index : Nat)
    (bound : index < table.entries.length) :
    (⟨table.owner, table.kind, index⟩ : Handle State Batch Kind) ∈ inventoryHandles table :=
  List.mem_map.mpr ⟨index, List.mem_range.mpr bound, rfl⟩

theorem locate_missing [DecidableEq Key] (key : Key) (xs : List Key) (absent : key ∉ xs) : locate key xs = none := by
  cases found : locate key xs with
  | none => rfl
  | some index =>
    exact False.elim (absent (List.mem_iff_getElem?.mpr ⟨index, locate_sound key xs index found⟩))

def available [DecidableEq Key] (table : Table State Batch Kind Key Value) (required : List Key) : Bool :=
  decide (valid table) && covers table required

theorem missing_candidate_unavailable [DecidableEq Key] (table : Table State Batch Kind Key Value)
    (required : List Key) (key : Key) (needed : key ∈ required) (absent : key ∉ keys table) :
    available table required = false := by
  have missing := locate_missing key (keys table) absent
  have gap : covers table required = false := by
    apply Bool.eq_false_iff.mpr
    intro all
    have present := List.all_eq_true.mp all key needed
    simp [missing] at present
  simp [available, gap]

theorem collapsed_inventory_unavailable [DecidableEq Key] (table : Table State Batch Kind Key Value)
    (required : List Key) (collapsed : ¬ valid table) : available table required = false := by
  simp [available, collapsed]

open CurrentEmissionOwnershipR47 (Endpoint)
open NativeResidualPublicationR51 (Inputs Query Item FactReads)
open PerCallResidualPublicationR52 (Captured Store Installed DrainSource ModeSource)
open WholePublicationResidualR53 (NativeSource OwnerReads CutChain assemble)

/-- Read the exact retained context/native object from owner-qualified tables.
This constructs no Rust-to-model correspondence: table values already have
the indicated model types. Such correspondence remains an explicit boundary. -/
def interpretR53 {Artifact Id Term Fact : Type}
    [DecidableEq State] [DecidableEq Batch] [DecidableEq Kind] [DecidableEq Key]
    [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Term] [DecidableEq Fact]
    (contexts : Table State Batch Kind Key (AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact))
    (states : Table State Batch Kind Key (Inputs Artifact Id Fact))
    (contextHandle stateHandle : Handle State Batch Kind) (store : Store Id Fact)
    (q : Query Artifact Id Term Fact)
    (plan : List (Endpoint Id × AuthenticatedResidualConsumerR49.Decision)) (calls : List (Captured Id Fact)) : Bool :=
  if contexts.owner = states.owner ∧ valid contexts ∧ valid states then
    match read contexts contextHandle, read states stateHandle with
    | some context, some base =>
      WholePublicationResidualR53.wholeObserve base store { q with context := context } plan calls
    | _, _ => false
  else false

/-- Finite lookup commutation plus same-owner composition applies the original
R53 theorem to the SAME read context/base. All primitive R53 source premises
remain visible; no faithful-extraction/target-equivalence hypothesis appears. -/
theorem same_owner_r53_application {Artifact Id Term Fact : Type}
    [DecidableEq State] [DecidableEq Batch] [DecidableEq Kind] [DecidableEq Key]
    [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Term] [DecidableEq Fact]
    (contexts : Table State Batch Kind Key (AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact))
    (states : Table State Batch Kind Key (Inputs Artifact Id Fact))
    (contextKey stateKey : Key) (contextHandle stateHandle : Handle State Batch Kind)
    (context : AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact) (base : Inputs Artifact Id Fact)
    (ec : encode contexts contexts.owner contexts.kind contextKey = some contextHandle)
    (es : encode states states.owner states.kind stateKey = some stateHandle)
    (rc : nativeRead contexts contextKey = some context) (rs : nativeRead states stateKey = some base)
    (same : contexts.owner = states.owner) (contextUnique : valid contexts) (stateUnique : valid states)
    (store : Store Id Fact) (seed : Query Artifact Id Term Fact)
    (plan : List (Endpoint Id × AuthenticatedResidualConsumerR49.Decision))
    (calls : List (Captured Id Fact)) (items : List (Item Id Fact))
    (acceptedPlan : AuthenticatedResidualConsumerR49.plan context seed.original = some plan)
    (built : assemble { seed with context := context } 0 plan calls = some items)
    (inventory : ∀ index, store.keyed seed.publication index =
      WholePublicationResidualR53.keyLookup seed.publication index calls)
    (sources : ∀ r ∈ calls, Installed store r ∧ DrainSource base r ∧
      ModeSource base { seed with context := context } r ∧ NativeSource base { seed with context := context } r)
    (artifact : base.after.current.artifact = context.inputs.arrival.current.artifact)
    (fact : FactReads base { seed with context := context })
    (owner : OwnerReads base { seed with context := context } calls) (chain : CutChain calls) :
    interpretR53 contexts states contextHandle stateHandle store seed plan calls = true := by
  have contextRead := (lookup_commutes contexts contextKey contextHandle ec).trans rc
  have stateRead := (lookup_commutes states stateKey stateHandle es).trans rs
  have observed := WholePublicationResidualR53.source_whole_observed base store
    { seed with context := context } plan calls items acceptedPlan built inventory sources artifact fact owner chain
  simpa only [interpretR53, same, contextUnique, stateUnique, contextRead, stateRead, and_self, ↓reduceIte] using observed

theorem foreign_context_state_unavailable {Artifact Id Term Fact : Type}
    [DecidableEq State] [DecidableEq Batch] [DecidableEq Kind] [DecidableEq Key]
    [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Term] [DecidableEq Fact]
    (contexts : Table State Batch Kind Key (AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact))
    (states : Table State Batch Kind Key (Inputs Artifact Id Fact))
    (contextHandle stateHandle : Handle State Batch Kind) (store : Store Id Fact)
    (q : Query Artifact Id Term Fact)
    (plan : List (Endpoint Id × AuthenticatedResidualConsumerR49.Decision)) (calls : List (Captured Id Fact))
    (different : contexts.owner.state ≠ states.owner.state) :
    interpretR53 contexts states contextHandle stateHandle store q plan calls = false := by
  have foreignOwner : contexts.owner ≠ states.owner := fun same => different (congrArg Owner.state same)
  simp [interpretR53, foreignOwner]

def ownerA : Owner Nat Nat := ⟨1, 77⟩
def ownerB : Owner Nat Nat := ⟨2, 77⟩
def finiteTable : Table Nat Nat Nat Nat Nat := ⟨ownerA, 3, [(4, 40), (9, 90)]⟩
def rawHandle : Handle Nat Nat Nat := ⟨ownerA, 3, 0⟩
def canonicalHandle : Handle Nat Nat Nat := ⟨ownerA, 3, 1⟩

theorem concrete_finite_roundtrips :
    valid finiteTable ∧ available finiteTable [4, 9] = true ∧
    encode finiteTable ownerA 3 4 = some rawHandle ∧ decode finiteTable rawHandle = some 4 ∧
    encode finiteTable ownerA 3 9 = some canonicalHandle ∧ decode finiteTable canonicalHandle = some 9 ∧
    read finiteTable rawHandle = nativeRead finiteTable 4 ∧
    read finiteTable canonicalHandle = nativeRead finiteTable 9 := by decide

theorem concrete_foreign_batch_and_kind_attacks :
    ownerA.batch = ownerB.batch ∧
    rawHandle.ordinal = (⟨ownerB, 3, 0⟩ : Handle Nat Nat Nat).ordinal ∧
    read finiteTable ⟨ownerB, 3, 0⟩ = none ∧ decode finiteTable ⟨ownerB, 3, 0⟩ = none ∧
    read finiteTable ⟨ownerA, 4, 0⟩ = none ∧
    join (⟨ownerA, 40⟩ : Owned Nat Nat Nat) (⟨ownerB, 40⟩ : Owned Nat Nat Nat) = none := by decide

theorem concrete_missing_and_collapsed_candidates :
    available finiteTable [4, 9, 11] = false ∧
    available ({ finiteTable with entries := [(4, 40), (4, 90)] }) [4] = false ∧
    (∀ decodeBad : Nat → Option Nat, ¬ (decodeBad 0 = some 4 ∧ decodeBad 0 = some 9)) := by
  refine ⟨by decide, by decide, ?_⟩
  intro decodeBad both
  have impossible : (4 : Nat) = 9 := Option.some.inj (both.1.symm.trans both.2)
  cases impossible

theorem concrete_raw_canonical_substitution_rejected :
    coordinatesCheck (fun key => if key = 4 then some 9 else if key = 9 then some 9 else none) ⟨4, 9⟩ = true ∧
    rawHandle ≠ canonicalHandle ∧
    read finiteTable rawHandle = some 40 ∧ read finiteTable canonicalHandle = some 90 ∧
    read finiteTable canonicalHandle ≠ some 40 ∧
    (Coordinates.mk 4 9 : Coordinates Nat) ≠ ⟨9, 9⟩ := by decide

def contextTable : Table Nat Nat Nat Nat (AuthenticatedResidualConsumerR49.Context Nat Nat Nat Nat) :=
  ⟨ownerA, 10, [(100, AuthenticatedResidualConsumerR49.knownUnmatchedContext)]⟩
def stateTable : Table Nat Nat Nat Nat (Inputs Nat Nat Nat) :=
  ⟨ownerA, 11, [(200, NativeResidualPublicationR51.witnessInputs)]⟩

theorem concrete_same_owner_r53 :
    interpretR53 contextTable stateTable ⟨ownerA, 10, 0⟩ ⟨ownerA, 11, 0⟩
      PerCallResidualPublicationR52.witnessStore NativeResidualPublicationR51.witnessQuery
      WholePublicationResidualR53.witnessPlan WholePublicationResidualR53.witnessCalls = true := by
  simpa [interpretR53, contextTable, stateTable, read, valid, keys, NativeResidualPublicationR51.witnessQuery] using
    WholePublicationResidualR53.concrete_whole_publication

theorem concrete_same_owner_missing_fact_rejected :
    interpretR53 contextTable
      { stateTable with entries := [(200, { NativeResidualPublicationR51.witnessInputs with facts := fun _ => none })] }
      ⟨ownerA, 10, 0⟩ ⟨ownerA, 11, 0⟩ PerCallResidualPublicationR52.witnessStore
      NativeResidualPublicationR51.witnessQuery WholePublicationResidualR53.witnessPlan
      WholePublicationResidualR53.witnessCalls = false := by decide

theorem concrete_collapsed_context_inventory_rejected :
    interpretR53
      { contextTable with entries := [(100, AuthenticatedResidualConsumerR49.knownUnmatchedContext),
          (100, AuthenticatedResidualConsumerR49.knownUnmatchedContext)] }
      stateTable ⟨ownerA, 10, 0⟩ ⟨ownerA, 11, 0⟩ PerCallResidualPublicationR52.witnessStore
      NativeResidualPublicationR51.witnessQuery WholePublicationResidualR53.witnessPlan
      WholePublicationResidualR53.witnessCalls = false := by decide

/-- Both states deliberately share the batch, model payloads and ordinal0.
Owner-sensitive composition still rejects the transplanted state table. -/
theorem concrete_foreign_state_transplant_rejected :
    contextTable.owner.batch = ({ stateTable with owner := ownerB }).owner.batch ∧
    WholePublicationResidualR53.wholeObserve NativeResidualPublicationR51.witnessInputs
      PerCallResidualPublicationR52.witnessStore NativeResidualPublicationR51.witnessQuery
      WholePublicationResidualR53.witnessPlan WholePublicationResidualR53.witnessCalls = true ∧
    interpretR53 contextTable { stateTable with owner := ownerB } ⟨ownerA, 10, 0⟩ ⟨ownerB, 11, 0⟩
      PerCallResidualPublicationR52.witnessStore NativeResidualPublicationR51.witnessQuery
      WholePublicationResidualR53.witnessPlan WholePublicationResidualR53.witnessCalls = false := by
  exact ⟨rfl, WholePublicationResidualR53.concrete_whole_publication, by decide⟩

end YulangClosure.OwnedResidualProjectionR54
