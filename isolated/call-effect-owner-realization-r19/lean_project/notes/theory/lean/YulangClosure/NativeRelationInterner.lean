import YulangClosure.NativeValuePorts

/-!
Physical ScopedFlowId / RelationKey interning. The native hash maps are modeled
by their finite exact-equality map semantics, whose insert/remove equations are
proved below. `Entry.origin` and `birth` are immutable ghost data recorded by the
actual allocation constructor; neither is consulted by the physical algorithm.
-/
namespace YulangClosure.NativeRelationInterner

open NativeValuePorts (Pair Flow Key Arena)
open NativeContextExpansion (Expr ScopedDemand)

abbrev Map (K : Type) := K → Option Nat

def empty : Map K := fun _ => none

def put [DecidableEq K] (m : Map K) (key : K) (value : Nat) : Map K :=
  fun query => if query = key then some value else m query

def erase [DecidableEq K] (m : Map K) (key : K) : Map K :=
  fun query => if query = key then none else m query

def restore [DecidableEq K] (m : Map K) (key : K) : Option Nat → Map K
  | none => erase m key
  | some old => put m key old

/-- Finite interner map: equality is equality of the entire key, independently
of hash bucket collisions. Its support is exactly the finite vector below. -/
def cache [DecidableEq K] (items : List K) : Map K :=
  fun key => if key ∈ items then some (items.idxOf key) else none

@[simp] theorem cache_none [DecidableEq K] (items : List K) (key : K) :
    cache items key = none ↔ key ∉ items := by simp [cache]

theorem cache_some [DecidableEq K] {items : List K} {key : K} {id : Nat}
    (found : cache items key = some id) : key ∈ items ∧ items.idxOf key = id := by
  unfold cache at found
  split at found
  · exact ⟨by assumption, Option.some.inj found⟩
  · cases found

theorem cache_readback [DecidableEq K] {items : List K} {key : K} {id : Nat}
    (found : cache items key = some id) : items[id]? = some key := by
  obtain ⟨member, rfl⟩ := cache_some found
  rw [List.getElem?_eq_getElem (List.idxOf_lt_length_of_mem member)]
  simp

theorem cache_append [DecidableEq K] (items : List K) (key : K)
    (fresh : key ∉ items) : cache (items ++ [key]) = put (cache items) key items.length := by
  funext query
  by_cases same : query = key
  · subst query
    simp [cache, put, fresh, List.idxOf_append]
  · by_cases member : query ∈ items <;> simp [cache, put, same, List.idxOf_append, member]

theorem cache_old [DecidableEq K] {items : List K} {key old : K} {id : Nat}
    (found : cache items old = some id) : cache (items ++ [key]) old = some id := by
  obtain ⟨member, index⟩ := cache_some found
  simp [cache, member, List.idxOf_append, index]

theorem restore_put [DecidableEq K] (m : Map K) (key : K) (value : Nat) :
    restore (put m key value) key (m key) = m := by
  funext query
  by_cases same : query = key
  · subst query
    cases old : m key <;> simp [restore, put, erase]
  · cases old : m key <;> simp [restore, put, erase, same]

theorem cache_remove_fresh [DecidableEq K] (items : List K) (key : K)
    (fresh : key ∉ items) : erase (cache (items ++ [key])) key = cache items := by
  rw [cache_append items key fresh]
  funext query
  by_cases same : query = key
  · subst query; simp [erase, cache, fresh]
  · simp [erase, put, same]

theorem cache_map_congr [DecidableEq A] [DecidableEq B] (items : List E)
    (f : E → A) (g : E → B) (a : A) (b : B)
    (equal : ∀ e ∈ items, f e = a ↔ g e = b) :
    cache (items.map f) a = cache (items.map g) b := by
  have indices : (items.map f).idxOf a = (items.map g).idxOf b := by
    induction items with
    | nil => rfl
    | cons e rest ih =>
        have head := equal e (by simp)
        have tail : ∀ x ∈ rest, f x = a ↔ g x = b := fun x mem => equal x (by simp [mem])
        simp only [List.map_cons, List.idxOf_cons, beq_iff_eq]
        simp only [head, ih tail]
  have members : a ∈ items.map f ↔ b ∈ items.map g := by
    simp only [List.mem_map]
    constructor
    · rintro ⟨e, member, value⟩; exact ⟨e, member, (equal e member).mp value⟩
    · rintro ⟨e, member, value⟩; exact ⟨e, member, (equal e member).mpr value⟩
  simp only [cache, members, indices]

structure RawKey where
  pair : Pair
  context : Nat
  sources : Option Nat
  flowIndex : Nat
  deriving DecidableEq, Repr

def encode (key : Key) (flowIndex : Nat) : RawKey :=
  ⟨key.pair, key.context, key.sources, flowIndex⟩

structure Entry where
  key : RawKey
  previous : Option Nat
  birth : Nat
  origin : Key
  deriving DecidableEq, Repr

def headFold (offset : Nat) (items : List Entry) (heads : Map Pair) : Map Pair :=
  match items with
  | [] => heads
  | e :: rest => headFold (offset + 1) rest (put heads e.key.pair offset)

def heads (items : List Entry) : Map Pair := headFold 0 items empty

theorem head_fold_append (left right : List Entry) (offset : Nat) (m : Map Pair) :
    headFold offset (left ++ right) m =
      headFold (offset + left.length) right (headFold offset left m) := by
  induction left generalizing offset m with
  | nil => simp [headFold]
  | cons e rest ih =>
      simpa [headFold, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (offset + 1) (put m e.key.pair offset)

theorem heads_append (items : List Entry) (entry : Entry) :
    heads (items ++ [entry]) = put (heads items) entry.key.pair items.length := by
  simp [heads, head_fold_append, headFold]

structure Store where
  flows : List Flow := []
  relations : List Entry := []
  workUsed : Nat := 0
  clock : Nat := 0
  deriving DecidableEq, Repr

def Store.flowKeys (s : Store) : Map Flow :=
  fun flow => (cache s.flows flow).map (· + 1)

def Store.flowId (s : Store) (flow : Flow) : Option Nat :=
  if flow = ({} : Flow) then some 0 else s.flowKeys flow

def Store.flowAt (s : Store) (id : Nat) : Option Flow :=
  if id = 0 then some {} else s.flows[id - 1]?

def Store.keys (s : Store) : Map RawKey := cache (s.relations.map Entry.key)
def Store.pairHeads (s : Store) : Map Pair := heads s.relations

def Store.decode (s : Store) (key : RawKey) : Option Key :=
  (s.flowAt key.flowIndex).map fun flow => ⟨key.pair, key.context, key.sources, flow⟩

def Store.readback (s : Store) (id : Nat) : Option Key := do
  let entry ← s.relations[id]?
  s.decode entry.key

def Store.arena (s : Store) (contexts : List Expr) (transformers : List NativeValuePorts.Transformer) : Arena :=
  ⟨contexts, transformers, s.relations.map Entry.origin⟩

def Store.charge (s : Store) : Store := { s with workUsed := s.workUsed + 1 }
def Store.addFlow (s : Store) (flow : Flow) : Store := { s with flows := s.flows ++ [flow] }

def Store.addRelation (s : Store) (key : Key) (flowId : Nat) : Store :=
  { s with
    relations := s.relations ++ [⟨encode key flowId, s.pairHeads key.pair, s.clock, key⟩]
    clock := s.clock + 1 }

theorem flow_id_readback {s : Store} {flow : Flow} {id : Nat}
    (found : s.flowId flow = some id) : s.flowAt id = some flow := by
  unfold Store.flowId at found
  split at found
  next identity =>
    subst flow
    have : id = 0 := (Option.some.inj found).symm
    subst id
    rfl
  next =>
    obtain ⟨index, actual, rfl⟩ := Option.map_eq_some_iff.mp found
    simpa [Store.flowAt] using cache_readback actual

theorem flow_id_injective {s : Store} {left right : Flow} {id : Nat}
    (a : s.flowId left = some id) (b : s.flowId right = some id) : left = right := by
  have first := flow_id_readback a
  rw [flow_id_readback b] at first
  exact (Option.some.inj first).symm

theorem flow_id_extension {s : Store} {flow old : Flow} {id : Nat}
    (found : s.flowId old = some id) : (s.addFlow flow).flowId old = some id := by
  unfold Store.flowId at found ⊢
  split at found
  next identity => simpa [identity] using found
  next different =>
    obtain ⟨index, actual, rfl⟩ := Option.map_eq_some_iff.mp found
    simp only [different, ↓reduceIte, Store.flowKeys, Store.addFlow, cache_old actual, Option.map_some]

theorem fresh_flow_id (s : Store) (flow : Flow) (nondefault : flow ≠ {})
    (fresh : flow ∉ s.flows) : (s.addFlow flow).flowId flow = some (s.flows.length + 1) := by
  simp [Store.flowId, nondefault, Store.flowKeys, Store.addFlow, cache, fresh, List.idxOf_append]

structure Valid (s : Store) : Prop where
  flowDistinct : s.flows.Nodup
  noDefault : ({} : Flow) ∉ s.flows
  relationDistinct : (s.relations.map Entry.key).Nodup
  encoded : ∀ e ∈ s.relations, e.key = encode e.origin e.key.flowIndex
  flow : ∀ e ∈ s.relations, s.flowId e.origin.flow = some e.key.flowIndex
  born : ∀ e ∈ s.relations, e.birth < s.clock

theorem valid_empty : Valid ({} : Store) := by constructor <;> simp

theorem valid_charge {s : Store} (valid : Valid s) : Valid s.charge :=
  ⟨valid.flowDistinct, valid.noDefault, valid.relationDistinct, valid.encoded, valid.flow, valid.born⟩

theorem valid_add_flow {s : Store} (valid : Valid s) {flow : Flow}
    (nondefault : flow ≠ {}) (fresh : flow ∉ s.flows) : Valid (s.addFlow flow) := by
  refine ⟨?_, ?_, valid.relationDistinct, valid.encoded, ?_, valid.born⟩
  · change (s.flows ++ [flow]).Nodup
    rw [List.nodup_append]
    refine ⟨valid.flowDistinct, by simp, ?_⟩
    intro a member b last same
    have value : b = flow := List.mem_singleton.mp last
    exact fresh ((same.trans value) ▸ member)
  · simpa [Store.addFlow, valid.noDefault] using Ne.symm nondefault
  · intro e member
    exact flow_id_extension (valid.flow e member)

theorem valid_add_relation {s : Store} (valid : Valid s) {key : Key} {id : Nat}
    (flow : s.flowId key.flow = some id) (fresh : s.keys (encode key id) = none) :
    Valid (s.addRelation key id) := by
  have absent := (cache_none _ _).mp fresh
  refine ⟨valid.flowDistinct, valid.noDefault, ?_, ?_, ?_, ?_⟩
  · simpa [Store.addRelation, List.nodup_append] using And.intro valid.relationDistinct absent
  · intro e member
    simp only [Store.addRelation, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact valid.encoded e old
    · rfl
  · intro e member
    simp only [Store.addRelation, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact valid.flow e old
    · exact flow
  · intro e member
    simp only [Store.addRelation, List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact Nat.lt_succ_of_lt (valid.born e old)
    · exact Nat.lt_succ_self _

theorem stored_key_decodes {s : Store} (valid : Valid s) {entry : Entry}
    (member : entry ∈ s.relations) : s.decode entry.key = some entry.origin := by
  have encoded := valid.encoded entry member
  have decoded := flow_id_readback (valid.flow entry member)
  unfold Store.decode
  rw [decoded]
  simp only [Option.map_some]
  rw [encoded]
  cases entry.origin
  rfl

theorem physical_complete_key {s : Store} (valid : Valid s) {entry : Entry}
    (member : entry ∈ s.relations) {key : Key} {id : Nat}
    (flow : s.flowId key.flow = some id) : entry.key = encode key id ↔ entry.origin = key := by
  constructor
  · intro same
    have target : s.decode (encode key id) = some key := by
      simp [Store.decode, encode, flow_id_readback flow]
    have actual := stored_key_decodes valid member
    rw [same, target] at actual
    exact (Option.some.inj actual).symm
  · intro same
    have actual := valid.flow entry member
    rw [same, flow] at actual
    have flowIndex : entry.key.flowIndex = id := (Option.some.inj actual).symm
    rw [valid.encoded entry member, same, flowIndex]

theorem physical_arena_cache {s : Store} (valid : Valid s) {key : Key} {id : Nat}
    (flow : s.flowId key.flow = some id) :
    s.keys (encode key id) = cache (s.relations.map Entry.origin) key :=
  cache_map_congr s.relations Entry.key Entry.origin _ _
    (fun _e member => physical_complete_key valid member flow)

theorem complete_stored_readback {s : Store} (valid : Valid s) {id : Nat} {entry : Entry}
    (found : s.relations[id]? = some entry) : s.readback id = some entry.origin := by
  simp only [Store.readback, found]
  exact stored_key_decodes valid (List.mem_of_getElem? found)

/-- Allocator results are inputs for the exact native calls, not promises that
allocation will succeed. Capacities themselves are intentionally projected out. -/
structure Resources where
  contextCount : Nat := 0
  enabled : Bool := true
  usizeMax : Nat := 2 ^ 64 - 1
  flowVector : Bool := true
  flowMap : Bool := true
  relationVector : Bool := true
  relationMap : Bool := true
  pairMap : Bool := true
  deriving DecidableEq, Repr

inductive Failure where
  | contextAssertion | exhausted | receiptMismatch
  deriving DecidableEq, Repr

inductive Result where
  | ok (id : Nat)
  | error (failure : Failure)
  deriving DecidableEq, Repr

/-- The actual three guards, in source order. Invalid Context is a prior panic,
not an availability result. -/
def guards (key : Key) : Option Failure :=
  match key.pair with
  | .effect lower upper =>
      if key.flow.transformer ≠ 0 ∧ lower = upper then some .exhausted
      else if key.flow.demand.isSome then some .receiptMismatch else none
  | .value _ _ =>
      if key.flow.transformer ≠ 0 then some .receiptMismatch else none

theorem guards_exact (key : Key) : guards key = none ↔ NativeValuePorts.Allowed key := by
  unfold guards NativeValuePorts.Allowed
  cases key.pair with
  | value => simp
  | effect lower upper =>
      cases key.flow.demand <;> by_cases zero : key.flow.transformer = 0 <;>
        by_cases same : lower = upper <;> simp [zero, same]

/-- candidate_context.rs 3072–3080, with ScopeInventory::charge(1)'s checked
addition and 65,536 work limit. Reuse bypasses every allocation guard. -/
def internFlow (s : Store) (resources : Resources) (flow : Flow) : Store × Result :=
  if flow = ({} : Flow) then (s, .ok 0)
  else match s.flowKeys flow with
  | some id => (s, .ok id)
  | none =>
      if resources.enabled = false ∨ s.flows.length ≥ 4096 then (s, .error .exhausted)
      else if s.workUsed + 1 > resources.usizeMax then (s, .error .exhausted)
      else if s.workUsed + 1 > 65536 then (s, .error .exhausted)
      else
        let charged := s.charge
        if resources.flowVector = false then (charged, .error .exhausted)
        else if resources.flowMap = false then (charged, .error .exhausted)
        else if s.flows.length + 1 > resources.usizeMax then (charged, .error .exhausted)
        else (charged.addFlow flow, .ok (s.flows.length + 1))

/-- candidate_context.rs 3082–3094. It runs AFTER flow allocation and therefore
retains the new flow and charged work if any relation reservation fails. -/
def internRelation (s : Store) (resources : Resources) (key : Key) (flowId : Nat) : Store × Result :=
  match s.keys (encode key flowId) with
  | some id => (s, .ok id)
  | none =>
      if s.relations.length ≥ 2 ^ 32 then (s, .error .exhausted)
      else if resources.relationVector = false then (s, .error .exhausted)
      else if resources.relationMap = false then (s, .error .exhausted)
      else if resources.pairMap = false then (s, .error .exhausted)
      else (s.addRelation key flowId, .ok s.relations.length)

def relationWithScoped (s : Store) (resources : Resources) (key : Key) : Store × Result :=
  if key.context > resources.contextCount then (s, .error .contextAssertion)
  else match guards key with
  | some error => (s, .error error)
  | none =>
      let (afterFlow, result) := internFlow s resources key.flow
      match result with
      | .error error => (afterFlow, .error error)
      | .ok flowId => internRelation afterFlow resources key flowId

/-- Constructor-derived state footprint. Error cases state precisely which
projected writes occurred; resource order remains the executable definition. -/
inductive FlowFootprint (s : Store) (flow : Flow) : Store → Result → Prop where
  | identity (same : flow = {}) : FlowFootprint s flow s (.ok 0)
  | reuse (id : Nat) (found : s.flowId flow = some id) : FlowFootprint s flow s (.ok id)
  | rejected : FlowFootprint s flow s (.error .exhausted)
  | chargedFailure : FlowFootprint s flow s.charge (.error .exhausted)
  | fresh (nondefault : flow ≠ {}) (absent : flow ∉ s.flows) :
      FlowFootprint s flow (s.charge.addFlow flow) (.ok (s.flows.length + 1))

theorem flow_footprint (s : Store) (resources : Resources) (flow : Flow) :
    FlowFootprint s flow (internFlow s resources flow).1 (internFlow s resources flow).2 := by
  unfold internFlow
  split
  next identity => exact .identity identity
  next nondefault =>
    split
    next id found => exact .reuse id (by simp [Store.flowId, nondefault, found])
    next missing =>
      have absent : flow ∉ s.flows := by
        unfold Store.flowKeys at missing
        simpa using missing
      split
      · exact .rejected
      · split
        · exact .rejected
        · split
          · exact .rejected
          · split
            · exact .chargedFailure
            · split
              · exact .chargedFailure
              · split
                · exact .chargedFailure
                · exact .fresh nondefault absent

theorem flow_footprint_valid {s u : Store} {flow : Flow} {result : Result}
    (event : FlowFootprint s flow u result) (valid : Valid s) : Valid u := by
  cases event with
  | identity | reuse | rejected => exact valid
  | chargedFailure => exact valid_charge valid
  | fresh nondefault absent => exact valid_add_flow (valid_charge valid) nondefault absent

theorem flow_footprint_success {s u : Store} {flow : Flow} {id : Nat}
    (event : FlowFootprint s flow u (.ok id)) : u.flowId flow = some id := by
  cases event with
  | identity same => simp [Store.flowId, same]
  | reuse _ found => exact found
  | fresh nondefault absent => exact fresh_flow_id s.charge flow nondefault absent

theorem flow_footprint_old {s u : Store} {flow old : Flow} {result : Result} {id : Nat}
    (event : FlowFootprint s flow u result) (found : s.flowId old = some id) :
    u.flowId old = some id := by
  cases event with
  | identity | reuse | rejected | chargedFailure => exact found
  | fresh => exact flow_id_extension found

theorem flow_footprint_vectors {s u : Store} {flow : Flow} {result : Result}
    (event : FlowFootprint s flow u result) :
    u.relations = s.relations ∧ u.clock = s.clock ∧ ∃ suffix, u.flows = s.flows ++ suffix := by
  cases event <;> simp [Store.charge, Store.addFlow]

theorem default_bypasses_resources (s : Store) (resources : Resources) :
    internFlow s resources {} = (s, .ok 0) := by simp [internFlow]

theorem existing_flow_bypasses_resources {s : Store} {flow : Flow} {id : Nat}
    (found : s.flowKeys flow = some id) (nondefault : flow ≠ {}) (resources : Resources) :
    internFlow s resources flow = (s, .ok id) := by simp [internFlow, nondefault, found]

inductive RelationFootprint (s : Store) (key : Key) (flowId : Nat) : Store → Result → Prop where
  | reuse (id : Nat) (found : s.keys (encode key flowId) = some id) :
      RelationFootprint s key flowId s (.ok id)
  | rejected : RelationFootprint s key flowId s (.error .exhausted)
  | fresh (absent : s.keys (encode key flowId) = none) :
      RelationFootprint s key flowId (s.addRelation key flowId) (.ok s.relations.length)

theorem relation_footprint (s : Store) (resources : Resources) (key : Key) (flowId : Nat) :
    RelationFootprint s key flowId (internRelation s resources key flowId).1
      (internRelation s resources key flowId).2 := by
  unfold internRelation
  split
  next id found => exact .reuse id found
  next missing =>
    split
    · exact .rejected
    · split
      · exact .rejected
      · split
        · exact .rejected
        · split
          · exact .rejected
          · exact .fresh missing

theorem relation_footprint_valid {s u : Store} {key : Key} {flowId : Nat} {result : Result}
    (event : RelationFootprint s key flowId u result) (valid : Valid s)
    (flow : s.flowId key.flow = some flowId) : Valid u := by
  cases event with
  | reuse | rejected => exact valid
  | fresh absent => exact valid_add_relation valid flow absent

theorem relation_success_arena {s u : Store} {key : Key} {flowId id : Nat}
    (event : RelationFootprint s key flowId u (.ok id)) (valid : Valid s)
    (flow : s.flowId key.flow = some flowId)
    (contexts : List Expr) (transformers : List NativeValuePorts.Transformer) :
    (s.arena contexts transformers).relation key = (u.arena contexts transformers, id) := by
  have same := physical_arena_cache valid flow
  cases event with
  | reuse id found =>
      rw [same] at found
      obtain ⟨member, index⟩ := cache_some found
      simp [Store.arena, Arena.relation, NativeValuePorts.intern, member, index]
  | fresh absent =>
      rw [same] at absent
      have fresh := (cache_none _ _).mp absent
      simp [Store.arena, Arena.relation, NativeValuePorts.intern, fresh, Store.addRelation]

theorem relation_success_readback {s u : Store} {key : Key} {flowId id : Nat}
    (event : RelationFootprint s key flowId u (.ok id)) (valid : Valid s)
    (flow : s.flowId key.flow = some flowId) : u.readback id = some key := by
  cases event with
  | reuse id found =>
      have raw := cache_readback found
      rw [List.getElem?_map] at raw
      obtain ⟨entry, actual, value⟩ := Option.map_eq_some_iff.mp raw
      have same := (physical_complete_key valid (List.mem_of_getElem? actual) flow).mp value
      rw [← same]
      exact complete_stored_readback valid actual
  | fresh absent =>
      exact complete_stored_readback (valid_add_relation valid flow absent)
        (entry := ⟨encode key flowId, s.pairHeads key.pair, s.clock, key⟩)
        (by simp [Store.addRelation])

inductive CallFootprint (s : Store) (resources : Resources) (key : Key) : Store → Result → Prop where
  | blocked (error : Failure) : CallFootprint s resources key s (.error error)
  | flowFailure {u : Store} {error : Failure} (flow : FlowFootprint s key.flow u (.error error)) :
      CallFootprint s resources key u (.error error)
  | allocated {middle u : Store} {flowId : Nat} {result : Result}
      (context : key.context ≤ resources.contextCount) (allowed : NativeValuePorts.Allowed key)
      (flow : FlowFootprint s key.flow middle (.ok flowId))
      (relation : RelationFootprint middle key flowId u result) :
      CallFootprint s resources key u result

theorem call_footprint (s : Store) (resources : Resources) (key : Key) :
    CallFootprint s resources key (relationWithScoped s resources key).1
      (relationWithScoped s resources key).2 := by
  unfold relationWithScoped
  split
  · exact .blocked _
  next context =>
    split
    · exact .blocked _
    next allowed =>
      have ff := flow_footprint s resources key.flow
      generalize result : internFlow s resources key.flow = output at ff ⊢
      rcases output with ⟨middle, outcome⟩
      cases outcome with
      | error error => exact .flowFailure ff
      | ok id =>
          exact .allocated (Nat.le_of_not_gt context) ((guards_exact key).mp allowed)
            ff (relation_footprint middle resources key id)

theorem call_preserves_valid {s u : Store} {resources : Resources} {key : Key} {result : Result}
    (event : CallFootprint s resources key u result) (valid : Valid s) : Valid u := by
  cases event with
  | blocked => exact valid
  | flowFailure flow => exact flow_footprint_valid flow valid
  | allocated _ _ flow relation =>
      exact relation_footprint_valid relation (flow_footprint_valid flow valid)
        (flow_footprint_success flow)

theorem successful_physical_intern {s u : Store} {resources : Resources} {key : Key} {id : Nat}
    (valid : Valid s) (computed : relationWithScoped s resources key = (u, .ok id))
    (contexts : List Expr) (transformers : List NativeValuePorts.Transformer) :
    NativeValuePorts.Allowed key ∧ key.context ≤ resources.contextCount ∧
    u.readback id = some key ∧
    (s.arena contexts transformers).relation key = (u.arena contexts transformers, id) := by
  have event := call_footprint s resources key
  rw [computed] at event
  cases event with
  | allocated context allowed flow relation =>
      have middleValid := flow_footprint_valid flow valid
      have flowValid := flow_footprint_success flow
      have readback := relation_success_readback relation middleValid flowValid
      have arena := relation_success_arena relation middleValid flowValid contexts transformers
      have vectors := (flow_footprint_vectors flow).1
      exact ⟨allowed, context, readback, by simpa only [Store.arena, vectors] using arena⟩

/-- The exact retained relation suffix and pair-head undo linkage. -/
inductive RelationTrace : List Entry → List Entry → Prop where
  | nil (items : List Entry) : RelationTrace items items
  | snoc {first last : List Entry} (prior : RelationTrace first last) (entry : Entry)
      (fresh : entry.key ∉ last.map Entry.key)
      (previous : entry.previous = heads last entry.key.pair) :
      RelationTrace first (last ++ [entry])

theorem relation_trace_trans {a b c : List Entry} (first : RelationTrace a b)
    (second : RelationTrace b c) : RelationTrace a c := by
  induction second with
  | nil => exact first
  | snoc _ entry fresh previous ih => exact .snoc ih entry fresh previous

def undoKeys : List Entry → Map RawKey → Map RawKey
  | [], keys => keys
  | entry :: rest, keys => erase (undoKeys rest keys) entry.key

def undoHeads : List Entry → Map Pair → Map Pair
  | [], table => table
  | entry :: rest, table => restore (undoHeads rest table) entry.key.pair entry.previous

theorem undo_keys_append (left right : List Entry) (m : Map RawKey) :
    undoKeys (left ++ right) m = undoKeys left (undoKeys right m) := by
  induction left with
  | nil => rfl
  | cons e rest ih => simp [undoKeys, ih]

theorem undo_heads_append (left right : List Entry) (m : Map Pair) :
    undoHeads (left ++ right) m = undoHeads left (undoHeads right m) := by
  induction left with
  | nil => rfl
  | cons e rest ih => simp [undoHeads, ih]

theorem relation_trace_undo {first last : List Entry} (trace : RelationTrace first last) :
    ∃ suffix, last = first ++ suffix ∧
      undoKeys suffix (cache (last.map Entry.key)) = cache (first.map Entry.key) ∧
      undoHeads suffix (heads last) = heads first := by
  induction trace with
  | nil => exact ⟨[], by simp, rfl, rfl⟩
  | @snoc middle prior entry fresh previous ih =>
      obtain ⟨suffix, shape, keys, pairs⟩ := ih
      refine ⟨suffix ++ [entry], by simp [shape, List.append_assoc], ?_, ?_⟩
      · rw [undo_keys_append]
        simp only [undoKeys]
        have remove : erase (cache ((middle ++ [entry]).map Entry.key)) entry.key =
            cache (middle.map Entry.key) := by
          simpa only [List.map_append, List.map_singleton] using cache_remove_fresh (middle.map Entry.key) entry.key fresh
        rw [remove]
        exact keys
      · rw [undo_heads_append]
        simp only [undoHeads, heads_append, previous, restore_put]
        exact pairs

theorem call_relation_trace {s u : Store} {resources : Resources} {key : Key} {result : Result}
    (event : CallFootprint s resources key u result) : RelationTrace s.relations u.relations := by
  cases event with
  | blocked => exact .nil _
  | flowFailure flow => rw [(flow_footprint_vectors flow).1]; exact .nil _
  | allocated _ _ flow relation =>
      have shape := (flow_footprint_vectors flow).1
      cases relation with
      | reuse | rejected => rw [shape]; exact .nil _
      | fresh absent =>
          rw [← shape]
          exact .snoc (.nil _) _ ((cache_none _ _).mp absent) rfl

theorem call_flow_old {s u : Store} {resources : Resources} {key : Key} {result : Result}
    (event : CallFootprint s resources key u result) {flow : Flow} {id : Nat}
    (found : s.flowId flow = some id) : u.flowId flow = some id := by
  cases event with
  | blocked => exact found
  | flowFailure ff => exact flow_footprint_old ff found
  | allocated _ _ ff relation =>
      have old := flow_footprint_old ff found
      cases relation <;> exact old

theorem call_flow_prefix {s u : Store} {resources : Resources} {key : Key} {result : Result}
    (event : CallFootprint s resources key u result) : ∃ suffix, u.flows = s.flows ++ suffix := by
  cases event with
  | blocked => exact ⟨[], by simp⟩
  | flowFailure ff => exact (flow_footprint_vectors ff).2.2
  | allocated _ _ ff relation =>
      have shape := (flow_footprint_vectors ff).2.2
      cases relation <;> exact shape

theorem call_clock {s u : Store} {resources : Resources} {key : Key} {result : Result}
    (event : CallFootprint s resources key u result) : s.clock ≤ u.clock := by
  cases event with
  | blocked => exact Nat.le_refl _
  | flowFailure ff => exact Nat.le_of_eq (flow_footprint_vectors ff).2.1.symm
  | allocated _ _ ff relation =>
      have clock := (flow_footprint_vectors ff).2.1
      cases relation <;> simp_all [Store.addRelation]

/-- Other native ScopeInventory::charge callers can consume work between
relation calls. Only their successful counter update is projected here. -/
def Store.inventory (s : Store) (amount : Nat) : Store :=
  { s with workUsed := s.workUsed + amount }

theorem valid_inventory {s : Store} (valid : Valid s) (amount : Nat) : Valid (s.inventory amount) :=
  ⟨valid.flowDistinct, valid.noDefault, valid.relationDistinct, valid.encoded, valid.flow, valid.born⟩

/-- Calls include errors and afterFailure flow/charge effects. A run has no successful
inference or completed-body premise. -/
inductive Run : Store → Store → Prop where
  | nil (s : Store) : Run s s
  | inventory {first last : Store} (prior : Run first last) (amount usizeMax : Nat)
      (fits : last.workUsed + amount ≤ usizeMax) (bounded : last.workUsed + amount ≤ 65536) :
      Run first (last.inventory amount)
  | call {first last : Store} (prior : Run first last) (resources : Resources) (key : Key) :
      Run first (relationWithScoped last resources key).1

theorem run_valid {s u : Store} (run : Run s u) (valid : Valid s) : Valid u := by
  induction run with
  | nil => exact valid
  | inventory _ amount _ _ _ ih => exact valid_inventory ih amount
  | call _ resources key ih => exact call_preserves_valid (call_footprint _ resources key) ih

theorem run_relation_trace {s u : Store} (run : Run s u) : RelationTrace s.relations u.relations := by
  induction run with
  | nil => exact .nil _
  | inventory _ _ _ _ _ ih => exact ih
  | call _ resources key ih => exact relation_trace_trans ih (call_relation_trace (call_footprint _ resources key))

theorem run_flow_old {s u : Store} (run : Run s u) {flow : Flow} {id : Nat}
    (found : s.flowId flow = some id) : u.flowId flow = some id := by
  induction run with
  | nil => exact found
  | inventory _ _ _ _ _ ih => exact ih
  | call _ resources key ih => exact call_flow_old (call_footprint _ resources key) ih

theorem run_flow_prefix {s u : Store} (run : Run s u) : ∃ suffix, u.flows = s.flows ++ suffix := by
  induction run with
  | nil => exact ⟨[], by simp⟩
  | inventory _ _ _ _ _ ih => exact ih
  | @call lastStore _ resources key ih =>
      obtain ⟨first, a⟩ := ih
      obtain ⟨last, b⟩ := call_flow_prefix (call_footprint lastStore resources key)
      exact ⟨first ++ last, by simp [b, a, List.append_assoc]⟩

theorem run_clock {s u : Store} (run : Run s u) : s.clock ≤ u.clock := by
  induction run with
  | nil => exact Nat.le_refl _
  | inventory _ _ _ _ _ ih => exact ih
  | call _ resources key ih => exact Nat.le_trans ih (call_clock (call_footprint _ resources key))

/-- Checkpoint rollback truncates relations only. Flow vectors, flow-map support,
charged work and the allocation birth clock remain at the attempted cut. -/
def rollback (saved current : Store) : Store :=
  { current with relations := current.relations.take saved.relations.length }

theorem rollback_relations {saved current : Store} (run : Run saved current) :
    (rollback saved current).relations = saved.relations := by
  obtain ⟨suffix, shape, _, _⟩ := relation_trace_undo (run_relation_trace run)
  simp [rollback, shape]

theorem rollback_retains_flows (saved current : Store) :
    (rollback saved current).flows = current.flows ∧
    (rollback saved current).flowKeys = current.flowKeys ∧
    (rollback saved current).workUsed = current.workUsed ∧
    (rollback saved current).clock = current.clock := ⟨rfl, rfl, rfl, rfl⟩

theorem rollback_native_maps {saved current : Store} (run : Run saved current) :
    (rollback saved current).keys =
      undoKeys (current.relations.drop saved.relations.length) current.keys ∧
    (rollback saved current).pairHeads =
      undoHeads (current.relations.drop saved.relations.length) current.pairHeads := by
  obtain ⟨suffix, shape, keys, pairs⟩ := relation_trace_undo (run_relation_trace run)
  have dropped : current.relations.drop saved.relations.length = suffix := by simp [shape]
  simp only [dropped, Store.keys, Store.pairHeads, rollback_relations run]
  exact ⟨keys.symm, pairs.symm⟩

theorem rollback_restores_maps {saved current : Store} (run : Run saved current) :
    (rollback saved current).keys = saved.keys ∧
    (rollback saved current).pairHeads = saved.pairHeads := by
  simp only [Store.keys, Store.pairHeads, rollback_relations run, and_self]

theorem rollback_valid {saved current : Store} (run : Run saved current)
    (valid : Valid saved) : Valid (rollback saved current) := by
  have actual := run_valid run valid
  have relations := rollback_relations run
  refine ⟨actual.flowDistinct, actual.noDefault, ?_, ?_, ?_, ?_⟩
  · rw [relations]; exact valid.relationDistinct
  · intro e member
    rw [relations] at member
    exact valid.encoded e member
  · intro e member
    rw [relations] at member
    exact run_flow_old run (valid.flow e member)
  · intro e member
    rw [relations] at member
    change e.birth < current.clock
    exact Nat.lt_of_lt_of_le (valid.born e member) (run_clock run)

inductive History : Store → Prop where
  | initial : History {}
  | commit {s u : Store} (history : History s) (run : Run s u) : History u
  | cancel {s u : Store} (history : History s) (run : Run s u) : History (rollback s u)

theorem history_valid {s : Store} (history : History s) : Valid s := by
  induction history with
  | initial => exact valid_empty
  | commit _ run ih => exact run_valid run ih
  | cancel _ run ih => exact rollback_valid run ih

/-- The physical-key reflection premise of the accepted Value-port Arena is
eliminated by the constructor history. The output Arena and raw ID are exact. -/
theorem history_success_arena {s u : Store} (history : History s)
    {resources : Resources} {key : Key} {id : Nat}
    (computed : relationWithScoped s resources key = (u, .ok id))
    (contexts : List Expr) (transformers : List NativeValuePorts.Transformer) :
    NativeValuePorts.Allowed key ∧ key.context ≤ resources.contextCount ∧
    u.readback id = some key ∧
    (s.arena contexts transformers).relation key = (u.arena contexts transformers, id) :=
  successful_physical_intern (history_valid history) computed contexts transformers

theorem history_stored_key_decodes {s : Store} (history : History s) {id : Nat} {entry : Entry}
    (found : s.relations[id]? = some entry) :
    s.decode entry.key = some entry.origin ∧ s.readback id = some entry.origin :=
  ⟨stored_key_decodes (history_valid history) (List.mem_of_getElem? found),
    complete_stored_readback (history_valid history) found⟩

theorem same_id_full_key {s : Store} {id : Nat} {left right : Key}
    (a : s.readback id = some left) (b : s.readback id = some right) : left = right := by
  rw [a] at b
  exact Option.some.inj b

theorem old_relation_readback {s u : Store} (history : History s) (run : Run s u)
    {id : Nat} {key : Key} (old : s.readback id = some key) : u.readback id = some key := by
  unfold Store.readback at old
  obtain ⟨entry, found, meaning⟩ := Option.bind_eq_some_iff.mp old
  have actual := stored_key_decodes (history_valid history) (List.mem_of_getElem? found)
  have original : entry.origin = key := by
    rw [meaning] at actual
    exact (Option.some.inj actual).symm
  obtain ⟨suffix, shape, _, _⟩ := relation_trace_undo (run_relation_trace run)
  have bound := (List.getElem?_eq_some_iff.mp found).1
  have retained : u.relations[id]? = some entry := by simpa [shape, List.getElem?_append_left bound] using found
  rw [← original]
  exact complete_stored_readback (run_valid run (history_valid history)) retained

theorem rollback_old_readback {saved current : Store} (history : History saved)
    (run : Run saved current) {id : Nat} {entry : Entry}
    (found : saved.relations[id]? = some entry) :
    (rollback saved current).readback id = some entry.origin :=
  complete_stored_readback (rollback_valid run (history_valid history))
    (by rw [rollback_relations run]; exact found)

theorem retry_birth_newer {saved current : Store} (history : History saved)
    (run : Run saved current) (key : Key) (flowId : Nat) {old : Entry}
    (removed : old ∈ current.relations) :
    old.birth < current.clock ∧
    (((rollback saved current).addRelation key flowId).relations[
      saved.relations.length]?).map Entry.birth = some current.clock := by
  refine ⟨(run_valid run (history_valid history)).born old removed, ?_⟩
  simp only [Store.addRelation]
  rw [rollback_relations run]
  simp [rollback]

theorem native_flow_map_insert (s : Store) (flow : Flow) (fresh : flow ∉ s.flows) :
    (s.addFlow flow).flowKeys = put s.flowKeys flow (s.flows.length + 1) := by
  funext query
  simp only [Store.flowKeys, Store.addFlow, cache_append s.flows flow fresh, put]
  split <;> simp

theorem native_relation_map_insert (s : Store) (key : Key) (id : Nat)
    (fresh : s.keys (encode key id) = none) :
    (s.addRelation key id).keys = put s.keys (encode key id) s.relations.length ∧
    (s.addRelation key id).pairHeads = put s.pairHeads key.pair s.relations.length := by
  have absent := (cache_none _ _).mp fresh
  constructor
  · simpa [Store.keys, Store.addRelation] using
      cache_append (s.relations.map Entry.key) (encode key id) absent
  · simp [Store.addRelation, Store.pairHeads, heads_append, encode]

theorem decoded_complete_fields {s : Store} {raw : RawKey} {key : Key}
    (decoded : s.decode raw = some key) :
    raw.pair = key.pair ∧ raw.context = key.context ∧ raw.sources = key.sources ∧
      s.flowAt raw.flowIndex = some key.flow := by
  obtain ⟨flow, found, value⟩ := Option.map_eq_some_iff.mp decoded
  cases value
  exact ⟨rfl, rfl, rfl, found⟩

theorem decoded_demand_fields {s : Store} {raw : RawKey} {key : Key} {demand : ScopedDemand}
    (decoded : s.decode raw = some key) (deferred : key.flow.demand = some demand) :
    ∃ flow, s.flowAt raw.flowIndex = some flow ∧ flow.transformer = key.flow.transformer ∧
      flow.demand = some ⟨demand.originalCall, demand.useInstance, demand.root,
        demand.outputScope, demand.inputRoute⟩ := by
  exact ⟨key.flow, (decoded_complete_fields decoded).2.2.2, rfl, deferred⟩

theorem same_id_across_forward_calls {s u w : Store} (history : History s) (run : Run s u)
    {left right : Key} {id : Nat} {resources : Resources}
    (old : s.readback id = some left)
    (computed : relationWithScoped u resources right = (w, .ok id)) : left = right := by
  have fullRun : Run s w := by simpa only [computed] using Run.call run resources right
  have retained := old_relation_readback history fullRun old
  have actual := (successful_physical_intern (run_valid run (history_valid history)) computed [] []).2.2.1
  exact same_id_full_key retained actual

theorem relation_reuse_before_reservation {s : Store} {key : Key} {flowId id : Nat}
    (found : s.keys (encode key flowId) = some id) (resources : Resources) :
    internRelation s resources key flowId = (s, .ok id) := by simp [internRelation, found]

theorem fresh_relation_constructor {s : Store} {key : Key} {flowId : Nat} {resources : Resources}
    (fresh : s.keys (encode key flowId) = none) (fits : s.relations.length < 2 ^ 32)
    (vector : resources.relationVector = true) (keys : resources.relationMap = true)
    (pairs : resources.pairMap = true) :
    internRelation s resources key flowId = (s.addRelation key flowId, .ok s.relations.length) := by
  simp [internRelation, fresh, Nat.not_le_of_gt fits, vector, keys, pairs]

namespace Examples

def demand : ScopedDemand := ⟨5, 6, 7, 8, 9⟩
def key : Key := ⟨.value .intPositive .intNegative, 0, some 11, ⟨0, some demand⟩⟩
def first : Store := (relationWithScoped {} {} key).1
def cancelled : Store := rollback {} first
def retryResources : Resources := { enabled := false, flowVector := false, flowMap := false }
def retried : Store := (relationWithScoped cancelled retryResources key).1

theorem first_success : relationWithScoped {} {} key = (first, .ok 0) := by decide

theorem first_history : History first := .commit .initial (.call (.nil _) {} key)

theorem cancellation_keeps_flow : cancelled.relations = [] ∧ cancelled.flows = [key.flow] ∧
    cancelled.workUsed = 1 ∧ cancelled.clock = 1 ∧ cancelled.flowId key.flow = some 1 := by decide

theorem retry_reuses_flow_raw_relation_id :
    relationWithScoped cancelled retryResources key = (retried, .ok 0) ∧
    retried.flows = first.flows ∧ retried.workUsed = first.workUsed ∧
    (first.relations[0]?).map Entry.birth = some 0 ∧
    (retried.relations[0]?).map Entry.birth = some 1 := by decide

def failureResources : Resources := { relationMap := false }
def afterFailure : Store := (relationWithScoped {} failureResources key).1

theorem failure_retains_allocated_flow :
    relationWithScoped {} failureResources key = (afterFailure, .error .exhausted) ∧
    afterFailure.flows = [key.flow] ∧ afterFailure.relations = [] ∧ afterFailure.workUsed = 1 ∧
    relationWithScoped afterFailure retryResources key = (afterFailure.addRelation key 1, .ok 0) := by decide

theorem partial_history : History afterFailure := .commit .initial (.call (.nil _) failureResources key)

def changedDemand : Key := { key with flow := ⟨0, some { demand with originalCall := 55 }⟩ }
def second : Store := (relationWithScoped first {} changedDemand).1

theorem complete_demand_distinguishes_keys :
    relationWithScoped first {} changedDemand = (second, .ok 1) ∧
    first.readback 0 = some key ∧ second.readback 0 = some key ∧
    second.readback 1 = some changedDemand ∧
    second.flows.length = 2 := by decide

theorem guard_order_and_no_mutation :
    relationWithScoped {} {} {key with context := 1, flow := ⟨3, some demand⟩} =
      ({}, .error .contextAssertion) ∧
    relationWithScoped {} {} {key with flow := ⟨3, some demand⟩} =
      ({}, .error .receiptMismatch) ∧
    relationWithScoped {} {} {key with pair := .effect .bottom .bottom, flow := ⟨3, some demand⟩} =
      ({}, .error .exhausted) ∧
    relationWithScoped {} {} {key with pair := .effect .bottom (.allowance 0)} =
      ({}, .error .receiptMismatch) := by decide

theorem charged_reservation_failure :
    let resources : Resources := {flowVector := false}
    relationWithScoped {} resources key = (({} : Store).charge, .error .exhausted) := by decide

theorem raw_id_not_global_identity :
    let different : Key := { key with sources := some 99 }
    let next := (relationWithScoped cancelled retryResources different).1
    next.readback 0 = some different ∧ first.readback 0 = some key ∧
    different ≠ key ∧ (next.relations[0]?).map Entry.birth = some 1 := by decide

end Examples
/-- Materialized native finite-map state. No lookup function is assumed correct:
`NativeHistory` below starts from empty maps and performs the actual updates. -/
structure Native where
  store : Store := {}
  flowCache : Map Flow := empty
  relationCache : Map RawKey := empty
  pairCache : Map Pair := empty

structure Coherent (n : Native) : Prop where
  flows : n.flowCache = n.store.flowKeys
  relations : n.relationCache = n.store.keys
  pairs : n.pairCache = n.store.pairHeads

def Native.charge (n : Native) : Native := { n with store := n.store.charge }
def Native.inventory (n : Native) (amount : Nat) : Native := { n with store := n.store.inventory amount }

def Native.addFlow (n : Native) (flow : Flow) : Native :=
  { n with
    store := n.store.addFlow flow
    flowCache := put n.flowCache flow (n.store.flows.length + 1) }

def Native.addRelation (n : Native) (key : Key) (flowId : Nat) : Native :=
  { n with
    store := { n.store with
      relations := n.store.relations ++
        [⟨encode key flowId, n.pairCache key.pair, n.store.clock, key⟩]
      clock := n.store.clock + 1 }
    relationCache := put n.relationCache (encode key flowId) n.store.relations.length
    pairCache := put n.pairCache key.pair n.store.relations.length }

def Native.rollback (saved current : Native) : Native :=
  { current with
    store := YulangClosure.NativeRelationInterner.rollback saved.store current.store
    relationCache := undoKeys (current.store.relations.drop saved.store.relations.length) current.relationCache
    pairCache := undoHeads (current.store.relations.drop saved.store.relations.length) current.pairCache }

theorem coherent_initial : Coherent ({} : Native) := by
  constructor <;> funext query <;> simp [empty, Store.flowKeys, Store.keys, Store.pairHeads, heads, headFold, cache]

theorem coherent_charge {n : Native} (coherent : Coherent n) : Coherent n.charge :=
  ⟨coherent.flows, coherent.relations, coherent.pairs⟩

theorem coherent_inventory {n : Native} (coherent : Coherent n) (amount : Nat) : Coherent (n.inventory amount) :=
  ⟨coherent.flows, coherent.relations, coherent.pairs⟩

theorem coherent_add_flow {n : Native} (coherent : Coherent n) {flow : Flow}
    (fresh : flow ∉ n.store.flows) : Coherent (n.addFlow flow) := by
  refine ⟨?_, coherent.relations, coherent.pairs⟩
  change put n.flowCache flow (n.store.flows.length + 1) = (n.store.addFlow flow).flowKeys
  rw [coherent.flows, native_flow_map_insert n.store flow fresh]

theorem native_relation_store {n : Native} (coherent : Coherent n) (key : Key) (flowId : Nat) :
    (n.addRelation key flowId).store = n.store.addRelation key flowId := by
  simp only [Native.addRelation, Store.addRelation, coherent.pairs]

theorem coherent_add_relation {n : Native} (coherent : Coherent n) {key : Key} {flowId : Nat}
    (fresh : n.store.keys (encode key flowId) = none) : Coherent (n.addRelation key flowId) := by
  have maps := native_relation_map_insert n.store key flowId fresh
  constructor
  · change n.flowCache = (n.addRelation key flowId).store.flowKeys
    rw [native_relation_store coherent]
    exact coherent.flows
  · change put n.relationCache (encode key flowId) n.store.relations.length =
      (n.addRelation key flowId).store.keys
    rw [native_relation_store coherent, coherent.relations, maps.1]
  · change put n.pairCache key.pair n.store.relations.length =
      (n.addRelation key flowId).store.pairHeads
    rw [native_relation_store coherent, coherent.pairs, maps.2]

theorem coherent_rollback {saved current : Native} (coherent : Coherent current)
    (run : Run saved.store current.store) : Coherent (Native.rollback saved current) := by
  have maps := rollback_native_maps run
  constructor
  · exact coherent.flows
  · change undoKeys _ current.relationCache = (rollback saved.store current.store).keys
    rw [coherent.relations, maps.1]
  · change undoHeads _ current.pairCache = (rollback saved.store current.store).pairHeads
    rw [coherent.pairs, maps.2]

/-- Native lookup decisions now read the stored maps, not reconstructed caches. -/
def Native.internFlow (n : Native) (resources : Resources) (flow : Flow) : Native × Result :=
  if flow = ({} : Flow) then (n, .ok 0)
  else match n.flowCache flow with
  | some id => (n, .ok id)
  | none =>
      if resources.enabled = false ∨ n.store.flows.length ≥ 4096 then (n, .error .exhausted)
      else if n.store.workUsed + 1 > resources.usizeMax then (n, .error .exhausted)
      else if n.store.workUsed + 1 > 65536 then (n, .error .exhausted)
      else
        let charged := n.charge
        if resources.flowVector = false then (charged, .error .exhausted)
        else if resources.flowMap = false then (charged, .error .exhausted)
        else if n.store.flows.length + 1 > resources.usizeMax then (charged, .error .exhausted)
        else (charged.addFlow flow, .ok (n.store.flows.length + 1))

def Native.internRelation (n : Native) (resources : Resources) (key : Key) (flowId : Nat) : Native × Result :=
  match n.relationCache (encode key flowId) with
  | some id => (n, .ok id)
  | none =>
      if n.store.relations.length ≥ 2 ^ 32 then (n, .error .exhausted)
      else if resources.relationVector = false then (n, .error .exhausted)
      else if resources.relationMap = false then (n, .error .exhausted)
      else if resources.pairMap = false then (n, .error .exhausted)
      else (n.addRelation key flowId, .ok n.store.relations.length)

def Native.call (n : Native) (resources : Resources) (key : Key) : Native × Result :=
  if key.context > resources.contextCount then (n, .error .contextAssertion)
  else match guards key with
  | some error => (n, .error error)
  | none =>
      let (afterFlow, result) := n.internFlow resources key.flow
      match result with
      | .error error => (afterFlow, .error error)
      | .ok flowId => afterFlow.internRelation resources key flowId

def forgetResult (result : Native × Result) : Store × Result := (result.1.store, result.2)

theorem native_flow_refinement {n : Native} (coherent : Coherent n) (resources : Resources) (flow : Flow) :
    forgetResult (n.internFlow resources flow) = internFlow n.store resources flow ∧
      Coherent (n.internFlow resources flow).1 := by
  unfold Native.internFlow internFlow
  rw [coherent.flows]
  split
  · exact ⟨rfl, coherent⟩
  · split
    · exact ⟨rfl, coherent⟩
    next missing =>
      have absent : flow ∉ n.store.flows := by
        unfold Store.flowKeys at missing
        simpa using missing
      split
      · exact ⟨rfl, coherent⟩
      · split
        · exact ⟨rfl, coherent⟩
        · split
          · exact ⟨rfl, coherent⟩
          · split
            · exact ⟨rfl, coherent_charge coherent⟩
            · split
              · exact ⟨rfl, coherent_charge coherent⟩
              · split
                · exact ⟨rfl, coherent_charge coherent⟩
                · exact ⟨rfl, coherent_add_flow (coherent_charge coherent) absent⟩

theorem native_relation_refinement {n : Native} (coherent : Coherent n) (resources : Resources)
    (key : Key) (flowId : Nat) :
    forgetResult (n.internRelation resources key flowId) = internRelation n.store resources key flowId ∧
      Coherent (n.internRelation resources key flowId).1 := by
  unfold Native.internRelation internRelation
  rw [coherent.relations]
  split
  · exact ⟨rfl, coherent⟩
  next missing =>
    split
    · exact ⟨rfl, coherent⟩
    · split
      · exact ⟨rfl, coherent⟩
      · split
        · exact ⟨rfl, coherent⟩
        · split
          · exact ⟨rfl, coherent⟩
          · exact ⟨by simp only [forgetResult, native_relation_store coherent], coherent_add_relation coherent missing⟩

theorem native_call_refinement {n : Native} (coherent : Coherent n) (resources : Resources) (key : Key) :
    forgetResult (n.call resources key) = relationWithScoped n.store resources key ∧
      Coherent (n.call resources key).1 := by
  unfold Native.call relationWithScoped
  split
  · exact ⟨rfl, coherent⟩
  · split
    · exact ⟨rfl, coherent⟩
    · have projected := native_flow_refinement coherent resources key.flow
      generalize output : n.internFlow resources key.flow = actual at projected ⊢
      rcases actual with ⟨middle, result⟩
      rw [← projected.1]
      cases result with
      | error error => exact ⟨rfl, projected.2⟩
      | ok id => exact native_relation_refinement projected.2 resources key id

inductive NativeRun : Native → Native → Prop where
  | nil (n : Native) : NativeRun n n
  | inventory {first last : Native} (prior : NativeRun first last) (amount usizeMax : Nat)
      (fits : last.store.workUsed + amount ≤ usizeMax) (bounded : last.store.workUsed + amount ≤ 65536) :
      NativeRun first (last.inventory amount)
  | call {first last : Native} (prior : NativeRun first last) (resources : Resources) (key : Key) :
      NativeRun first (last.call resources key).1

theorem native_run_refinement {first last : Native} (run : NativeRun first last)
    (coherent : Coherent first) : Coherent last ∧ Run first.store last.store := by
  induction run with
  | nil => exact ⟨coherent, .nil _⟩
  | inventory _ amount maximum fits bounded ih =>
      exact ⟨coherent_inventory ih.1 amount, .inventory ih.2 amount maximum fits bounded⟩
  | @call middle _ resources key ih =>
      have step := native_call_refinement ih.1 resources key
      refine ⟨step.2, ?_⟩
      have projected := congrArg Prod.fst step.1
      change (middle.call resources key).1.store =
        (relationWithScoped middle.store resources key).1 at projected
      rw [projected]
      exact Run.call ih.2 resources key

inductive NativeHistory : Native → Prop where
  | initial : NativeHistory {}
  | commit {first last : Native} (history : NativeHistory first) (run : NativeRun first last) : NativeHistory last
  | cancel {first last : Native} (history : NativeHistory first) (run : NativeRun first last) :
      NativeHistory (Native.rollback first last)

theorem native_history_refinement {n : Native} (history : NativeHistory n) :
    Coherent n ∧ History n.store := by
  induction history with
  | initial => exact ⟨coherent_initial, .initial⟩
  | commit _ run ih =>
      have projected := native_run_refinement run ih.1
      exact ⟨projected.1, .commit ih.2 projected.2⟩
  | cancel _ run ih =>
      have projected := native_run_refinement run ih.1
      exact ⟨coherent_rollback projected.1 projected.2, .cancel ih.2 projected.2⟩

/-- Actual materialized-map success supplies complete decoder readback and the
accepted Arena interner's SAME output/ID. No map-coherence or reflection premise
is exposed: both are generated from NativeHistory, including cancellation. -/
theorem native_success_arena {n next : Native} (history : NativeHistory n)
    {resources : Resources} {key : Key} {id : Nat}
    (computed : n.call resources key = (next, .ok id))
    (contexts : List Expr) (transformers : List NativeValuePorts.Transformer) :
    NativeValuePorts.Allowed key ∧ key.context ≤ resources.contextCount ∧
    next.store.readback id = some key ∧
    (n.store.arena contexts transformers).relation key = (next.store.arena contexts transformers, id) := by
  obtain ⟨coherent, projected⟩ := native_history_refinement history
  have actual := (native_call_refinement coherent resources key).1
  rw [computed] at actual
  exact history_success_arena projected actual.symm contexts transformers

/-- Success-only entry point, naming no chosen output or matching ID witness. -/
theorem native_ok_refines_arena {n : Native} (history : NativeHistory n)
    {resources : Resources} {key : Key} {id : Nat}
    (success : (n.call resources key).2 = .ok id)
    (contexts : List Expr) (transformers : List NativeValuePorts.Transformer) :
    let actual := (n.call resources key).1
    NativeValuePorts.Allowed key ∧ key.context ≤ resources.contextCount ∧
    actual.store.readback id = some key ∧
    (n.store.arena contexts transformers).relation key = (actual.store.arena contexts transformers, id) := by
  exact native_success_arena history (Prod.ext rfl success) contexts transformers

theorem native_stored_complete_key {n : Native} (history : NativeHistory n)
    {raw : RawKey} {id : Nat} (found : n.relationCache raw = some id) :
    ∃ entry, n.store.relations[id]? = some entry ∧ entry.key = raw ∧
      n.store.decode raw = some entry.origin ∧ n.store.readback id = some entry.origin := by
  obtain ⟨coherent, projected⟩ := native_history_refinement history
  rw [coherent.relations] at found
  have actual := cache_readback found
  rw [List.getElem?_map] at actual
  obtain ⟨entry, existsAt, keyIs⟩ := Option.map_eq_some_iff.mp actual
  have decoded := history_stored_key_decodes projected existsAt
  exact ⟨entry, existsAt, keyIs, by simpa only [keyIs] using decoded.1, decoded.2⟩

theorem native_cancel_maps_and_flows {saved current : Native} (history : NativeHistory saved)
    (run : NativeRun saved current) :
    (Native.rollback saved current).store.relations = saved.store.relations ∧
    (Native.rollback saved current).relationCache = saved.relationCache ∧
    (Native.rollback saved current).pairCache = saved.pairCache ∧
    (Native.rollback saved current).flowCache = current.flowCache ∧
    (Native.rollback saved current).store.flows = current.store.flows ∧
    (Native.rollback saved current).store.workUsed = current.store.workUsed := by
  obtain ⟨before, _⟩ := native_history_refinement history
  obtain ⟨after, projected⟩ := native_run_refinement run before
  have coherent := coherent_rollback after projected
  have restore := rollback_restores_maps projected
  exact ⟨rollback_relations projected,
    by rw [coherent.relations, before.relations]; exact restore.1,
    by rw [coherent.pairs, before.pairs]; exact restore.2,
    rfl, rfl, rfl⟩

namespace Examples

def physicalFirst : Native := (({} : Native).call {} key).1
def physicalCancelled : Native := Native.rollback {} physicalFirst
def physicalRetry : Native := (physicalCancelled.call retryResources key).1

theorem physical_first_history : NativeHistory physicalFirst :=
  .commit .initial (.call (.nil _) {} key)

theorem physical_cancelled_history : NativeHistory physicalCancelled :=
  .cancel .initial (.call (.nil _) {} key)

theorem physical_retry_history : NativeHistory physicalRetry :=
  .commit physical_cancelled_history (.call (.nil _) retryResources key)

theorem physical_maps_retry_exact :
    (({} : Native).call {} key).2 = .ok 0 ∧
    physicalFirst.flowCache key.flow = some 1 ∧
    physicalFirst.relationCache (encode key 1) = some 0 ∧
    physicalCancelled.flowCache key.flow = some 1 ∧
    physicalCancelled.relationCache (encode key 1) = none ∧
    (physicalCancelled.call retryResources key).2 = .ok 0 ∧
    physicalRetry.store.readback 0 = some key ∧
    (physicalRetry.store.relations[0]?).map Entry.birth = some 1 := by decide

theorem physical_partial_failure_exact :
    let actual := ({} : Native).call failureResources key
    actual.2 = .error .exhausted ∧ actual.1.flowCache key.flow = some 1 ∧
    actual.1.relationCache (encode key 1) = none ∧ actual.1.store.workUsed = 1 := by decide

end Examples
structure Bounds (s : Store) : Prop where
  flows : s.flows.length ≤ 4096
  relations : s.relations.length ≤ 2 ^ 32
  work : s.workUsed ≤ 65536

theorem flow_bounds {s : Store} (bounded : Bounds s) (resources : Resources) (flow : Flow) :
    Bounds (internFlow s resources flow).1 := by
  unfold internFlow
  split
  · exact bounded
  · split
    · exact bounded
    · split
      · exact bounded
      next room =>
        split
        · exact bounded
        · split
          · exact bounded
          next work =>
            have charged : Bounds s.charge := ⟨bounded.flows, bounded.relations, by
              change s.workUsed + 1 ≤ 65536; omega⟩
            split
            · exact charged
            · split
              · exact charged
              · split
                · exact charged
                · refine ⟨?_, bounded.relations, charged.work⟩
                  simp only [Store.addFlow, Store.charge, List.length_append, List.length_singleton]
                  omega

theorem relation_bounds {s : Store} (bounded : Bounds s) (resources : Resources) (key : Key) (flowId : Nat) :
    Bounds (internRelation s resources key flowId).1 := by
  unfold internRelation
  split
  · exact bounded
  · split
    · exact bounded
    next room =>
      split
      · exact bounded
      · split
        · exact bounded
        · split
          · exact bounded
          · refine ⟨bounded.flows, ?_, bounded.work⟩
            simp only [Store.addRelation, List.length_append, List.length_singleton]
            omega

theorem call_bounds {s : Store} (bounded : Bounds s) (resources : Resources) (key : Key) :
    Bounds (relationWithScoped s resources key).1 := by
  unfold relationWithScoped
  split
  · exact bounded
  · split
    · exact bounded
    · have afterFlow := flow_bounds bounded resources key.flow
      generalize value : internFlow s resources key.flow = output at afterFlow ⊢
      rcases output with ⟨middle, result⟩
      cases result with
      | error => exact afterFlow
      | ok id => exact relation_bounds afterFlow resources key id

theorem run_bounds {s u : Store} (run : Run s u) (bounded : Bounds s) : Bounds u := by
  induction run with
  | nil => exact bounded
  | inventory _ _ _ _ work ih => exact ⟨ih.flows, ih.relations, work⟩
  | call _ resources key ih => exact call_bounds ih resources key

theorem history_bounds {s : Store} (history : History s) : Bounds s := by
  induction history with
  | initial => constructor <;> decide
  | commit _ run ih => exact run_bounds run ih
  | cancel _ run ih =>
      have current := run_bounds run ih
      refine ⟨current.flows, ?_, current.work⟩
      rw [rollback_relations run]
      exact ih.relations

theorem native_history_bounds {n : Native} (history : NativeHistory n) : Bounds n.store :=
  history_bounds (native_history_refinement history).2

theorem native_success_u32 {n : Native} (history : NativeHistory n)
    {resources : Resources} {key : Key} {id : Nat}
    (success : (n.call resources key).2 = .ok id) : id < 2 ^ 32 := by
  have nextHistory : NativeHistory (n.call resources key).1 := .commit history (.call (.nil _) resources key)
  have meaning := (native_ok_refines_arena history success [] []).2.2.1
  unfold Store.readback at meaning
  obtain ⟨entry, found, _⟩ := Option.bind_eq_some_iff.mp meaning
  exact Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp found).1
    (native_history_bounds nextHistory).relations

theorem native_nondefault_flow_range {n : Native} (history : NativeHistory n)
    {flow : Flow} {id : Nat} (found : n.flowCache flow = some id) :
    0 < id ∧ id ≤ 4096 ∧ n.store.flowAt id = some flow := by
  have coherent := (native_history_refinement history).1
  rw [coherent.flows] at found
  obtain ⟨index, actual, rfl⟩ := Option.map_eq_some_iff.mp found
  have member := cache_readback actual
  have bound := (List.getElem?_eq_some_iff.mp member).1
  refine ⟨Nat.zero_lt_succ _, by have total := (native_history_bounds history).flows; omega, ?_⟩
  simpa [Store.flowAt] using member

end YulangClosure.NativeRelationInterner
