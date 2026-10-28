import YulangClosure.NativeScopeTransformer

/-!
The successful ID-allocation projection of `ScopeInventory::fresh` in
`candidate_source.rs`: the fresh counter increases on every copied key and
`HashMap::insert` overwrites that key's image. Uncopied keys use their identity
image. Scopes and input tags have separate counters and use the same algorithm.

The native map is NOT injective on all natural numbers: a fresh image has an
identity image when it is outside the old inventory. We construct a globally
injective ghost extension which agrees on the entire old inventory, then use
the existing scope-transformer theorem on valid incoming states. No supplied
injectivity, collision-free map, or final commutation law is a premise.

This does not identify arbitrary source states with well-formed native
inventories, prove allocation/resource success, or complete full effect
semantics. It models the exact ID projection after successful allocation;
region ownership, origin payloads and fallible Rust execution remain separate.
-/
namespace YulangClosure.NativeFreshScopeTransport

open NativeScopeTransformer

def swap (first second value : Nat) : Nat :=
  if value = first then second else if value = second then first else value

theorem swap_involution (first second value : Nat) :
    swap first second (swap first second value) = value := by
  by_cases one : value = first
  · subst value
    by_cases same : first = second <;> simp [swap, same, Ne.symm]
  · by_cases two : value = second
    · subst value
      simp [swap, one]
    · simp [swap, one, two]

theorem swap_injective (first second : Nat) : Function.Injective (swap first second) := by
  intro x y same
  have equal := congrArg (swap first second) same
  simpa only [swap_involution] using equal

structure CopyState where
  next : Nat
  remap : Nat → Nat

def initial (count : Nat) : CopyState := ⟨count, id⟩

def allocate (state : CopyState) (key : Nat) : CopyState :=
  ⟨state.next + 1, fun old => if old = key then state.next else state.remap old⟩

def copy (state : CopyState) : List Nat → CopyState
  | [] => state
  | key :: rest => copy (allocate state key) rest

def fresh (count : Nat) (keys : List Nat) : CopyState := copy (initial count) keys

/-- Agreement is needed on the whole old inventory, including external names
absent from the transformer's own support. The extension is proof-only. -/
structure Extends (count : Nat) (state : CopyState) : Prop where
  bounded : ∀ old, old < count → state.remap old < state.next
  extension : ∃ permutation : Nat → Nat, Function.Injective permutation ∧
    ∀ old, old < count → permutation old = state.remap old

theorem initial_extends (count : Nat) : Extends count (initial count) :=
  ⟨fun _ valid => valid, id, fun _ _ equal => equal, fun _ _ => rfl⟩

theorem allocate_extends (count : Nat) (state : CopyState) (key : Nat)
    (old : Extends count state) : Extends count (allocate state key) := by
  obtain ⟨permutation, injective, agrees⟩ := old.extension
  constructor
  · intro name valid
    simp only [allocate]
    split
    · omega
    · exact Nat.lt_trans (old.bounded name valid) (Nat.lt_succ_self _)
  · refine ⟨fun name => swap (permutation key) state.next (permutation name),
      (swap_injective _ _).comp injective, ?_⟩
    intro name valid
    by_cases equal : name = key
    · subst name
      simp [allocate, swap]
    · have distinct : permutation name ≠ permutation key := fun same => equal (injective same)
      have below : permutation name < state.next := by rw [agrees name valid]; exact old.bounded name valid
      simp only [allocate, ite_eq_right equal, swap, ite_eq_right distinct, ite_eq_right (Nat.ne_of_lt below)]
      exact agrees name valid

theorem copy_extends (count : Nat) (state : CopyState) (keys : List Nat)
    (old : Extends count state) : Extends count (copy state keys) := by
  induction keys generalizing state with
  | nil => exact old
  | cons key rest ih => exact ih (allocate state key) (allocate_extends count state key old)

theorem fresh_extends (count : Nat) (keys : List Nat) : Extends count (fresh count keys) :=
  copy_extends count (initial count) keys (initial_extends count)

theorem copy_next (state : CopyState) (keys : List Nat) :
    (copy state keys).next = state.next + keys.length := by
  induction keys generalizing state with
  | nil => simp [copy]
  | cons key rest ih => simp [copy, ih, allocate, Nat.add_comm, Nat.add_left_comm]

theorem fresh_next (count : Nat) (keys : List Nat) :
    (fresh count keys).next = count + keys.length := by
  exact copy_next (initial count) keys

theorem fresh_old_bounded (count : Nat) (keys : List Nat) (old : Nat)
    (valid : old < count) : (fresh count keys).remap old < count + keys.length := by
  simpa only [← fresh_next] using (fresh_extends count keys).bounded old valid

theorem fresh_injective_on_old (count : Nat) (keys : List Nat) (first second : Nat)
    (one : first < count) (two : second < count)
    (same : (fresh count keys).remap first = (fresh count keys).remap second) :
    first = second := by
  obtain ⟨permutation, injective, agrees⟩ := (fresh_extends count keys).extension
  apply injective
  rw [agrees first one, agrees second two]
  exact same

theorem copy_untouched (state : CopyState) (keys : List Nat) (old : Nat)
    (absent : old ∉ keys) : (copy state keys).remap old = state.remap old := by
  induction keys generalizing state with
  | nil => rfl
  | cons key rest ih =>
      simp only [List.mem_cons, not_or] at absent
      rw [copy, ih (allocate state key) absent.2]
      simp [allocate, absent.1]

theorem fresh_untouched (count : Nat) (keys : List Nat) (old : Nat)
    (absent : old ∉ keys) : (fresh count keys).remap old = old :=
  copy_untouched (initial count) keys old absent

theorem copy_touched_range (state : CopyState) (keys : List Nat) (old : Nat)
    (present : old ∈ keys) :
    state.next ≤ (copy state keys).remap old ∧
      (copy state keys).remap old < (copy state keys).next := by
  induction keys generalizing state with
  | nil => simp at present
  | cons key rest ih =>
      by_cases later : old ∈ rest
      · have result := ih (allocate state key) later
        exact ⟨Nat.le_trans (Nat.le_succ _) result.1, result.2⟩
      · have equal : old = key := (List.mem_cons.mp present).resolve_right later
        subst old
        rw [copy, copy_untouched _ _ _ later]
        simp only [allocate, ↓reduceIte]
        rw [copy_next]
        change state.next ≤ state.next ∧ state.next < state.next + 1 + rest.length
        omega

theorem fresh_touched_range (count : Nat) (keys : List Nat) (old : Nat)
    (present : old ∈ keys) :
    count ≤ (fresh count keys).remap old ∧
      (fresh count keys).remap old < count + keys.length := by
  simpa only [fresh, initial, copy_next] using copy_touched_range (initial count) keys old present

theorem fresh_copied_disjoint_from_fixed (count : Nat) (keys : List Nat)
    (copied fixed : Nat) (present : copied ∈ keys) (valid : fixed < count)
    (absent : fixed ∉ keys) : (fresh count keys).remap copied ≠ (fresh count keys).remap fixed := by
  rw [fresh_untouched count keys fixed absent]
  have lower := (fresh_touched_range count keys copied present).1
  omega

/-- Validity refers to the pre-copy inventories, not only copied local names. -/
def StateValid (scopeCount tagCount : Nat) (state : State) : Prop :=
  (∀ tag ∈ state.inputs, tag < tagCount) ∧
  (∀ scope ∈ state.protections, scope < scopeCount)

def TransformerValid (scopeCount tagCount : Nat) (transformer : Transformer) : Prop :=
  (∀ tag ∈ transformer.stamped, tag < tagCount) ∧
  ∀ pair ∈ transformer.scopes, pair.1 < scopeCount ∧
    ∀ tag ∈ pair.2.missing, tag < tagCount

theorem evaluate_valid (scopeCount tagCount : Nat) (transformer : Transformer) (state : State)
    (validTransformer : TransformerValid scopeCount tagCount transformer)
    (validState : StateValid scopeCount tagCount state) :
    StateValid scopeCount tagCount (transformer.evaluate state) := by
  constructor
  · intro tag present
    rcases List.mem_append.mp present with old | stamped
    · exact validState.1 tag old
    · exact validTransformer.1 tag stamped
  · intro scope present
    rcases List.mem_append.mp present with old | new
    · exact validState.2 scope (List.mem_filter.mp old).1
    · obtain ⟨pair, member, equal⟩ := List.mem_map.mp (List.mem_filter.mp new).1
      exact equal ▸ (validTransformer.2 pair member).1

theorem map_eq_on_support {α β : Type} (items : List α) (first second : α → β)
    (agree : ∀ item ∈ items, first item = second item) : items.map first = items.map second := by
  induction items with
  | nil => rfl
  | cons head rest ih =>
      simp only [List.map_cons]
      rw [agree head (List.mem_cons_self ..), ih (fun item member => agree item (List.mem_cons_of_mem _ member))]

theorem state_rename_agrees (scopeCount tagCount : Nat) (state : State)
    (valid : StateValid scopeCount tagCount state)
    (scopes scopes' tags tags' : Nat → Nat)
    (scopeAgreement : ∀ scope, scope < scopeCount → scopes scope = scopes' scope)
    (tagAgreement : ∀ tag, tag < tagCount → tags tag = tags' tag) :
    state.rename scopes tags = state.rename scopes' tags' := by
  have inputs := map_eq_on_support state.inputs tags tags' (fun tag member => tagAgreement tag (valid.1 tag member))
  have protections := map_eq_on_support state.protections scopes scopes'
    (fun scope member => scopeAgreement scope (valid.2 scope member))
  simp only [State.rename, inputs, protections]

theorem transformer_rename_agrees (scopeCount tagCount : Nat) (transformer : Transformer)
    (valid : TransformerValid scopeCount tagCount transformer)
    (scopes scopes' tags tags' : Nat → Nat)
    (scopeAgreement : ∀ scope, scope < scopeCount → scopes scope = scopes' scope)
    (tagAgreement : ∀ tag, tag < tagCount → tags tag = tags' tag) :
    transformer.rename scopes tags = transformer.rename scopes' tags' := by
  have stamped := map_eq_on_support transformer.stamped tags tags'
    (fun tag member => tagAgreement tag (valid.1 tag member))
  have pairs : transformer.scopes.map (fun pair => (scopes pair.1, pair.2.rename tags)) =
      transformer.scopes.map (fun pair => (scopes' pair.1, pair.2.rename tags')) := by
    apply map_eq_on_support
    intro pair member
    have bound := valid.2 pair member
    have missing := map_eq_on_support pair.2.missing tags tags'
      (fun tag present => tagAgreement tag (bound.2 tag present))
    simp only [scopeAgreement pair.1 bound.1, Entry.rename, missing]
  simp only [Transformer.rename, stamped, pairs]

theorem fresh_state_valid (scopeCount tagCount : Nat) (scopeKeys tagKeys : List Nat)
    (state : State) (valid : StateValid scopeCount tagCount state) :
    StateValid (scopeCount + scopeKeys.length) (tagCount + tagKeys.length)
      (state.rename (fresh scopeCount scopeKeys).remap (fresh tagCount tagKeys).remap) := by
  constructor
  · intro tag present
    obtain ⟨old, member, rfl⟩ := List.mem_map.mp present
    exact fresh_old_bounded tagCount tagKeys old (valid.1 old member)
  · intro scope present
    obtain ⟨old, member, rfl⟩ := List.mem_map.mp present
    exact fresh_old_bounded scopeCount scopeKeys old (valid.2 old member)

theorem fresh_transformer_valid (scopeCount tagCount : Nat) (scopeKeys tagKeys : List Nat)
    (transformer : Transformer) (valid : TransformerValid scopeCount tagCount transformer) :
    TransformerValid (scopeCount + scopeKeys.length) (tagCount + tagKeys.length)
      (transformer.rename (fresh scopeCount scopeKeys).remap (fresh tagCount tagKeys).remap) := by
  constructor
  · intro tag present
    obtain ⟨old, member, rfl⟩ := List.mem_map.mp present
    exact fresh_old_bounded tagCount tagKeys old (valid.1 old member)
  · intro pair present
    obtain ⟨old, member, rfl⟩ := List.mem_map.mp present
    refine ⟨fresh_old_bounded scopeCount scopeKeys old.1 (valid.2 old member).1, ?_⟩
    intro tag present
    obtain ⟨oldTag, memberTag, rfl⟩ := List.mem_map.mp present
    exact fresh_old_bounded tagCount tagKeys oldTag ((valid.2 old member).2 oldTag memberTag)

/-- The actual overwrite-or-identity map commutes with native scope evaluation
on the ENTIRE valid old state. Allocated names, including repeated keys, supply
the required injection; it is not an input hypothesis. -/
theorem fresh_evaluate (scopeCount tagCount : Nat) (scopeKeys tagKeys : List Nat)
    (transformer : Transformer) (state : State)
    (validTransformer : TransformerValid scopeCount tagCount transformer)
    (validState : StateValid scopeCount tagCount state) :
    let scopes := (fresh scopeCount scopeKeys).remap
    let tags := (fresh tagCount tagKeys).remap
    Equivalent ((transformer.rename scopes tags).evaluate (state.rename scopes tags))
      ((transformer.evaluate state).rename scopes tags) := by
  obtain ⟨scopes, scopeInjection, scopeAgreement⟩ := (fresh_extends scopeCount scopeKeys).extension
  obtain ⟨tags, tagInjection, tagAgreement⟩ := (fresh_extends tagCount tagKeys).extension
  have transformerEqual := transformer_rename_agrees scopeCount tagCount transformer validTransformer
    scopes (fresh scopeCount scopeKeys).remap tags (fresh tagCount tagKeys).remap scopeAgreement tagAgreement
  have initialEqual := state_rename_agrees scopeCount tagCount state validState
    scopes (fresh scopeCount scopeKeys).remap tags (fresh tagCount tagKeys).remap scopeAgreement tagAgreement
  have outputEqual := state_rename_agrees scopeCount tagCount (transformer.evaluate state)
    (evaluate_valid scopeCount tagCount transformer state validTransformer validState)
    scopes (fresh scopeCount scopeKeys).remap tags (fresh tagCount tagKeys).remap scopeAgreement tagAgreement
  have natural := evaluate_rename transformer state scopes tags scopeInjection tagInjection
  rw [transformerEqual, initialEqual, outputEqual] at natural
  exact natural

/-- Both preservation equations and the output inventory validity needed by
the next copy are constructed. The number of later copies is unrestricted. -/
theorem fresh_evaluate_and_reuse (scopeCount tagCount : Nat) (scopeKeys tagKeys : List Nat)
    (transformer : Transformer) (state : State)
    (validTransformer : TransformerValid scopeCount tagCount transformer)
    (validState : StateValid scopeCount tagCount state) :
    let scopes := (fresh scopeCount scopeKeys).remap
    let tags := (fresh tagCount tagKeys).remap
    let renamedTransformer := transformer.rename scopes tags
    let renamedState := state.rename scopes tags
    Equivalent (renamedTransformer.evaluate renamedState)
      ((transformer.evaluate state).rename scopes tags) ∧
    TransformerValid (scopeCount + scopeKeys.length) (tagCount + tagKeys.length) renamedTransformer ∧
    StateValid (scopeCount + scopeKeys.length) (tagCount + tagKeys.length)
      (renamedTransformer.evaluate renamedState) := by
  refine ⟨fresh_evaluate scopeCount tagCount scopeKeys tagKeys transformer state validTransformer validState,
    fresh_transformer_valid scopeCount tagCount scopeKeys tagKeys transformer validTransformer, ?_⟩
  exact evaluate_valid _ _ _ _
    (fresh_transformer_valid scopeCount tagCount scopeKeys tagKeys transformer validTransformer)
    (fresh_state_valid scopeCount tagCount scopeKeys tagKeys state validState)

/-- The global injection premise in the older theorem is not literally true
of the native map. The new theorem uses valid old support instead. -/
theorem native_map_not_globally_injective :
    ¬ Function.Injective (fresh 2 [0]).remap := by
  intro injective
  have impossible : (0 : Nat) = 2 := injective (show (fresh 2 [0]).remap 0 = (fresh 2 [0]).remap 2 from rfl)
  omega

theorem repeated_key_overwrites_without_old_collision :
    (fresh 2 [0, 0]).next = 4 ∧
    (fresh 2 [0, 0]).remap 0 = 3 ∧ (fresh 2 [0, 0]).remap 1 = 1 ∧
    ∀ first < 2, ∀ second < 2,
      (fresh 2 [0, 0]).remap first = (fresh 2 [0, 0]).remap second → first = second := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro first one second two same
  exact fresh_injective_on_old 2 [0, 0] first second one two same

/-- An external old protection survives a copied local release. It is outside
the local transformer's support but inside the inventory covered by allocation. -/
theorem external_protection_survives_local_release :
    let scopes := (fresh 2 [0]).remap
    let transformer := release 0
    let state : State := ⟨[], [1]⟩
    Equivalent ((transformer.rename scopes id).evaluate (state.rename scopes id))
      ((transformer.evaluate state).rename scopes id) ∧
    ((transformer.rename scopes id).evaluate (state.rename scopes id)).protections = [1] := by
  constructor
  · exact fresh_evaluate 2 0 [0] [] (release 0) ⟨[], [1]⟩
      (by simp [TransformerValid, release]) (by simp [StateValid])
  · rfl

end YulangClosure.NativeFreshScopeTransport
