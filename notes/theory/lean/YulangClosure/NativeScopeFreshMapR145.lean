import YulangClosure.NativeFreshScopeTransport

/-!
R145 candidate, UNCHECKED. The packet prohibits Lean/Lake execution.

This localizes `NativeScopeTransformer.evaluate_rename` to finite supports
containing BOTH transformer coordinates and the incoming state. It supplies no
source-side support, allocation-cut, shared-map, or native execution receipt.
The original source/effect-hygiene and A/B obligations remain OPEN.
-/
namespace YulangClosure.NativeScopeFreshMapR145

open NativeScopeTransformer

def InjectiveOn (support : List Nat) (rename : Nat → Nat) : Prop :=
  ∀ a ∈ support, ∀ b ∈ support, rename a = rename b → a = b

def TransformerSupported (transformer : Transformer) (scopes tags : List Nat) : Prop :=
  (∀ tag ∈ transformer.stamped, tag ∈ tags) ∧
  ∀ pair ∈ transformer.scopes, pair.1 ∈ scopes ∧
    ∀ tag ∈ pair.2.missing, tag ∈ tags

def StateSupported (state : State) (scopes tags : List Nat) : Prop :=
  (∀ tag ∈ state.inputs, tag ∈ tags) ∧
  (∀ scope ∈ state.protections, scope ∈ scopes)

theorem mem_map_on_support (support items : List Nat) (rename : Nat → Nat)
    (injective : InjectiveOn support rename)
    (contained : ∀ item ∈ items, item ∈ support) (item : Nat)
    (valid : item ∈ support) :
    rename item ∈ items.map rename ↔ item ∈ items := by
  constructor
  · intro found
    obtain ⟨old, member, same⟩ := List.mem_map.mp found
    have equal := injective old (contained old member) item valid same
    exact equal ▸ member
  · intro member
    exact List.mem_map.mpr ⟨item, member, rfl⟩

theorem entry_rename_on_support (entries : List (Nat × Entry))
    (support : List Nat) (scopes tags : Nat → Nat)
    (injective : InjectiveOn support scopes)
    (contained : ∀ pair ∈ entries, pair.1 ∈ support)
    (scope : Nat) (valid : scope ∈ support) :
    entryAt (entries.map (fun pair => (scopes pair.1, pair.2.rename tags)))
      (scopes scope) = (entryAt entries scope).rename tags := by
  induction entries with
  | nil => rfl
  | cons pair rest ih =>
      rcases pair with ⟨key, entry⟩
      by_cases same : key = scope
      · subst key
        simp [entryAt]
      · have different : scopes key ≠ scopes scope := by
          intro equal
          exact same (injective key (contained (key, entry) (List.mem_cons_self ..))
            scope valid equal)
        have tail := ih (fun pair member => contained pair (List.mem_cons_of_mem _ member))
        simp [entryAt, same, different, tail]

theorem entry_missing_supported (entries : List (Nat × Entry)) (tags : List Nat)
    (contained : ∀ pair ∈ entries, ∀ tag ∈ pair.2.missing, tag ∈ tags)
    (scope tag : Nat) (member : tag ∈ (entryAt entries scope).missing) :
    tag ∈ tags := by
  induction entries with
  | nil => simp [entryAt, identityEntry] at member
  | cons pair rest ih =>
      rcases pair with ⟨key, entry⟩
      by_cases same : key = scope
      · simp only [entryAt, same, ↓reduceIte] at member
        exact contained (key, entry) (List.mem_cons_self ..) tag member
      · simp only [entryAt, same, ↓reduceIte] at member
        exact ih (fun pair present => contained pair (List.mem_cons_of_mem _ present)) member

theorem missing_rename_on_support (support guards inputs : List Nat)
    (rename : Nat → Nat) (injective : InjectiveOn support rename)
    (guardSupport : ∀ tag ∈ guards, tag ∈ support)
    (inputSupport : ∀ tag ∈ inputs, tag ∈ support) :
    Missing (guards.map rename) (inputs.map rename) ↔ Missing guards inputs := by
  constructor
  · rintro ⟨image, member, absent⟩
    obtain ⟨tag, present, rfl⟩ := List.mem_map.mp member
    exact ⟨tag, present, fun found => absent (List.mem_map.mpr ⟨tag, found, rfl⟩)⟩
  · rintro ⟨tag, member, absent⟩
    refine ⟨rename tag, List.mem_map.mpr ⟨tag, member, rfl⟩, ?_⟩
    intro found
    exact absent ((mem_map_on_support support inputs rename injective inputSupport
      tag (guardSupport tag member)).mp found)

theorem renamed_protection_on_support (transformer : Transformer) (state : State)
    (scopeSupport tagSupport : List Nat) (scopes tags : Nat → Nat)
    (transformerSupport : TransformerSupported transformer scopeSupport tagSupport)
    (stateSupport : StateSupported state scopeSupport tagSupport)
    (scopeInjection : InjectiveOn scopeSupport scopes)
    (tagInjection : InjectiveOn tagSupport tags)
    (scope : Nat) (valid : scope ∈ scopeSupport) :
    scopes scope ∈ ((transformer.rename scopes tags).evaluate
      (state.rename scopes tags)).protections ↔
    scope ∈ (transformer.evaluate state).protections := by
  have entryEqual := entry_rename_on_support transformer.scopes scopeSupport scopes tags
    scopeInjection (fun pair member => (transformerSupport.2 pair member).1) scope valid
  have guardSupport : ∀ tag ∈ (transformer.entry scope).missing, tag ∈ tagSupport := by
    intro tag member
    exact entry_missing_supported transformer.scopes tagSupport
      (fun pair present => (transformerSupport.2 pair present).2) scope tag member
  simp only [evaluate_protection, Transformer.entry, Transformer.rename]
  rw [entryEqual]
  simp only [Entry.rename, State.rename,
    mem_map_on_support scopeSupport state.protections scopes scopeInjection stateSupport.2 scope valid,
    missing_rename_on_support tagSupport _ state.inputs tags tagInjection guardSupport stateSupport.1]

/-- Same conclusion as the global-injective law. Injection is required only
on finite supports containing the transformer AND the incoming state. -/
theorem evaluate_rename_on_support (transformer : Transformer) (state : State)
    (scopeSupport tagSupport : List Nat) (scopes tags : Nat → Nat)
    (transformerSupport : TransformerSupported transformer scopeSupport tagSupport)
    (stateSupport : StateSupported state scopeSupport tagSupport)
    (scopeInjection : InjectiveOn scopeSupport scopes)
    (tagInjection : InjectiveOn tagSupport tags) :
    Equivalent ((transformer.rename scopes tags).evaluate (state.rename scopes tags))
      ((transformer.evaluate state).rename scopes tags) := by
  constructor
  · intro tag
    simp only [Transformer.evaluate, Transformer.rename, State.rename, List.map_append]
  · intro observed
    constructor
    · intro present
      have origin : ∃ scope ∈ scopeSupport, scopes scope = observed := by
        rcases (evaluate_protection _ _ _).mp present with inherited | added
        · obtain ⟨scope, member, same⟩ := List.mem_map.mp inherited.2
          exact ⟨scope, stateSupport.2 scope member, same⟩
        · have member := missing_has_entry (transformer.rename scopes tags) observed
            (state.rename scopes tags).inputs added
          simp only [keys, Transformer.rename, List.map_map, Function.comp_def] at member
          obtain ⟨pair, member, same⟩ := List.mem_map.mp member
          exact ⟨pair.1, (transformerSupport.2 pair member).1, same⟩
      obtain ⟨scope, valid, same⟩ := origin
      subst observed
      exact List.mem_map.mpr ⟨scope,
        (renamed_protection_on_support transformer state scopeSupport tagSupport scopes tags
          transformerSupport stateSupport scopeInjection tagInjection scope valid).mp present, rfl⟩
    · intro present
      obtain ⟨scope, member, same⟩ := List.mem_map.mp present
      have valid : scope ∈ scopeSupport := by
        rcases (evaluate_protection transformer state scope).mp member with inherited | added
        · exact stateSupport.2 scope inherited.2
        · obtain ⟨pair, member, equal⟩ :=
            List.mem_map.mp (missing_has_entry transformer scope state.inputs added)
          exact equal ▸ (transformerSupport.2 pair member).1
      subst observed
      exact (renamed_protection_on_support transformer state scopeSupport tagSupport scopes tags
        transformerSupport stateSupport scopeInjection tagInjection scope valid).mpr member

/-- Concrete allocation specialization. The complete pre-copy support bounds
remain premises; the allocation model supplies injection, including duplicate
copy keys. There is no asserted R145 source instantiation. -/
theorem fresh_evaluate_on_support (transformer : Transformer) (state : State)
    (scopeSupport tagSupport : List Nat) (scopeCount tagCount : Nat)
    (scopeKeys tagKeys : List Nat)
    (transformerSupport : TransformerSupported transformer scopeSupport tagSupport)
    (stateSupport : StateSupported state scopeSupport tagSupport)
    (scopeBound : ∀ scope ∈ scopeSupport, scope < scopeCount)
    (tagBound : ∀ tag ∈ tagSupport, tag < tagCount) :
    let scopes := (NativeFreshScopeTransport.fresh scopeCount scopeKeys).remap
    let tags := (NativeFreshScopeTransport.fresh tagCount tagKeys).remap
    Equivalent ((transformer.rename scopes tags).evaluate (state.rename scopes tags))
      ((transformer.evaluate state).rename scopes tags) := by
  apply evaluate_rename_on_support transformer state scopeSupport tagSupport _ _
    transformerSupport stateSupport
  · intro a one b two same
    exact NativeFreshScopeTransport.fresh_injective_on_old scopeCount scopeKeys a b
      (scopeBound a one) (scopeBound b two) same
  · intro a one b two same
    exact NativeFreshScopeTransport.fresh_injective_on_old tagCount tagKeys a b
      (tagBound a one) (tagBound b two) same

-- Audit directives are intentionally not executed in R145.
#check @YulangClosure.NativeScopeFreshMapR145.mem_map_on_support
#print axioms YulangClosure.NativeScopeFreshMapR145.mem_map_on_support
#check @YulangClosure.NativeScopeFreshMapR145.entry_rename_on_support
#print axioms YulangClosure.NativeScopeFreshMapR145.entry_rename_on_support
#check @YulangClosure.NativeScopeFreshMapR145.entry_missing_supported
#print axioms YulangClosure.NativeScopeFreshMapR145.entry_missing_supported
#check @YulangClosure.NativeScopeFreshMapR145.missing_rename_on_support
#print axioms YulangClosure.NativeScopeFreshMapR145.missing_rename_on_support
#check @YulangClosure.NativeScopeFreshMapR145.renamed_protection_on_support
#print axioms YulangClosure.NativeScopeFreshMapR145.renamed_protection_on_support
#check @YulangClosure.NativeScopeFreshMapR145.evaluate_rename_on_support
#print axioms YulangClosure.NativeScopeFreshMapR145.evaluate_rename_on_support
#check @YulangClosure.NativeScopeFreshMapR145.fresh_evaluate_on_support
#print axioms YulangClosure.NativeScopeFreshMapR145.fresh_evaluate_on_support

end YulangClosure.NativeScopeFreshMapR145
