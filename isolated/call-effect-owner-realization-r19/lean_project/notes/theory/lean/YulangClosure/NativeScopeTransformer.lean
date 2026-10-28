import Std

/-!
The finite normal-form CONTENT of `candidate_scope.rs`, with the same stamped
tags, per-scope keep bit, missing-tag disjunction, and ordered composition.
This formalizes the already reviewed algebra in
`2026-10-15-compose-scoped-release-construction.md` §2. Lists below represent
sets by membership; their sorting, allocation errors, and Rust loop execution
are not identified with Lean reduction. The entire contribution witness stays
outside these two coordinates, exactly as in the native module.

In particular composition is proved from its actual formula, not supplied as
a law. This does not construct original source attribution, the shared FreshUse
map, or the interpretation of every Context/Call/effect guard.
-/
namespace YulangClosure.NativeScopeTransformer

structure Entry where
  keep : Bool := true
  missing : List Nat := []
  deriving DecidableEq, Repr

def identityEntry : Entry := ⟨true, []⟩

def entryAt : List (Nat × Entry) → Nat → Entry
  | [], _ => identityEntry
  | (scope, entry) :: rest, wanted =>
      if scope = wanted then entry else entryAt rest wanted

def keys (entries : List (Nat × Entry)) : List Nat := entries.map Prod.fst

theorem entryAt_absent (entries : List (Nat × Entry)) (scope : Nat)
    (absent : scope ∉ keys entries) : entryAt entries scope = identityEntry := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
      rcases head with ⟨key, entry⟩
      simp only [keys, List.map_cons, List.mem_cons, not_or] at absent
      simp only [entryAt, Ne.symm absent.1, ↓reduceIte]
      exact ih absent.2

/-- Native identity entries are omitted, while release tombstones remain. -/
def encode (support : List Nat) (value : Nat → Entry) : List (Nat × Entry) :=
  support.filterMap fun scope =>
    if value scope = identityEntry then none else some (scope, value scope)

theorem entryAt_encode (support : List Nat) (value : Nat → Entry) (scope : Nat) :
    entryAt (encode support value) scope =
      if scope ∈ support then value scope else identityEntry := by
  induction support with
  | nil => simp [encode, entryAt]
  | cons head rest ih =>
      simp only [encode] at ih
      by_cases same : head = scope
      · subst head
        by_cases neutral : value scope = identityEntry
        · simp [encode, neutral, ih]
        · simp [encode, neutral, entryAt]
      · by_cases neutral : value head = identityEntry
        · simp [encode, neutral, Ne.symm same, ih]
        · simp [encode, neutral, entryAt, same, Ne.symm same, ih]

structure Transformer where
  stamped : List Nat := []
  scopes : List (Nat × Entry) := []
  deriving DecidableEq, Repr

def Transformer.entry (transformer : Transformer) (scope : Nat) : Entry :=
  entryAt transformer.scopes scope

structure State where
  inputs : List Nat := []
  protections : List Nat := []
  deriving DecidableEq, Repr

def Missing (guards inputs : List Nat) : Prop := ∃ tag ∈ guards, tag ∉ inputs

instance (guards inputs : List Nat) : Decidable (Missing guards inputs) :=
  inferInstanceAs (Decidable (∃ tag ∈ guards, tag ∉ inputs))

@[simp] theorem missing_nil (inputs : List Nat) : ¬ Missing [] inputs := by
  simp [Missing]

theorem missing_append (first second inputs : List Nat) :
    Missing (first ++ second) inputs ↔ Missing first inputs ∨ Missing second inputs := by
  simp [Missing, or_and_right, exists_or]

theorem missing_retained (guards stamps inputs : List Nat) :
    Missing (guards.filter fun tag => decide (tag ∉ stamps)) inputs ↔
      Missing guards (inputs ++ stamps) := by
  simp only [Missing, List.mem_filter, decide_eq_true_eq, List.mem_append, not_or]
  constructor
  · rintro ⟨tag, ⟨member, unstamped⟩, absent⟩
    exact ⟨tag, member, absent, unstamped⟩
  · rintro ⟨tag, member, absent, unstamped⟩
    exact ⟨tag, ⟨member, unstamped⟩, absent⟩

def composeEntry (first second : Entry) (firstStamps : List Nat) : Entry :=
  ⟨first.keep && second.keep,
    (if second.keep then first.missing else []) ++
      second.missing.filter (fun tag => decide (tag ∉ firstStamps))⟩

def Transformer.then (first second : Transformer) : Transformer :=
  { stamped := first.stamped ++ second.stamped
    scopes := encode (keys first.scopes ++ keys second.scopes)
      (fun scope => composeEntry (first.entry scope) (second.entry scope) first.stamped) }

theorem then_entry (first second : Transformer) (scope : Nat) :
    (first.then second).entry scope =
      composeEntry (first.entry scope) (second.entry scope) first.stamped := by
  simp only [Transformer.entry, Transformer.then, entryAt_encode]
  split
  · rfl
  · rename_i absent
    simp only [List.mem_append, not_or] at absent
    rw [entryAt_absent _ _ absent.1, entryAt_absent _ _ absent.2]
    rfl

theorem compose_missing (first second : Entry) (stamps inputs : List Nat) :
    Missing (composeEntry first second stamps).missing inputs ↔
      (second.keep = true ∧ Missing first.missing inputs) ∨
        Missing second.missing (inputs ++ stamps) := by
  simp only [composeEntry, missing_append, missing_retained]
  cases second.keep <;> simp

/-- Both tests use the original input tags, not the newly stamped output. -/
def Transformer.evaluate (transformer : Transformer) (initial : State) : State :=
  { inputs := initial.inputs ++ transformer.stamped
    protections :=
      initial.protections.filter (fun scope => (transformer.entry scope).keep) ++
      (keys transformer.scopes).filter
        (fun scope => decide (Missing (transformer.entry scope).missing initial.inputs)) }

theorem missing_has_entry (transformer : Transformer) (scope : Nat) (inputs : List Nat)
    (added : Missing (transformer.entry scope).missing inputs) :
    scope ∈ keys transformer.scopes := by
  by_cases present : scope ∈ keys transformer.scopes
  · exact present
  · have neutral := entryAt_absent transformer.scopes scope present
    simp only [Transformer.entry, neutral, identityEntry] at added
    exact False.elim (missing_nil inputs added)

theorem evaluate_protection (transformer : Transformer) (initial : State) (scope : Nat) :
    scope ∈ (transformer.evaluate initial).protections ↔
      ((transformer.entry scope).keep = true ∧ scope ∈ initial.protections) ∨
        Missing (transformer.entry scope).missing initial.inputs := by
  simp only [Transformer.evaluate, List.mem_append, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro (⟨present, kept⟩ | ⟨_, added⟩)
    · exact Or.inl ⟨kept, present⟩
    · exact Or.inr added
  · rintro (⟨kept, present⟩ | added)
    · exact Or.inl ⟨present, kept⟩
    · exact Or.inr ⟨missing_has_entry transformer scope initial.inputs added, added⟩

def Equivalent (first second : State) : Prop :=
  (∀ tag, tag ∈ first.inputs ↔ tag ∈ second.inputs) ∧
  (∀ scope, scope ∈ first.protections ↔ scope ∈ second.protections)

theorem Equivalent.refl (state : State) : Equivalent state state := ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem Equivalent.symm {first second : State} (same : Equivalent first second) :
    Equivalent second first := ⟨fun tag => (same.1 tag).symm, fun scope => (same.2 scope).symm⟩

theorem Equivalent.trans {first middle last : State}
    (one : Equivalent first middle) (two : Equivalent middle last) : Equivalent first last :=
  ⟨fun tag => (one.1 tag).trans (two.1 tag), fun scope => (one.2 scope).trans (two.2 scope)⟩

theorem missing_congr (guards : List Nat) {first second : List Nat}
    (same : ∀ tag, tag ∈ first ↔ tag ∈ second) : Missing guards first ↔ Missing guards second := by
  constructor
  · rintro ⟨tag, member, absent⟩
    exact ⟨tag, member, fun found => absent ((same tag).mpr found)⟩
  · rintro ⟨tag, member, absent⟩
    exact ⟨tag, member, fun found => absent ((same tag).mp found)⟩

theorem evaluate_congr (transformer : Transformer) {first second : State}
    (same : Equivalent first second) :
    Equivalent (transformer.evaluate first) (transformer.evaluate second) := by
  constructor
  · intro tag
    simp only [Transformer.evaluate, List.mem_append, same.1 tag]
  · intro scope
    simp only [evaluate_protection, same.2 scope, missing_congr _ same.1]

/-- Universal native normal-form composition law. No composition, safety,
source-typing, or final-model premise is assumed. -/
theorem evaluate_then (first second : Transformer) (initial : State) :
    Equivalent ((first.then second).evaluate initial)
      (second.evaluate (first.evaluate initial)) := by
  constructor
  · intro tag
    simp only [Transformer.evaluate, Transformer.then, List.mem_append, or_assoc]
  · intro scope
    rw [evaluate_protection, then_entry, evaluate_protection, evaluate_protection]
    rw [compose_missing]
    simp only [composeEntry, Bool.and_eq_true, Transformer.evaluate]
    simp only [and_or_left, and_assoc, and_left_comm, or_assoc]

def identity : Transformer := ⟨[], []⟩
def stamp (tag : Nat) : Transformer := ⟨[tag], []⟩
def protect (scope tag : Nat) : Transformer := ⟨[], [(scope, ⟨true, [tag]⟩)]⟩
def release (scope : Nat) : Transformer := ⟨[], [(scope, ⟨false, []⟩)]⟩

theorem evaluate_identity (initial : State) : Equivalent (identity.evaluate initial) initial := by
  constructor
  · intro tag; simp [Transformer.evaluate, identity]
  · intro scope; simp [evaluate_protection, identity, Transformer.entry, entryAt, identityEntry]

theorem evaluate_stamp (tag : Nat) (initial : State) (scope : Nat) :
    scope ∈ ((stamp tag).evaluate initial).protections ↔ scope ∈ initial.protections := by
  simp [evaluate_protection, stamp, Transformer.entry, entryAt, identityEntry]

theorem evaluate_protect (scope tag : Nat) (initial : State) (observed : Nat) :
    observed ∈ ((protect scope tag).evaluate initial).protections ↔
      observed ∈ initial.protections ∨ (observed = scope ∧ tag ∉ initial.inputs) := by
  by_cases same : scope = observed
  · subst observed
    simp [evaluate_protection, protect, Transformer.entry, entryAt, Missing]
  · simp [evaluate_protection, protect, Transformer.entry, entryAt, same,
      Ne.symm same, identityEntry, Missing]

theorem evaluate_release (scope : Nat) (initial : State) (observed : Nat) :
    observed ∈ ((release scope).evaluate initial).protections ↔
      observed ∈ initial.protections ∧ observed ≠ scope := by
  by_cases same : scope = observed
  · subst observed
    simp [evaluate_protection, release, Transformer.entry, entryAt]
  · simp [evaluate_protection, release, Transformer.entry, entryAt, same,
      Ne.symm same, identityEntry]

theorem release_removes (scope : Nat) (initial : State) :
    scope ∉ ((release scope).evaluate initial).protections := by
  simp [evaluate_release]

/-- Release is a tombstone, including for an already inherited protection. -/
theorem protect_then_release (scope tag : Nat) (initial : State) :
    Equivalent (((protect scope tag).then (release scope)).evaluate initial)
      ((release scope).evaluate initial) := by
  apply (evaluate_then _ _ initial).trans
  constructor
  · intro input
    simp [Transformer.evaluate, protect, release]
  · intro observed
    simp only [evaluate_release, evaluate_protect]
    constructor
    · rintro ⟨inherited | ⟨same, _⟩, different⟩
      · exact ⟨inherited, different⟩
      · exact False.elim (different same)
    · rintro ⟨inherited, different⟩
      exact ⟨Or.inl inherited, different⟩

/-- A stamp suppresses only NEW protection; inherited protection remains. -/
theorem stamp_then_protect (scope tag : Nat) (initial : State) (observed : Nat) :
    observed ∈ (((stamp tag).then (protect scope tag)).evaluate initial).protections ↔
      observed ∈ initial.protections := by
  rw [(evaluate_then _ _ initial).2 observed, evaluate_protect, evaluate_stamp]
  simp [Transformer.evaluate, stamp]

theorem protect_then_stamp (scope tag : Nat) (initial : State) (observed : Nat) :
    observed ∈ (((protect scope tag).then (stamp tag)).evaluate initial).protections ↔
      observed ∈ initial.protections ∨ (observed = scope ∧ tag ∉ initial.inputs) := by
  rw [(evaluate_then _ _ initial).2 observed, evaluate_stamp, evaluate_protect]

theorem untouched_scope (transformer : Transformer) (scope : Nat) (initial : State)
    (outside : scope ∉ keys transformer.scopes) :
    scope ∈ (transformer.evaluate initial).protections ↔ scope ∈ initial.protections := by
  rw [evaluate_protection]
  simp [Transformer.entry, entryAt_absent _ _ outside, identityEntry]

/-- A released scope cannot reappear without a later applicable add guard. -/
theorem release_no_revival (transformer : Transformer) (scope : Nat) (initial : State)
    (noAdd : ¬ Missing (transformer.entry scope).missing initial.inputs) :
    scope ∉ (((release scope).then transformer).evaluate initial).protections := by
  rw [(evaluate_then _ _ initial).2 scope, evaluate_protection]
  simp only [release_removes, and_false, false_or]
  simpa [Transformer.evaluate, release] using noAdd

def compile : List Transformer → Transformer
  | [] => identity
  | first :: rest => first.then (compile rest)

def execute : List Transformer → State → State
  | [], initial => initial
  | first :: rest, initial => execute rest (first.evaluate initial)

theorem compiled_execution (steps : List Transformer) (initial : State) :
    Equivalent ((compile steps).evaluate initial) (execute steps initial) := by
  induction steps generalizing initial with
  | nil => exact evaluate_identity initial
  | cons first rest ih =>
      exact (evaluate_then first (compile rest) initial).trans (ih (first.evaluate initial))

theorem ordered_associativity (first second third : Transformer) (initial : State) :
    Equivalent (((first.then second).then third).evaluate initial)
      ((first.then (second.then third)).evaluate initial) := by
  have left := (evaluate_then (first.then second) third initial).trans
    (evaluate_congr third (evaluate_then first second initial))
  have right := (evaluate_then first (second.then third) initial).trans
    (evaluate_then second third (first.evaluate initial))
  exact left.trans right.symm

/-- Every newly present protection has an actual applicable guard at some
step. This is not an attribution theorem for original source witnesses. -/
theorem new_protection_has_origin (steps : List Transformer) (initial : State) (scope : Nat)
    (present : scope ∈ (execute steps initial).protections)
    (absent : scope ∉ initial.protections) :
    ∃ before transformer after,
      steps = before ++ transformer :: after ∧
      Missing (transformer.entry scope).missing (execute before initial).inputs := by
  induction steps generalizing initial with
  | nil => exact False.elim (absent present)
  | cons first rest ih =>
      by_cases intermediate : scope ∈ (first.evaluate initial).protections
      · have introduced := (evaluate_protection first initial scope).mp intermediate
        rcases introduced with inherited | added
        · exact False.elim (absent inherited.2)
        · exact ⟨[], first, rest, rfl, added⟩
      · obtain ⟨before, transformer, after, route, added⟩ :=
          ih (first.evaluate initial) present intermediate
        refine ⟨first :: before, transformer, after, ?_, added⟩
        simp only [List.cons_append, route]

structure Fact (Witness : Type) where
  witness : Witness
  state : State

def Transformer.applyFact (transformer : Transformer) (fact : Fact Witness) : Fact Witness :=
  ⟨fact.witness, transformer.evaluate fact.state⟩

/-- Every observer of the COMPLETE carried witness is unchanged. Receipts,
provider/instance identity, and grants must be components of that same witness
at the source/native owner; this algebra does not invent those components. -/
theorem witness_observer_preserved (transformer : Transformer) (fact : Fact Witness)
    (observe : Witness → Result) :
    observe (transformer.applyFact fact).witness = observe fact.witness := rfl

def Entry.rename (entry : Entry) (tags : Nat → Nat) : Entry :=
  ⟨entry.keep, entry.missing.map tags⟩

def Transformer.rename (transformer : Transformer) (scopes tags : Nat → Nat) : Transformer :=
  ⟨transformer.stamped.map tags,
    transformer.scopes.map (fun entry => (scopes entry.1, entry.2.rename tags))⟩

def State.rename (state : State) (scopes tags : Nat → Nat) : State :=
  ⟨state.inputs.map tags, state.protections.map scopes⟩

theorem mem_injective_map (map : Nat → Nat) (injective : Function.Injective map)
    (items : List Nat) (item : Nat) : map item ∈ items.map map ↔ item ∈ items := by
  constructor
  · intro found
    obtain ⟨old, present, same⟩ := List.mem_map.mp found
    exact (injective same) ▸ present
  · exact fun present => List.mem_map.mpr ⟨item, present, rfl⟩

theorem renamed_entry (entries : List (Nat × Entry)) (scopes tags : Nat → Nat)
    (injective : Function.Injective scopes) (scope : Nat) :
    entryAt (entries.map (fun entry => (scopes entry.1, entry.2.rename tags))) (scopes scope) =
      (entryAt entries scope).rename tags := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
      rcases head with ⟨key, entry⟩
      by_cases same : key = scope
      · subst key
        simp [entryAt]
      · have different : scopes key ≠ scopes scope := fun equal => same (injective equal)
        simp [entryAt, same, different, ih]

theorem missing_rename (guards inputs : List Nat) (tags : Nat → Nat)
    (injective : Function.Injective tags) :
    Missing (guards.map tags) (inputs.map tags) ↔ Missing guards inputs := by
  constructor
  · rintro ⟨image, member, absent⟩
    obtain ⟨tag, present, rfl⟩ := List.mem_map.mp member
    exact ⟨tag, present, fun found => absent (List.mem_map.mpr ⟨tag, found, rfl⟩)⟩
  · rintro ⟨tag, member, absent⟩
    exact ⟨tags tag, List.mem_map.mpr ⟨tag, member, rfl⟩,
      fun found => absent ((mem_injective_map tags injective inputs tag).mp found)⟩

/-- The same injective maps must cover both the transformer and the incoming
state. Native `remap`'s private-support collision check alone is insufficient. -/
theorem renamed_protection (transformer : Transformer) (initial : State)
    (scopes tags : Nat → Nat) (scopeInjection : Function.Injective scopes)
    (tagInjection : Function.Injective tags) (scope : Nat) :
    scopes scope ∈ ((transformer.rename scopes tags).evaluate
      (initial.rename scopes tags)).protections ↔
        scope ∈ (transformer.evaluate initial).protections := by
  simp only [evaluate_protection, Transformer.entry, Transformer.rename]
  rw [renamed_entry _ _ _ scopeInjection]
  simp only [Entry.rename, State.rename, mem_injective_map _ scopeInjection,
    missing_rename _ _ _ tagInjection]

theorem renamed_output_has_origin (transformer : Transformer) (initial : State)
    (scopes tags : Nat → Nat) (observed : Nat)
    (present : observed ∈ ((transformer.rename scopes tags).evaluate
      (initial.rename scopes tags)).protections) :
    ∃ scope, scopes scope = observed := by
  rcases (evaluate_protection _ _ _).mp present with inherited | added
  · obtain ⟨scope, _, same⟩ := List.mem_map.mp inherited.2
    exact ⟨scope, same⟩
  · have origin := missing_has_entry (transformer.rename scopes tags) observed
      (initial.rename scopes tags).inputs added
    simp only [keys, Transformer.rename, List.map_map, Function.comp_def] at origin
    obtain ⟨entry, _, same⟩ := List.mem_map.mp origin
    exact ⟨entry.1, same⟩

theorem evaluate_rename (transformer : Transformer) (initial : State)
    (scopes tags : Nat → Nat) (scopeInjection : Function.Injective scopes)
    (tagInjection : Function.Injective tags) :
    Equivalent ((transformer.rename scopes tags).evaluate (initial.rename scopes tags))
      ((transformer.evaluate initial).rename scopes tags) := by
  constructor
  · intro tag
    simp only [Transformer.evaluate, Transformer.rename, State.rename, List.map_append]
  · intro observed
    constructor
    · intro present
      obtain ⟨scope, same⟩ := renamed_output_has_origin transformer initial scopes tags observed present
      subst observed
      exact List.mem_map.mpr ⟨scope,
        (renamed_protection transformer initial scopes tags scopeInjection tagInjection scope).mp present, rfl⟩
    · intro present
      obtain ⟨scope, member, same⟩ := List.mem_map.mp present
      subst observed
      exact (renamed_protection transformer initial scopes tags scopeInjection tagInjection scope).mpr member

/-- A transformer-support-injective rename may collide with a distinct
external incoming scope. A concrete release then removes too much. This
refutes that insufficient bridge, not the original Yulang inference theorem. -/
theorem local_support_injection_is_insufficient :
    let transformer := release 0
    let initial : State := ⟨[], [1]⟩
    let scopes : Nat → Nat := fun _ => 0
    (∀ a ∈ keys transformer.scopes, ∀ b ∈ keys transformer.scopes,
      scopes a = scopes b → a = b) ∧
    ¬ Equivalent ((transformer.rename scopes id).evaluate (initial.rename scopes id))
      ((transformer.evaluate initial).rename scopes id) := by
  constructor
  · simp [release, keys]
  · intro same
    have failed := same.2 0
    simp [Transformer.rename, Transformer.evaluate, Transformer.entry,
      Entry.rename, State.rename, release, entryAt, identityEntry, keys, Missing] at failed

end YulangClosure.NativeScopeTransformer
