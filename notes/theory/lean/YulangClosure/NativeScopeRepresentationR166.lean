import YulangClosure.NativeScopeEvaluateRefinementR165

/-!
R166: ordered representation facts for a Lean model of the private native
scope API. `encodeId` is the unsigned `u32` interpretation. Allocation errors
are omitted from this successful-value model. `thenModel` merges ordered scope
support and computes the Rust per-scope formula; it is not a proof of the Rust
cursor loop. `remapModel` uses pure, already sampled maps: it does not execute
Rust `FnMut`, and its checks cover only the transformer's finite support.

`orderedSearch` is a sorted-list search model, not `std::slice::binary_search`.
Its contract is the membership contract needed by Missing. Rust execution,
standard-library implementation and authentication of route/scope identities
remain source correspondence obligations. No initial-state restriction is
introduced in the application to R165.
-/
namespace YulangClosure.NativeScopeRepresentationR166

open NativeScopeTransformer
open NativeScopeEvaluateRefinementR165

def encodeId (id : UInt32) : Nat := id.toNat

theorem encodeId_injective : Function.Injective encodeId := by
  intro a b h
  exact UInt32.toNat.inj h

theorem encodeId_lt (a b : UInt32) : encodeId a < encodeId b ↔ a < b :=
  UInt32.lt_iff_toNat_lt.symm

theorem encodeId_bound (a : UInt32) : encodeId a < 2 ^ 32 := UInt32.toNat_lt a

structure NativeEntry where
  scope : UInt32
  keep : Bool
  missing : List UInt32

structure NativeFields where
  stamped : List UInt32
  scopes : List NativeEntry

def encodeFields (native : NativeFields) : Transformer :=
  ⟨native.stamped.map encodeId,
    native.scopes.map (fun entry =>
      (encodeId entry.scope, ⟨entry.keep, entry.missing.map encodeId⟩))⟩

theorem encodeId_mem (ids : List UInt32) (id : UInt32) :
    encodeId id ∈ ids.map encodeId ↔ id ∈ ids := by
  constructor
  · intro h
    obtain ⟨old, hold, heq⟩ := List.mem_map.mp h
    exact encodeId_injective heq ▸ hold
  · intro h
    exact List.mem_map.mpr ⟨id, h, rfl⟩

theorem encodeId_sorted (ids : List UInt32) :
    (ids.map encodeId).Pairwise (· < ·) ↔ ids.Pairwise (· < ·) := by
  simp only [List.pairwise_map, encodeId_lt]

/-- The stronger native invariant also orders each Missing guard vector. -/
def Representation (transformer : Transformer) : Prop :=
  Canonical transformer ∧
    ∀ entry ∈ transformer.scopes, entry.2.missing.Pairwise (· < ·)

def NativeOrdered (native : NativeFields) : Prop :=
  native.stamped.Pairwise (· < ·) ∧
    (native.scopes.map (·.scope)).Pairwise (· < ·) ∧
    ∀ entry ∈ native.scopes, entry.missing.Pairwise (· < ·)

theorem encodeFields_representation (native : NativeFields) (h : NativeOrdered native) :
    Representation (encodeFields native) := by
  refine ⟨⟨(encodeId_sorted _).mpr h.1, ?_⟩, ?_⟩
  · simpa only [encodeFields, keys, List.map_map, Function.comp_def] using
      (encodeId_sorted _).mpr h.2.1
  · intro entry he
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp he
    exact (encodeId_sorted _).mpr (h.2.2 old hold)

def identityModel : Transformer := identity
def stampModel (tag : UInt32) : Transformer := stamp (encodeId tag)
def protectModel (scope tag : UInt32) : Transformer := protect (encodeId scope) (encodeId tag)
def releaseModel (scope : UInt32) : Transformer := release (encodeId scope)

theorem identity_representation : Representation identityModel := by
  simp [Representation, Canonical, identityModel, identity, keys]

theorem stamp_representation (tag : UInt32) : Representation (stampModel tag) := by
  simp [Representation, Canonical, stampModel, stamp, keys]

theorem protect_representation (scope tag : UInt32) :
    Representation (protectModel scope tag) := by
  simp [Representation, Canonical, protectModel, protect, keys]

theorem release_representation (scope : UInt32) : Representation (releaseModel scope) := by
  simp [Representation, Canonical, releaseModel, release, keys]

private theorem entry_sorted (entries : List (Nat × Entry))
    (h : ∀ entry ∈ entries, entry.2.missing.Pairwise (· < ·)) (scope : Nat) :
    (entryAt entries scope).missing.Pairwise (· < ·) := by
  induction entries with
  | nil => simp [entryAt, identityEntry]
  | cons head rest ih =>
    simp only [entryAt]
    split
    · exact h head (by simp)
    · exact ih (fun e he => h e (by simp [he]))

def composeEntryModel (first second : Entry) (firstStamps : List Nat) : Entry :=
  ⟨first.keep && second.keep,
    unionCursor (if second.keep then first.missing else [])
      (second.missing.filter (fun tag => decide (tag ∉ firstStamps)))⟩

def thenModel (first second : Transformer) : Transformer :=
  ⟨unionCursor first.stamped second.stamped,
    encode (unionCursor (keys first.scopes) (keys second.scopes))
      (fun scope => composeEntryModel (first.entry scope) (second.entry scope) first.stamped)⟩

private theorem encode_keys_sorted (support : List Nat) (value : Nat → Entry)
    (h : support.Pairwise (· < ·)) : (keys (encode support value)).Pairwise (· < ·) := by
  induction support with
  | nil => simp [encode, keys]
  | cons scope rest ih =>
    have hr := (List.pairwise_cons.mp h).2
    by_cases neutral : value scope = identityEntry
    · simpa [encode, neutral] using ih hr
    · simp only [encode, neutral, ↓reduceIte, List.filterMap_cons, keys, List.map_cons,
        List.pairwise_cons]
      refine ⟨?_, ih hr⟩
      intro other present
      have inRest : other ∈ rest := by
        obtain ⟨pair, hpair, heq⟩ := List.mem_map.mp present
        obtain ⟨key, hk, hsome⟩ := List.mem_filterMap.mp hpair
        split at hsome
        · contradiction
        · simp only [Option.some.injEq] at hsome
          subst pair
          simpa using heq ▸ hk
      exact (List.pairwise_cons.mp h).1 other inRest

theorem then_representation (first second : Transformer)
    (hf : Representation first) (hs : Representation second) :
    Representation (thenModel first second) := by
  refine ⟨⟨unionCursor_sorted _ _ hf.1.1 hs.1.1,
    encode_keys_sorted _ _ (unionCursor_sorted _ _ hf.1.2 hs.1.2)⟩, ?_⟩
  intro pair present
  obtain ⟨scope, _, hsome⟩ := List.mem_filterMap.mp present
  split at hsome
  · contradiction
  · simp only [Option.some.injEq] at hsome
    subst pair
    apply unionCursor_sorted
    · cases hkeep : (second.entry scope).keep
      · simp
      · exact entry_sorted first.scopes hf.2 scope
    · exact (entry_sorted second.scopes hs.2 scope).filter _

theorem composeEntryModel_missing (first second : Entry) (stamps inputs : List Nat) :
    Missing (composeEntryModel first second stamps).missing inputs ↔
      Missing (composeEntry first second stamps).missing inputs := by
  simp only [composeEntryModel, composeEntry, Missing, unionCursor_mem, List.mem_append]

theorem thenModel_entry (first second : Transformer) (scope : Nat) :
    (thenModel first second).entry scope =
      composeEntryModel (first.entry scope) (second.entry scope) first.stamped := by
  simp only [thenModel, Transformer.entry, entryAt_encode]
  split
  · rfl
  · rename_i absent
    have ha : scope ∉ keys first.scopes ∧ scope ∉ keys second.scopes := by
      simpa only [unionCursor_mem, not_or] using absent
    rw [entryAt_absent _ _ ha.1, entryAt_absent _ _ ha.2]
    simp [composeEntryModel, identityEntry, unionCursor]

theorem thenModel_denotation (first second : Transformer) (initial : State) :
    Equivalent ((thenModel first second).evaluate initial)
      (second.evaluate (first.evaluate initial)) := by
  apply Equivalent.trans (middle := (first.then second).evaluate initial)
  · constructor
    · intro tag
      simp only [Transformer.evaluate, thenModel, Transformer.then, List.mem_append,
        unionCursor_mem]
    · intro scope
      simp only [evaluate_protection, thenModel_entry, then_entry]
      rw [composeEntryModel_missing]
      rfl
  · exact evaluate_then first second initial

def sortIds (ids : List Nat) : List Nat := ids.mergeSort (fun a b => decide (a ≤ b))

private theorem sortIds_le (ids : List Nat) : (sortIds ids).Pairwise (· ≤ ·) := by
  have h := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp; omega) ids
  exact h.imp (fun hab => of_decide_eq_true hab)

private theorem sorted_of_le_nodup (ids : List Nat) (hle : ids.Pairwise (· ≤ ·))
    (hn : ids.Nodup) : ids.Pairwise (· < ·) :=
  List.Pairwise.imp₂ (fun _ _ hab hne => Nat.lt_of_le_of_ne hab hne)
    hle (List.nodup_iff_pairwise_ne.mp hn)

private theorem sortIds_sorted (ids : List Nat) (hn : ids.Nodup) :
    (sortIds ids).Pairwise (· < ·) :=
  sorted_of_le_nodup _ (sortIds_le ids)
    ((List.mergeSort_perm ids _).symm.nodup hn)

def adjacentDistinct : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (a != b) && adjacentDistinct (b :: rest)

private theorem adjacentDistinct_iff_strict (ids : List Nat) (hle : ids.Pairwise (· ≤ ·)) :
    adjacentDistinct ids = true ↔ ids.Pairwise (· < ·) := by
  induction ids with
  | nil => simp [adjacentDistinct]
  | cons a tail ih =>
    cases tail with
    | nil => simp [adjacentDistinct]
    | cons b rest =>
      have ht := (List.pairwise_cons.mp hle).2
      have hi := ih ht
      simp only [adjacentDistinct, Bool.and_eq_true, bne_iff_ne] at hi ⊢
      constructor
      · rintro ⟨hne, htail⟩
        have hs := hi.mp htail
        have hab : a < b := Nat.lt_of_le_of_ne ((List.pairwise_cons.mp hle).1 b (by simp)) hne
        refine List.pairwise_cons.mpr ⟨?_, hs⟩
        intro c hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact hab
        · exact Nat.lt_trans hab ((List.pairwise_cons.mp hs).1 c hc)
      · intro hs
        refine ⟨Nat.ne_of_lt ((List.pairwise_cons.mp hs).1 b (by simp)),
          hi.mpr (List.pairwise_cons.mp hs).2⟩

/-- Native sorted-scope `windows(2)` collision rejection has this exact
finite-set specification. Sorting does not remove any duplicate. -/
theorem adjacent_sort_iff_nodup (ids : List Nat) :
    adjacentDistinct (sortIds ids) = true ↔ ids.Nodup := by
  rw [adjacentDistinct_iff_strict _ (sortIds_le ids)]
  constructor
  · intro hs
    exact (List.mergeSort_perm ids _).nodup
      (List.nodup_iff_pairwise_ne.mpr (hs.imp (by omega)))
  · exact sortIds_sorted ids

private theorem eraseDups_sublist (ids : List Nat) : List.Sublist ids.eraseDups ids := by
  have aux : ∀ n (xs : List Nat), xs.length = n → List.Sublist xs.eraseDups xs := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro xs hlen
      cases xs with
      | nil => simp
      | cons a rest =>
        rw [List.eraseDups_cons]
        apply List.Sublist.cons_cons
        exact (ih _ (by have := List.length_filter_le (fun b => !b == a) rest; simp at hlen; omega)
          _ rfl).trans List.filter_sublist
  exact aux ids.length ids rfl

/-- Exact collision test used for the sampled input images in native remap. -/
theorem normalize_length_eq_iff (ids : List Nat) :
    (normalize ids).length = ids.length ↔ ids.Nodup := by
  constructor
  · intro heq
    have hlen : ids.eraseDups.length = ids.length := by simpa [normalize] using heq
    have same := (eraseDups_sublist ids).eq_of_length hlen
    rw [← same]
    exact nodup_eraseDups_nat ids
  · intro hn
    have perm : List.Perm (normalize ids) ids := List.perm_ext_iff_of_nodup
      (List.nodup_iff_pairwise_ne.mpr ((sorted_normalize ids).imp (by omega))) hn |>.mpr
        (fun tag => mem_normalize ids tag)
    exact perm.length_eq

private theorem nodup_map_injective_on (support : List Nat) (f : Nat → Nat)
    (hn : (support.map f).Nodup) :
    ∀ a ∈ support, ∀ b ∈ support, f a = f b → a = b := by
  induction support with
  | nil => simp
  | cons head rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hn
    intro a ha b hb heq
    rcases List.mem_cons.mp ha with rfl | atail
    · rcases List.mem_cons.mp hb with rfl | btail
      · rfl
      · exact False.elim (hn.1 (List.mem_map.mpr ⟨b, btail, heq.symm⟩))
    · rcases List.mem_cons.mp hb with rfl | btail
      · exact False.elim (hn.1 (List.mem_map.mpr ⟨a, atail, heq⟩))
      · exact ih hn.2 a atail b btail heq

private theorem nodup_map_subset (support xs : List Nat) (f : Nat → Nat)
    (hs : (support.map f).Nodup) (hx : xs.Nodup) (sub : xs ⊆ support) :
    (xs.map f).Nodup := by
  apply List.nodup_iff_pairwise_ne.mpr
  rw [List.pairwise_map]
  apply (List.nodup_iff_pairwise_ne.mp hx).imp_of_mem
  intro a b ha hb hne heq
  exact hne (nodup_map_injective_on support f hs a (sub ha) b (sub hb) heq)

def inputSupport (transformer : Transformer) : List Nat :=
  normalize (transformer.stamped ++ transformer.scopes.flatMap (fun entry => entry.2.missing))

theorem inputSupport_stamp (transformer : Transformer) : transformer.stamped ⊆ inputSupport transformer := by
  intro tag htag
  rw [inputSupport, mem_normalize]
  exact List.mem_append_left _ htag

theorem inputSupport_guard (transformer : Transformer) (entry : Nat × Entry)
    (hentry : entry ∈ transformer.scopes) : entry.2.missing ⊆ inputSupport transformer := by
  intro tag htag
  rw [inputSupport, mem_normalize]
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨entry, hentry, htag⟩)

def renameEntryModel (entry : Nat × Entry) (scopes tags : Nat → Nat) : Nat × Entry :=
  (scopes entry.1, ⟨entry.2.keep, sortIds (entry.2.missing.map tags)⟩)

def sortEntries (entries : List (Nat × Entry)) : List (Nat × Entry) :=
  entries.mergeSort (fun a b => decide (a.1 ≤ b.1))

private theorem sortEntries_keys (entries : List (Nat × Entry)) :
    keys (sortEntries entries) = sortIds (keys entries) := by
  exact List.map_mergeSort (fun _ _ _ _ => rfl)

theorem scope_collision_check (transformer : Transformer) (scopes tags : Nat → Nat) :
    adjacentDistinct (keys (sortEntries (transformer.scopes.map
      (fun entry => renameEntryModel entry scopes tags)))) = true ↔
      ((keys transformer.scopes).map scopes).Nodup := by
  rw [sortEntries_keys, adjacent_sort_iff_nodup]
  simp only [keys, List.map_map, Function.comp_def, renameEntryModel]

/-- Both checks concern only private finite support, as in the native API.
The scope Nodup check is the order-independent specification of the native
sort followed by adjacent-equality rejection; no external-state injection is
assumed or concluded. Input images are already sampled consistently once. -/
def remapModel (transformer : Transformer) (scopes tags : Nat → Nat) : Option Transformer :=
  if (normalize ((inputSupport transformer).map tags)).length = (inputSupport transformer).length ∧
      ((keys transformer.scopes).map scopes).Nodup then
    some ⟨sortIds (transformer.stamped.map tags),
      sortEntries (transformer.scopes.map (fun entry => renameEntryModel entry scopes tags))⟩
  else none

theorem remap_success_injective (transformer result : Transformer) (scopes tags : Nat → Nat)
    (success : remapModel transformer scopes tags = some result) :
    (∀ a ∈ inputSupport transformer, ∀ b ∈ inputSupport transformer, tags a = tags b → a = b) ∧
    (∀ a ∈ keys transformer.scopes, ∀ b ∈ keys transformer.scopes, scopes a = scopes b → a = b) := by
  unfold remapModel at success
  split at success
  · rename_i hcheck
    have ht : ((inputSupport transformer).map tags).Nodup :=
      (normalize_length_eq_iff _).mp (by simpa using hcheck.1)
    exact ⟨nodup_map_injective_on _ _ ht, nodup_map_injective_on _ _ hcheck.2⟩
  · contradiction

theorem remap_representation (transformer result : Transformer) (scopes tags : Nat → Nat)
    (hrep : Representation transformer) (success : remapModel transformer scopes tags = some result) :
    Representation result := by
  unfold remapModel at success
  split at success
  · rename_i hcheck
    simp only [Option.some.injEq] at success
    subst result
    have ht : ((inputSupport transformer).map tags).Nodup :=
      (normalize_length_eq_iff _).mp (by simpa using hcheck.1)
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact sortIds_sorted _ (nodup_map_subset _ _ _ ht
        (List.nodup_iff_pairwise_ne.mpr (hrep.1.1.imp (by omega))) (inputSupport_stamp transformer))
    · rw [sortEntries_keys]
      have heq : keys (transformer.scopes.map (fun entry => renameEntryModel entry scopes tags)) =
          (keys transformer.scopes).map scopes := by simp [keys, renameEntryModel]
      rw [heq]
      exact sortIds_sorted _ hcheck.2
    · intro entry hentry
      have hin := (List.mergeSort_perm _ _).mem_iff.mp hentry
      obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hin
      exact sortIds_sorted _ (nodup_map_subset _ _ _ ht
        (List.nodup_iff_pairwise_ne.mpr ((hrep.2 old hold).imp (by omega)))
        (inputSupport_guard transformer old hold))
  · contradiction

/-- A concrete early-stop search of an ordered slice. The Rust binary-search
implementation is outside this model; the proved result is its required
membership contract, including the absent/empty cases. -/
def orderedSearch (tag : Nat) : List Nat → Bool
  | [] => false
  | head :: tail => if tag < head then false else if tag = head then true else orderedSearch tag tail

theorem orderedSearch_iff (tag : Nat) (ids : List Nat) (sorted : ids.Pairwise (· < ·)) :
    orderedSearch tag ids = true ↔ tag ∈ ids := by
  induction ids with
  | nil => simp [orderedSearch]
  | cons head tail ih =>
    have ht := (List.pairwise_cons.mp sorted).2
    by_cases hlt : tag < head
    · have absent : tag ∉ tail := by
        intro htag
        have := (List.pairwise_cons.mp sorted).1 tag htag
        omega
      simp [orderedSearch, hlt, absent, Nat.ne_of_lt hlt]
    · by_cases heq : tag = head
      · simp [orderedSearch, heq]
      · simp [orderedSearch, hlt, heq, ih ht]

def missingSearch (guards inputs : List Nat) : Bool :=
  guards.any (fun tag => !(orderedSearch tag inputs))

theorem missingSearch_iff (guards inputs : List Nat) (sorted : inputs.Pairwise (· < ·)) :
    missingSearch guards inputs = true ↔ Missing guards inputs := by
  simp only [missingSearch, List.any_eq_true, Missing]
  constructor
  · rintro ⟨tag, htag, hfalse⟩
    exact ⟨tag, htag, fun hin => by
      have ht := (orderedSearch_iff tag inputs sorted).mpr hin
      simp [ht] at hfalse⟩
  · rintro ⟨tag, htag, absent⟩
    refine ⟨tag, htag, ?_⟩
    cases hs : orderedSearch tag inputs
    · rfl
    · exact False.elim (absent ((orderedSearch_iff tag inputs sorted).mp hs))

/-- The sorted unsigned slice and its Nat encoding agree on every missing
guard, including guards outside the initial slice. -/
theorem missingSearch_encoded (guards inputs : List UInt32)
    (sorted : inputs.Pairwise (· < ·)) :
    missingSearch (guards.map encodeId) (inputs.map encodeId) = true ↔
      ∃ tag ∈ guards, tag ∉ inputs := by
  rw [missingSearch_iff _ _ ((encodeId_sorted inputs).mpr sorted)]
  constructor
  · rintro ⟨image, hguard, absent⟩
    obtain ⟨tag, htag, rfl⟩ := List.mem_map.mp hguard
    exact ⟨tag, htag, fun hin => absent ((encodeId_mem inputs tag).mpr hin)⟩
  · rintro ⟨tag, htag, absent⟩
    exact ⟨encodeId tag, List.mem_map.mpr ⟨tag, htag, rfl⟩,
      fun hin => absent ((encodeId_mem inputs tag).mp hin)⟩

inductive Generated : Transformer → Prop where
  | identity : Generated identityModel
  | stamp (tag : UInt32) : Generated (stampModel tag)
  | protect (scope tag : UInt32) : Generated (protectModel scope tag)
  | release (scope : UInt32) : Generated (releaseModel scope)
  | then {first second : Transformer} : Generated first → Generated second → Generated (thenModel first second)
  | remap {transformer result : Transformer} (scopes tags : Nat → Nat) : Generated transformer →
      remapModel transformer scopes tags = some result → Generated result

theorem generated_representation (transformer : Transformer) (generated : Generated transformer) :
    Representation transformer := by
  induction generated with
  | identity => exact identity_representation
  | stamp tag => exact stamp_representation tag
  | protect scope tag => exact protect_representation scope tag
  | release scope => exact release_representation scope
  | «then» _ _ hf hs => exact then_representation _ _ hf hs
  | remap scopes tags _ success ih => exact remap_representation _ _ scopes tags ih success

/-- R165 applied to every generated model value and every initial state,
including duplicate/unsorted initial lists. This is a Lean model theorem. -/
theorem generated_evaluate_equivalent (transformer : Transformer) (initial : State)
    (generated : Generated transformer) :
    Equivalent (evaluateCursor transformer initial) (transformer.evaluate initial) :=
  evaluateCursor_equivalent transformer initial (generated_representation transformer generated).1

/-- Explicit successful-native/encoded-model premise stays visible. Neither
Rust execution nor authenticity of native IDs is inferred from Generated. -/
theorem encoded_native_evaluate_equivalent (native : NativeFields) (transformer : Transformer)
    (initial : State) (encoding : encodeFields native = transformer) (generated : Generated transformer) :
    Equivalent (evaluateCursor (encodeFields native) initial) ((encodeFields native).evaluate initial) := by
  rw [encoding]
  exact generated_evaluate_equivalent transformer initial generated

end YulangClosure.NativeScopeRepresentationR166
