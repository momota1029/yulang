import Yulang.Variants
import Yulang.StructuralBase

/-!
# Tag-unique variants

Decision 2026-11-05, spec/04-types.md §4.5: one alternative per tag,
with the whole merged payload selected or removed at once.

`merge` is explicit. Normalization uses the reverse order of the last occurrences
of tags and right-associates payloads in source order. No result requires
associativity, commutativity, or idempotence: permuting or duplicating the input
is not claimed to preserve payload equality. A union interpretation may supply
these laws up to its own semantic equivalence.
-/

namespace Yulang.Variants.Merged

/-- A finite row with exactly one entry per present tag. -/
structure Row (Tag Payload : Type) where
  entries : Variants.Row Tag Payload
  unique : (entries.map Prod.fst).Nodup

namespace Raw

variable [DecidableEq Tag]

def insert (merge : Payload → Payload → Payload) (tag : Tag) (payload : Payload) :
    Variants.Row Tag Payload → Variants.Row Tag Payload
  | [] => [(tag, payload)]
  | (key, value) :: rest =>
    if tag = key then (key, merge payload value) :: rest
    else (key, value) :: insert merge tag payload rest

/-- Lookup observes the first entry on raw rows; clients use unique rows. -/
def lookup (tag : Tag) : Variants.Row Tag Payload → Option Payload
  | [] => none
  | (key, value) :: rest => if tag = key then some value else lookup tag rest

@[simp] theorem tags_insert (merge : Payload → Payload → Payload) (tag key : Tag)
    (payload : Payload) (row : Variants.Row Tag Payload) :
    key ∈ (insert merge tag payload row).map Prod.fst ↔
      key = tag ∨ key ∈ row.map Prod.fst := by
  induction row with
  | nil => simp [insert]
  | cons entry rest ih =>
    rcases entry with ⟨head, value⟩
    by_cases h : tag = head
    · subst head; simp [insert]
    · simp [insert, h, ih, or_left_comm]

theorem insert_unique (merge : Payload → Payload → Payload) (tag : Tag)
    (payload : Payload) (row : Variants.Row Tag Payload)
    (unique : (row.map Prod.fst).Nodup) :
    ((insert merge tag payload row).map Prod.fst).Nodup := by
  induction row with
  | nil => simp [insert]
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    simp only [List.map_cons, List.nodup_cons] at unique
    by_cases h : tag = key
    · simpa [insert, h] using unique
    · simp [insert, h, List.nodup_cons, tags_insert, Ne.symm h, unique.1, ih unique.2]

@[simp] theorem lookup_insert (merge : Payload → Payload → Payload)
    (tag key : Tag) (payload : Payload) (row : Variants.Row Tag Payload) :
    lookup key (insert merge tag payload row) =
      if key = tag then some (match lookup tag row with
        | none => payload
        | some old => merge payload old)
      else lookup key row := by
  induction row with
  | nil => simp [insert, lookup]
  | cons entry rest ih =>
    rcases entry with ⟨head, value⟩
    by_cases ht : tag = head
    · subst head
      by_cases hk : key = tag <;> simp [insert, lookup, hk]
    · by_cases hk : key = head
      · subst head; simp [insert, lookup, ht, Ne.symm ht]
      · simp [insert, lookup, ht, hk, ih]

/-- A tag-only filter cannot leave part of an inserted payload behind. -/
theorem filter_insert (merge : Payload → Payload → Payload) (keep : Tag → Bool)
    (tag : Tag) (payload : Payload) (row : Variants.Row Tag Payload) :
    (insert merge tag payload row).filter (fun entry => keep entry.1) =
      if keep tag then insert merge tag payload (row.filter (fun entry => keep entry.1))
      else row.filter (fun entry => keep entry.1) := by
  induction row with
  | nil => cases h : keep tag <;> simp [insert, h]
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    by_cases heq : tag = key
    · subst key
      cases h : keep tag <;> simp [insert, h]
    · cases ht : keep tag <;> cases hk : keep key <;>
        simp [insert, heq, ht, hk, ih]

theorem lookup_filter (keep : Tag → Bool) (tag : Tag)
    (row : Variants.Row Tag Payload) :
    lookup tag (row.filter (fun entry => keep entry.1)) =
      if keep tag then lookup tag row else none := by
  induction row with
  | nil => simp [lookup]
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    by_cases heq : tag = key
    · subst key; cases h : keep tag <;> simp [lookup, h, ih]
    · cases ht : keep tag <;> cases hk : keep key <;> simp [lookup, heq, ht, hk, ih]

theorem lookup_eq_some_iff (tag : Tag) (payload : Payload)
    (row : Variants.Row Tag Payload) (unique : (row.map Prod.fst).Nodup) :
    lookup tag row = some payload ↔ (tag, payload) ∈ row := by
  induction row with
  | nil => simp [lookup]
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    simp only [List.map_cons, List.nodup_cons] at unique
    by_cases heq : tag = key
    · subst key
      have absent : (tag, payload) ∉ rest := by
        intro h
        exact unique.1 (List.mem_map.mpr ⟨(tag, payload), h, rfl⟩)
      simp [lookup, absent, eq_comm]
    · simp [lookup, heq, ih unique.2]

theorem lookup_eq_none_iff (tag : Tag) (row : Variants.Row Tag Payload) :
    lookup tag row = none ↔ tag ∉ row.map Prod.fst := by
  induction row with
  | nil => simp [lookup]
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    by_cases h : tag = key <;> simp [lookup, h, ih]

theorem map_insert (merge : Payload → Payload → Payload)
    (merge' : Payload' → Payload' → Payload') (f : Payload → Payload')
    (hom : ∀ a b, f (merge a b) = merge' (f a) (f b))
    (tag : Tag) (payload : Payload) (row : Variants.Row Tag Payload) :
    (insert merge tag payload row).map (fun entry => (entry.1, f entry.2)) =
      insert merge' tag (f payload) (row.map (fun entry => (entry.1, f entry.2))) := by
  induction row with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    by_cases h : tag = key <;> simp [insert, h, hom, ih]

end Raw

variable [DecidableEq Tag]

/-- `none` means absence, not a distinguished bottom payload. For the matching
subsequence `[a,b,c]` this returns `some (merge a (merge b c))`; no identity is
required. A singleton matching subsequence returns its payload unchanged. -/
def mergeAll (merge : Payload → Payload → Payload) (tag : Tag) :
    Variants.Row Tag Payload → Option Payload
  | [] => none
  | (key, value) :: rest =>
    if tag = key then some (match mergeAll merge tag rest with
      | none => value
      | some old => merge value old)
    else mergeAll merge tag rest

/-- Merge equal tags into a row with kernel-checked tag uniqueness. -/
def normalize (merge : Payload → Payload → Payload) :
    Variants.Row Tag Payload → Row Tag Payload
  | [] => ⟨[], by simp⟩
  | (tag, payload) :: rest =>
    let tail := normalize merge rest
    ⟨Raw.insert merge tag payload tail.entries,
      Raw.insert_unique merge tag payload tail.entries tail.unique⟩

def lookup (tag : Tag) (row : Row Tag Payload) : Option Payload :=
  Raw.lookup tag row.entries

/-- Pairwise distinct tags are an invariant of the representation. -/
theorem normalize_unique (merge : Payload → Payload → Payload)
    (row : Variants.Row Tag Payload) :
    ((normalize merge row).entries.map Prod.fst).Nodup :=
  (normalize merge row).unique

omit [DecidableEq Tag] in
@[ext] theorem Row.ext {left right : Row Tag Payload}
    (h : left.entries = right.entries) : left = right := by
  cases left; cases right; cases h; rfl

/-- Retain whole entries, preserving uniqueness of tags. -/
def filter (keep : Tag → Bool) (row : Row Tag Payload) : Row Tag Payload :=
  ⟨row.entries.filter (fun entry => keep entry.1), by
    exact (List.filter_sublist.map Prod.fst).nodup row.unique⟩

def residual (handled : Tag → Bool) (row : Row Tag Payload) : Row Tag Payload :=
  filter (fun tag => !handled tag) row

def selected (handled : Tag → Bool) (row : Row Tag Payload) : Row Tag Payload :=
  filter handled row

@[simp] theorem lookup_normalize (merge : Payload → Payload → Payload)
    (tag : Tag) (row : Variants.Row Tag Payload) :
    lookup tag (normalize merge row) = mergeAll merge tag row := by
  induction row with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    simp only [normalize, lookup, Raw.lookup_insert]
    change (if tag = key then _ else _) = _
    by_cases h : tag = key
    · subst key; simpa [mergeAll, lookup] using congrArg
        (fun old => some (match old with | none => value | some p => merge value p)) ih
    · simpa [mergeAll, h, lookup] using ih

/-- Normalization neither loses nor invents tags. -/
@[simp] theorem tags_normalize (merge : Payload → Payload → Payload)
    (tag : Tag) (row : Variants.Row Tag Payload) :
    tag ∈ (normalize merge row).entries.map Prod.fst ↔ tag ∈ row.map Prod.fst := by
  induction row with
  | nil => simp [normalize]
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    simp [normalize, Raw.tags_insert, ih]

/-- The empty/none case is precisely absence of the tag in the original row. -/
theorem mergeAll_eq_none_iff (merge : Payload → Payload → Payload)
    (tag : Tag) (row : Variants.Row Tag Payload) :
    mergeAll merge tag row = none ↔ tag ∉ row.map Prod.fst := by
  rw [← lookup_normalize]
  exact (Raw.lookup_eq_none_iff tag (normalize merge row).entries).trans
    (not_congr (tags_normalize merge tag row))

@[simp] theorem normalize_filter (merge : Payload → Payload → Payload)
    (keep : Tag → Bool) (row : Variants.Row Tag Payload) :
    normalize merge (row.filter (fun entry => keep entry.1)) =
      filter keep (normalize merge row) := by
  apply Row.ext
  induction row with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨tag, value⟩
    cases h : keep tag <;>
      simp [normalize, filter, h, Raw.filter_insert] at ih ⊢ <;> rw [ih]

/-- Removing handled tags commutes with merging, with literal row equality. -/
theorem normalize_residual (merge : Payload → Payload → Payload)
    (handled : Tag → Bool) (row : Variants.Row Tag Payload) :
    normalize merge (Variants.residual handled row) =
      residual handled (normalize merge row) :=
  normalize_filter merge (fun tag => !handled tag) row

@[simp] theorem lookup_residual (handled : Tag → Bool) (tag : Tag)
    (row : Row Tag Payload) :
    lookup tag (residual handled row) = if handled tag then none else lookup tag row := by
  change Raw.lookup tag (row.entries.filter (fun entry => !handled entry.1)) = _
  rw [Raw.lookup_filter (fun key => !handled key)]
  cases handled tag <;> rfl

@[simp] theorem lookup_selected (handled : Tag → Bool) (tag : Tag)
    (row : Row Tag Payload) :
    lookup tag (selected handled row) = if handled tag then lookup tag row else none :=
  Raw.lookup_filter handled tag row.entries

theorem mem_iff_lookup (tag : Tag) (payload : Payload) (row : Row Tag Payload) :
    (tag, payload) ∈ row.entries ↔ lookup tag row = some payload :=
  (Raw.lookup_eq_some_iff tag payload row.entries row.unique).symm

/-- A handled tag selects exactly the whole merged payload. -/
theorem selected_normalize (merge : Payload → Payload → Payload)
    (handled : Tag → Bool) (tag : Tag) (row : Variants.Row Tag Payload)
    (h : handled tag = true) :
    lookup tag (selected handled (normalize merge row)) = mergeAll merge tag row := by
  simp [h]

/-- Every residual entry is the entire merged payload of an unhandled tag. -/
theorem mem_residual_normalize_iff (merge : Payload → Payload → Payload)
    (handled : Tag → Bool) (tag : Tag) (payload : Payload)
    (row : Variants.Row Tag Payload) :
    (tag, payload) ∈ (residual handled (normalize merge row)).entries ↔
      handled tag = false ∧ mergeAll merge tag row = some payload := by
  rw [mem_iff_lookup, lookup_residual, lookup_normalize]
  cases handled tag <;> simp

/-- No handled tag remains, for any proposed partial payload. -/
theorem handled_no_residual_payload (handled : Tag → Bool) (tag : Tag)
    (row : Row Tag Payload) (h : handled tag = true) (payload : Payload) :
    (tag, payload) ∉ (residual handled row).entries := by
  rw [mem_iff_lookup, lookup_residual]
  simp [h]

/-- Exhaustiveness of a finite unique row is exactly coverage of its tags. -/
theorem residual_empty_iff (handled : Tag → Bool) (row : Row Tag Payload) :
    (residual handled row).entries = [] ↔
      ∀ tag payload, lookup tag row = some payload → handled tag = true := by
  change Variants.residual handled row.entries = [] ↔ _
  rw [Variants.residual_empty_iff]
  constructor
  · intro h tag payload hin
    exact h (tag, payload) ((mem_iff_lookup tag payload row).mpr hin)
  · intro h ⟨tag, payload⟩ hin
    exact h tag payload ((mem_iff_lookup tag payload row).mp hin)

/-- Exact coverage of the input tags yields an empty residual. -/
theorem case_exact_tags_empty (handled : Tag → Bool) (row : Row Tag Payload)
    (covers : ∀ tag, handled tag = true ↔ ∃ payload, lookup tag row = some payload) :
    (residual handled row).entries = [] := by
  apply (residual_empty_iff handled row).mpr
  intro tag payload h
  exact (covers tag).mpr ⟨payload, h⟩

/-- Omitting a present tag leaves a nonempty residual with its full payload. -/
theorem case_omitted_tag (handled : Tag → Bool) (row : Row Tag Payload)
    (tag : Tag) (payload : Payload) (present : lookup tag row = some payload)
    (omitted : handled tag = false) :
    (residual handled row).entries ≠ [] ∧
      lookup tag (residual handled row) = some payload ∧
      (tag, payload) ∈ (residual handled row).entries := by
  have hlookup : lookup tag (residual handled row) = some payload := by
    simp [omitted, present]
  have hmem := (mem_iff_lookup tag payload (residual handled row)).mpr hlookup
  exact ⟨List.ne_nil_of_mem hmem, hlookup, hmem⟩

/-- The omitted-tag result specialized to the original row and its full merge. -/
theorem case_omitted_normalize (merge : Payload → Payload → Payload)
    (handled : Tag → Bool) (row : Variants.Row Tag Payload)
    (tag : Tag) (payload : Payload) (present : mergeAll merge tag row = some payload)
    (omitted : handled tag = false) :
    (residual handled (normalize merge row)).entries ≠ [] ∧
      lookup tag (residual handled (normalize merge row)) = some payload ∧
      (tag, payload) ∈ (residual handled (normalize merge row)).entries :=
  case_omitted_tag handled (normalize merge row) tag payload
    (by simpa using present) omitted

/-- Substitute payloads without changing tags or their uniqueness. -/
def map (f : Payload → Payload') (row : Row Tag Payload) : Row Tag Payload' :=
  ⟨row.entries.map (fun entry => (entry.1, f entry.2)), by
    simpa [List.map_map, Function.comp_def] using row.unique⟩

/-- Substitution commutes with normalization if it preserves the chosen merge. -/
theorem normalize_map (merge : Payload → Payload → Payload)
    (merge' : Payload' → Payload' → Payload') (f : Payload → Payload')
    (hom : ∀ a b, f (merge a b) = merge' (f a) (f b))
    (row : Variants.Row Tag Payload) :
    normalize merge' (row.map (fun entry => (entry.1, f entry.2))) =
      map f (normalize merge row) := by
  apply Row.ext
  induction row with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨tag, payload⟩
    simp only [List.map_cons, normalize, map] at ih ⊢
    rw [Raw.map_insert merge merge' f hom, ih]

omit [DecidableEq Tag] in
theorem residual_map (handled : Tag → Bool) (f : Payload → Payload')
    (row : Row Tag Payload) :
    residual handled (map f row) = map f (residual handled row) := by
  apply Row.ext
  exact Variants.residual_map_payload handled f row.entries

/-- The existing structural rules give a sound upper bound, not an equivalence
or a normalization theorem for Subtype. -/
theorem variant_union_upper_bound {RowType : Type u}
    (leRow : RowType → RowType → Prop) (tag : Nat)
    (a b : StructuralBase.Ty RowType) :
    StructuralBase.Subtype leRow (.union (.variant tag a) (.variant tag b))
      (.variant tag (.union a b)) :=
  .unionElim (.variant (.unionLeft a b)) (.variant (.unionRight a b))

namespace Examples

open StructuralBase

abbrev int : Ty Unit := .base .int
abbrev str : Ty Unit := .base .str

theorem id_merge :
    (normalize Ty.union [("id", int), ("id", str)]).entries =
      [("id", Ty.union int str)] := by rfl

theorem id_handled_entirely :
    (residual (fun tag : String => tag == "id")
      (normalize Ty.union [("id", int), ("id", str)])).entries = [] := by decide

theorem str_leaves_num (merge : Payload → Payload → Payload) (s n : Payload) :
    (residual (fun tag : String => tag == "str")
      (normalize merge [("str", s), ("num", n)])).entries = [("num", n)] := by
  simp [residual, filter, normalize, Raw.insert]

end Examples
end Yulang.Variants.Merged
