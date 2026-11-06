import Yulang.MethodResolutionCost

/-!
# A finite role-method index that preserves the actual selection result

An index entry summarizes all declarations of one method name as zero, one
distinct `(role, declaration)`, or at least two. Inserting a duplicate does
not introduce ambiguity, and insertion order never selects a winner.

`Scope` has an arbitrary function for method lookup. The bridge below supplies
that function by a finite declaration catalog and proves the indexed result
equal to `MethodResolution.unknown`. A catalog must be functional at each
`(role, name)`; duplicate imports of the same declaration remain permitted.
The index is built from the visible part of this catalog, not by scanning all
visible roles again at each selection site.

The instrumented build counts two abstract table operations and at most one
candidate comparison per entry. Visibility filtering and the representation
cost of persistent table lookup/update are separate; this is not a claim that
an arbitrary Rust hash table has constant worst-case cost.
-/

namespace Yulang.MethodResolutionIndex

open MethodResolution
open Methods (Selection)

def insertCount [DecidableEq α] (candidate : α) : Selection α → Selection α × Nat
  | .missing => (.unique candidate, 0)
  | .unique previous => (if candidate = previous then .unique previous else .ambiguous, 1)
  | .ambiguous => (.ambiguous, 0)

def insert [DecidableEq α] (candidate : α) (summary : Selection α) : Selection α :=
  (insertCount candidate summary).1

theorem insertCount_bound [DecidableEq α] (candidate : α) (summary : Selection α) :
    (insertCount candidate summary).2 ≤ 1 := by
  cases summary <;> simp [insertCount]

theorem insert_select [DecidableEq α] (candidate : α) (members : List α) :
    insert candidate (Methods.select members) = Methods.select (candidate :: members) := by
  cases selected : Methods.select members with
  | missing =>
      have absent := (Methods.select_missing_iff members).mp selected
      simp only [insert, insertCount]
      symm
      apply (Methods.select_unique_iff _ _).mpr
      refine ⟨List.mem_cons_self, ?_⟩
      intro other member
      exact (List.mem_cons.mp member).elim id (fun impossible => False.elim (absent other impossible))
  | unique previous =>
      obtain ⟨present, unique⟩ := (Methods.select_unique_iff members previous).mp selected
      by_cases same : candidate = previous
      · simp only [insert, insertCount, same, ↓reduceIte]
        symm
        apply (Methods.select_unique_iff _ _).mpr
        exact ⟨List.mem_cons_self, fun other member =>
          (List.mem_cons.mp member).elim id (unique other)⟩
      · simp only [insert, insertCount, same, ↓reduceIte]
        symm
        apply (Methods.select_ambiguous_iff _).mpr
        exact ⟨candidate, List.mem_cons_self, previous, List.mem_cons_of_mem _ present, same⟩
  | ambiguous =>
      obtain ⟨first, firstMember, last, lastMember, different⟩ :=
        (Methods.select_ambiguous_iff members).mp selected
      simp only [insert, insertCount]
      symm
      apply (Methods.select_ambiguous_iff _).mpr
      exact ⟨first, List.mem_cons_of_mem _ firstMember, last, List.mem_cons_of_mem _ lastMember, different⟩

structure Entry where
  name : Nat
  role : Nat
  declaration : Nat
  deriving DecidableEq, Repr

abbrev Index := Nat → Selection (Nat × Nat)

def addEntry (entry : Entry) (index : Index) : Index :=
  fun name => if name = entry.name then insert (entry.role, entry.declaration) (index name)
    else index name

def buildIndex : List Entry → Index
  | [] => fun _ => .missing
  | entry :: rest => addEntry entry (buildIndex rest)

def namedCandidates (entries : List Entry) (name : Nat) : List (Nat × Nat) :=
  (entries.filter fun entry => decide (entry.name = name)).map fun entry =>
    (entry.role, entry.declaration)

theorem mem_namedCandidates (entries : List Entry) (name : Nat) (candidate : Nat × Nat) :
    candidate ∈ namedCandidates entries name ↔
      ∃ entry ∈ entries, entry.name = name ∧ (entry.role, entry.declaration) = candidate := by
  simp only [namedCandidates, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨entry, ⟨present, same⟩, value⟩
    exact ⟨entry, present, same, value⟩
  · rintro ⟨entry, present, same, value⟩
    exact ⟨entry, ⟨present, same⟩, value⟩

theorem buildIndex_exact (entries : List Entry) (name : Nat) :
    buildIndex entries name = Methods.select (namedCandidates entries name) := by
  induction entries generalizing name with
  | nil => rfl
  | cons entry rest ih =>
      by_cases same : entry.name = name
      · simp [buildIndex, addEntry, ← same, ih, insert_select, namedCandidates]
      · simp [buildIndex, addEntry, Ne.symm same, ih, namedCandidates, same]

/-- Permutations and repeated imports are observationally immaterial. -/
theorem buildIndex_ext (left right : List Entry)
    (sameMembers : ∀ entry, entry ∈ left ↔ entry ∈ right) :
    buildIndex left = buildIndex right := by
  funext name
  rw [buildIndex_exact, buildIndex_exact]
  apply Methods.select_ext
  intro candidate
  simp only [mem_namedCandidates, sameMembers]

theorem buildIndex_perm (left right : List Entry) (permutation : left.Perm right) :
    buildIndex left = buildIndex right := buildIndex_ext left right (fun _ => permutation.mem_iff)

def Functional (entries : List Entry) : Prop :=
  ∀ first ∈ entries, ∀ last ∈ entries,
    first.role = last.role → first.name = last.name → first.declaration = last.declaration

def lookupRef : List Entry → Nat → Nat → Option Nat
  | [], _, _ => none
  | entry :: rest, role, name =>
      if entry.role = role ∧ entry.name = name then some entry.declaration
      else lookupRef rest role name

theorem lookupRef_sound (entries : List Entry) (role name declaration : Nat)
    (found : lookupRef entries role name = some declaration) :
    ∃ entry ∈ entries, entry.role = role ∧ entry.name = name ∧ entry.declaration = declaration := by
  induction entries with
  | nil => simp [lookupRef] at found
  | cons entry rest ih =>
      by_cases hit : entry.role = role ∧ entry.name = name
      · have same : entry.declaration = declaration := by simpa [lookupRef, hit] using found
        exact ⟨entry, List.mem_cons_self, hit.1, hit.2, same⟩
      · have tail : lookupRef rest role name = some declaration := by simpa [lookupRef, hit] using found
        obtain ⟨other, member, facts⟩ := ih tail
        exact ⟨other, List.mem_cons_of_mem _ member, facts⟩

theorem lookupRef_complete (entries : List Entry) (functional : Functional entries)
    (entry : Entry) (present : entry ∈ entries) :
    lookupRef entries entry.role entry.name = some entry.declaration := by
  induction entries with
  | nil => simp at present
  | cons first rest ih =>
      by_cases hit : first.role = entry.role ∧ first.name = entry.name
      · have same := functional first List.mem_cons_self entry present hit.1 hit.2
        simp [lookupRef, hit, same]
      · have later : entry ∈ rest := by
          rcases List.mem_cons.mp present with equal | member
          · subst first
            exact False.elim (hit ⟨rfl, rfl⟩)
          · exact member
        have tail : Functional rest := fun left hl right hr =>
          functional left (List.mem_cons_of_mem _ hl) right (List.mem_cons_of_mem _ hr)
        simpa only [lookupRef, hit, ↓reduceIte] using ih tail later

def catalogScope (entries : List Entry) (visible : List Nat) : Scope :=
  ⟨visible, lookupRef entries⟩

def visibleEntries (entries : List Entry) (visible : List Nat) : List Entry :=
  entries.filter fun entry => decide (entry.role ∈ visible)

theorem catalog_candidates_exact (entries : List Entry) (visible : List Nat)
    (functional : Functional entries) (name role declaration : Nat) :
    (role, declaration) ∈ namedCandidates (visibleEntries entries visible) name ↔
      Candidate (catalogScope entries visible) name role declaration := by
  rw [mem_namedCandidates]
  constructor
  · rintro ⟨entry, member, named, pair⟩
    have facts : entry ∈ entries ∧ entry.role ∈ visible := by simpa [visibleEntries] using member
    have roleSame : entry.role = role := congrArg Prod.fst pair
    have declarationSame : entry.declaration = declaration := congrArg Prod.snd pair
    refine ⟨?_, ?_⟩
    · simpa only [catalogScope, ← roleSame] using facts.2
    · have lookup := lookupRef_complete entries functional entry facts.1
      simpa only [catalogScope, roleSame, named, declarationSame] using lookup
  · rintro ⟨roleVisible, found⟩
    obtain ⟨entry, member, roleSame, named, declarationSame⟩ :=
      lookupRef_sound entries role name declaration found
    refine ⟨entry, ?_, named, Prod.ext roleSame declarationSame⟩
    simp only [visibleEntries, List.mem_filter, decide_eq_true_eq]
    exact ⟨member, by simpa only [catalogScope, roleSame] using roleVisible⟩

def indexedUnknown (index : Index) (name : Nat) : Selection Reference :=
  match index name with
  | .missing => .unique (.field name)
  | .unique (role, declaration) => .unique (.role role declaration)
  | .ambiguous => .ambiguous

/-- A finite, functional declaration catalog gives the same answer as the
existing visible-role scan, for every method name and visibility list. -/
theorem indexedUnknown_exact (entries : List Entry) (visible : List Nat)
    (functional : Functional entries) (name : Nat) :
    indexedUnknown (buildIndex (visibleEntries entries visible)) name =
      unknown (catalogScope entries visible) name := by
  have same : buildIndex (visibleEntries entries visible) name =
      Methods.select (candidates (catalogScope entries visible) name) := by
    rw [buildIndex_exact]
    apply Methods.select_ext
    rintro ⟨role, declaration⟩
    rw [catalog_candidates_exact entries visible functional, mem_candidates]
  simp only [indexedUnknown, same, unknown]
  rfl

def indexedResolve (index : Index) (site : Site Row) : Selection Reference :=
  match site.receiver with
  | none => indexedUnknown index site.name
  | some receiver => known receiver site.name site.typedFallback

/-- Known receiver lookup is left intact; the finite index replaces exactly
the unknown-receiver scan of the actual resolver. -/
theorem indexedResolve_exact (entries : List Entry) (visible : List Nat)
    (functional : Functional entries) (name : Nat)
    (receiver : Option (StructuralBase.Ty Row)) (fallback : Selection Nat) :
    indexedResolve (buildIndex (visibleEntries entries visible))
      ⟨name, catalogScope entries visible, receiver, fallback⟩ =
      resolve ⟨name, catalogScope entries visible, receiver, fallback⟩ := by
  cases receiver with
  | none => exact indexedUnknown_exact entries visible functional name
  | some type => rfl

def addEntryCount (entry : Entry) (index : Index) : Index × Nat :=
  let selected := insertCount (entry.role, entry.declaration) (index entry.name)
  ((fun name => if name = entry.name then selected.1 else index name), 2 + selected.2)

theorem addEntryCount_value (entry : Entry) (index : Index) :
    (addEntryCount entry index).1 = addEntry entry index := by
  funext name
  by_cases same : name = entry.name <;> simp [addEntryCount, addEntry, insert, same]

theorem addEntryCount_bound (entry : Entry) (index : Index) :
    (addEntryCount entry index).2 ≤ 3 := by
  have bounded := insertCount_bound (entry.role, entry.declaration) (index entry.name)
  simp only [addEntryCount]
  omega

def buildIndexCount : List Entry → Index × Nat
  | [] => ((fun _ => .missing), 0)
  | entry :: rest =>
      let tail := buildIndexCount rest
      let next := addEntryCount entry tail.1
      (next.1, tail.2 + next.2)

theorem buildIndexCount_value (entries : List Entry) :
    (buildIndexCount entries).1 = buildIndex entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih => simp only [buildIndexCount, addEntryCount_value, ih, buildIndex]

theorem buildIndexCount_bound (entries : List Entry) :
    (buildIndexCount entries).2 ≤ 3 * entries.length := by
  induction entries with
  | nil => simp [buildIndexCount]
  | cons entry rest ih =>
      have next := addEntryCount_bound entry (buildIndexCount rest).1
      simp only [buildIndexCount, List.length_cons]
      omega

/-- An abstract index query is one table operation; its representation cost
is deliberately left to the eventual persistent map implementation. -/
def queryIndexCount (index : Index) (name : Nat) : Selection (Nat × Nat) × Nat :=
  (index name, 1)

def indexedUnknownCount (index : Index) (name : Nat) : Selection Reference × Nat :=
  let queried := queryIndexCount index name
  let result := match queried.1 with
    | .missing => .unique (.field name)
    | .unique (role, declaration) => .unique (.role role declaration)
    | .ambiguous => .ambiguous
  (result, queried.2 + 1)

theorem indexedUnknownCount_value (index : Index) (name : Nat) :
    (indexedUnknownCount index name).1 = indexedUnknown index name := by
  rfl

theorem indexedUnknownCount_steps (index : Index) (name : Nat) :
    (indexedUnknownCount index name).2 = 2 := rfl

def queryNamesCount (index : Index) : List Nat → List (Selection Reference) × Nat
  | [] => ([], 0)
  | name :: rest =>
      let selected := indexedUnknownCount index name
      let tail := queryNamesCount index rest
      (selected.1 :: tail.1, selected.2 + tail.2)

theorem queryNamesCount_value (index : Index) (names : List Nat) :
    (queryNamesCount index names).1 = names.map (indexedUnknown index) := by
  induction names with
  | nil => rfl
  | cons name rest ih => simp only [queryNamesCount, indexedUnknownCount_value, List.map_cons, ih]

theorem queryNamesCount_steps (index : Index) (names : List Nat) :
    (queryNamesCount index names).2 = 2 * names.length := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
      simp only [queryNamesCount, indexedUnknownCount_steps, ih, List.length_cons]
      omega

/-- One index build followed by all name queries. The `entries` parameter is
the already visible catalog; the visibility pass itself is not charged here. -/
def resolveNamesCount (entries : List Entry) (names : List Nat) : List (Selection Reference) × Nat :=
  let indexed := buildIndexCount entries
  let selected := queryNamesCount indexed.1 names
  (selected.1, indexed.2 + selected.2)

theorem resolveNamesCount_exact (entries : List Entry) (visible : List Nat)
    (functional : Functional entries) (names : List Nat) :
    (resolveNamesCount (visibleEntries entries visible) names).1 =
      names.map (unknown (catalogScope entries visible)) := by
  simp only [resolveNamesCount, queryNamesCount_value, buildIndexCount_value]
  apply List.map_congr_left
  intro name _
  exact indexedUnknown_exact entries visible functional name

/-- An actual one-build/many-query interpreter uses at most `3D + 2N`
abstract operations for `D` visible declarations and `N` selection names.
No well-formedness or successful selection premise is needed for the bound. -/
theorem resolveNamesCount_bound (entries : List Entry) (names : List Nat) :
    (resolveNamesCount entries names).2 ≤ 3 * entries.length + 2 * names.length := by
  simp only [resolveNamesCount, queryNamesCount_steps]
  exact Nat.add_le_add_right (buildIndexCount_bound entries) _

end Yulang.MethodResolutionIndex
