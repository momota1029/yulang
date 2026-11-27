import Yulang.GeneralDeclarativeNestedIndex332
import Yulang.GeneralDeclarativeI65I74AttachedInputField472

namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open Yulang.GeneralDeclarativeHead320 (Equation)
open Yulang.GeneralDeclarativeNestedIndex332 (direct)
open Yulang.GeneralNominalCenteredHeadMatExpressions (Expr)

def indexed (n : Nat) (base : Nat) : List Equation → Option (Nat × Expr)
  | [] => none
  | e :: es => if e.left == n then some (base,e.right) else indexed n (base + 1) es

theorem erases_to_same_direct (n : Nat) (base : Nat) (rows : List Equation) :
    (indexed n base rows).map Prod.snd = direct rows n := by
  induction rows generalizing base with
  | nil => rfl
  | cons row tail ih =>
    simp only [indexed, direct, List.find?_cons]
    split <;> rename_i agrees
    · simp [agrees]
    · cases test : (row.left == n) <;> simp_all [direct]

theorem indexed_lower (n : Nat) (rows : List Equation) (start v : Nat) (r : Expr)
    (hit : indexed n start rows = some (v,r)) : start ≤ v := by
  induction rows generalizing start with
  | nil => cases hit
  | cons h t ih =>
    simp only [indexed] at hit
    split at hit
    · cases hit; omega
    · have step := ih (start + 1) hit
      omega

theorem checks_actual_ordinal (n base i : Nat) (rows : List Equation) (rhs : Expr)
    (read : indexed n base rows = some (base + i, rhs)) :
    rows[i]? = some (⟨n,rhs⟩ : Equation) := by
  induction rows generalizing base i with
  | nil => cases read
  | cons row tail ih =>
    by_cases center : row.left = n
    · simp [indexed, center] at read
      cases row with
      | mk l r =>
        dsimp at center read
        obtain ⟨zero, same⟩ := read
        have atZero : i = 0 := by omega
        subst i; subst n; subst r; rfl
    · simp [indexed, center] at read
      cases i with
      | zero =>
        have impossible := indexed_lower n tail (base + 1) base rhs (by simpa using read)
        omega
      | succ i =>
        have step : indexed n (base + 1) tail = some ((base + 1) + i,rhs) := by
          have align : base + (i + 1) = (base + 1) + i := by omega
          exact align ▸ read
        simpa using ih (base+1) i step

def checkedSubsequence (raw : List Equation) : List (Nat × Equation) → Bool
  | [] => true
  | (ordinal,row)::more =>
    (decide (raw[ordinal]? = some row)) && checkedSubsequence raw more

def projected (n : Nat) (supported : List (Nat × Equation)) : Option (Nat × Expr) :=
  (supported.find? fun stamped => stamped.2.left == n).map fun stamped =>
    (stamped.1,stamped.2.right)

theorem checkedSubsequence_exact {raw : List Equation} {supported : List (Nat × Equation)} :
    checkedSubsequence raw supported = true ↔
      ∀ pair ∈ supported, raw[pair.1]? = some pair.2 := by
  induction supported with
  | nil => simp [checkedSubsequence]
  | cons p ps ih =>
    rcases p with ⟨i,e⟩
    simp [checkedSubsequence, ih]

theorem projected_erases (n : Nat) (supported : List (Nat × Equation)) :
    (projected n supported).map Prod.snd = direct (supported.map Prod.snd) n := by
  induction supported with
  | nil => rfl
  | cons h t ih =>
    rcases h with ⟨ordinal,row⟩
    cases test : (row.left == n) <;>
      simp_all [projected, direct]

theorem unErased_row_really_exists {raw : List Equation} {supported : List (Nat × Equation)}
    (ok : checkedSubsequence raw supported = true) {n i : Nat} {rhs : Expr}
    (found : projected n supported = some (i,rhs)) : raw[i]? = some (⟨n,rhs⟩ : Equation) := by
  unfold projected at found
  cases h : supported.find? (fun stamped => stamped.2.left == n) with
  | none => simp [h] at found
  | some stamp =>
    have key := List.find?_some h
    have existsIn := List.mem_of_find?_eq_some h
    obtain ⟨o,⟨owner,e⟩⟩ := stamp
    have got : raw[o]? = some (⟨owner,e⟩ : Equation) :=
      checkedSubsequence_exact.mp ok (o,⟨owner,e⟩) existsIn
    have same : owner = n := by simpa using key
    obtain ⟨rfl,rfl⟩ : o = i ∧ e = rhs := by simpa [h] using found
    subst owner
    exact got

structure StampedRead where
  raw : Nat
  author : Nat
  row : Equation

def valid (r a : List Equation) (s : List StampedRead) : Bool :=
  checkedSubsequence r (s.map fun x => (x.raw,x.row)) &&
    checkedSubsequence a (s.map fun x => (x.author,x.row))

def first (n : Nat) (rows : List StampedRead) : Option StampedRead :=
  rows.find? fun x => x.row.left == n

theorem first_uses_two_actual_coordinates (r a : List Equation) (s : List StampedRead)
  (ok : valid r a s = true) {n : Nat} {picked : StampedRead} (found : first n s = some picked) :
    r[picked.raw]? = some picked.row ∧ a[picked.author]? = some picked.row ∧ picked.row.left = n := by
  have inside : picked ∈ s := List.mem_of_find?_eq_some found
  have key : picked.row.left = n := by simpa using List.find?_some found
  obtain ⟨rOk,aOk⟩ := Bool.and_eq_true_iff.mp ok
  exact ⟨checkedSubsequence_exact.mp rOk _ (List.mem_map.mpr ⟨picked,inside,rfl⟩),
    checkedSubsequence_exact.mp aOk _ (List.mem_map.mpr ⟨picked,inside,rfl⟩),key⟩

theorem first_erases_to_unchanged_old_result (n : Nat) (rows : List StampedRead) :
    (first n rows).map (fun x => x.row.right) = direct (rows.map StampedRead.row) n := by
  induction rows with
  | nil => rfl
  | cons h t ih =>
    cases test : (h.row.left == n) <;> simp_all [first, direct]

open Yulang.GeneralDeclarativeHead320 (Equation)
private abbrev OldState := Yulang.GeneralDeclarativeHead320.State
open Yulang.GeneralDeclarativeNestedView332 (Sources expand)
private abbrev OldAlias := Yulang.GeneralDeclarativeLowerKnown321.Alias
open Yulang.GeneralDeclarativeOrigins321 (restriction backed_iff)
open Yulang.GeneralDeclarativeWitnessOrigins350 (Table Attached support)

def toOldSources {raw : OldState} {table : Table} (supplied : Attached raw table)
    (offered : List StampedRead)
    (matched : valid raw.equations table.authored offered = true)
    (target : Nat → Nat)
    (ground : ∀ n, OldAlias (restriction (support supplied)) n (target n)) :
    Sources (restriction (support supplied)) where
  visible := fun n => (first (target n) offered).map (fun x => x.row.right)
  authorized := by
    intro n rhs h
    cases got : first (target n) offered with
    | none => simp [got] at h
    | some marked =>
      have rights := first_uses_two_actual_coordinates _ _ _ matched got
      obtain ⟨_,authored,owner⟩ := rights
      have actual : marked.row.right = rhs := by simpa [got] using h
      refine ⟨target n,ground n,?_⟩
      have validRow : marked.row ∈ (restriction (support supplied)).equations :=
        (backed_iff (support supplied) marked.row).mpr
          ⟨.source,List.mem_of_getElem? authored,.source⟩
      have same : marked.row = (⟨target n,rhs⟩ : Equation) := by
        cases hrow : marked.row with
        | mk left right =>
          simp only [hrow] at owner actual
          subst left; subst right; rfl
      exact same ▸ validRow
  spines := fun _ => none
  spine_sound := by intro n raw tail h; cases h

theorem exact_before_capture {raw : OldState} {table : Table} (supplied : Attached raw table)
    (offered : List StampedRead)
    (matched : valid raw.equations table.authored offered = true)
    (target : Nat → Nat)
    (ground : ∀ n, OldAlias (restriction (support supplied)) n (target n))
    (n : Nat) :
    (toOldSources supplied offered matched target ground).visible n =
      direct (offered.map StampedRead.row) (target n) :=
  first_erases_to_unchanged_old_result _ _

private theorem sources_ext {s : OldState} (a b : Sources s)
    (vis : a.visible = b.visible) (sp : a.spines = b.spines) : a = b := by
  cases a with
  | mk av ah asp asound =>
    cases b with
    | mk bv bh bsp bsound =>
      dsimp at vis sp
      subst bv; subst bsp; rfl

theorem exact_rows_in_old_source_view {raw : OldState} {table : Table} (supplied : Attached raw table)
    (offered : List StampedRead) (matched : valid raw.equations table.authored offered = true) :
    offered.map StampedRead.row ⊆ (restriction (support supplied)).equations := by
  intro row inside
  obtain ⟨p,there,rfl⟩ := List.mem_map.mp inside
  have part := (Bool.and_eq_true_iff.mp matched).2
  have atAuthor : table.authored[p.author]? = some p.row :=
    checkedSubsequence_exact.mp part _ (List.mem_map.mpr ⟨p,there,rfl⟩)
  exact (backed_iff (support supplied) p.row).mpr ⟨.source,List.mem_of_getElem? atAuthor,.source⟩

theorem same_old_index_all_fields {raw : OldState} {table : Table} (supplied : Attached raw table)
    (offered : List StampedRead)
    (matched : valid raw.equations table.authored offered = true)
    (target : Nat → Nat)
    (ground : ∀ n, OldAlias (restriction (support supplied)) n (target n)) :
    toOldSources supplied offered matched target ground =
      Yulang.GeneralDeclarativeNestedIndex332.withAliases
        (offered.map StampedRead.row) (exact_rows_in_old_source_view supplied offered matched) target ground := by
  apply sources_ext
  · funext n
    exact exact_before_capture supplied offered matched target ground n
  · rfl

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
