import Yulang.AutomaticRowSummaries
import Yulang.SemilinearRowAlgebra

/-!
# Whole-row decisions from original recursive row constraints

The finite input graph supplies every possible operation key; the ambient key
and slot identifier types may both be infinite. Each key is summarized by the
automatic guard checker, and successful results are assembled into the exact
finite-key semilinear row algebra. Whole-row containment and equality are then
decided against the original `RecursiveRows.Derives` sets, not merely against
independently supplied semilinear expressions.

`none` records a problem unsupported by the current guard-erasure check. Every returned
Boolean is exact, including false answers and equality of infinite rows.
-/

namespace Yulang.SolvedRecursiveRows

open SemilinearWeights (Weight Semi)
open SemilinearRowAlgebra (Row Meaning)

variable {n : Nat} {Key Slot : Type}

def keys [DecidableEq Key] (problem : RecursiveRows.Problem n Key Slot) : List Key :=
  (RecursiveRowGraph.headKeys (RecursiveRowGraph.compile problem)).eraseDups

theorem derives_key [DecidableEq Key] (problem : RecursiveRows.Problem n Key Slot)
    (slot : Slot) (key : Key) (weight : Weight n)
    (derived : RecursiveRows.Derives problem slot ⟨key, weight⟩) : key ∈ keys problem :=
  List.mem_eraseDups.mpr (RecursiveRowGraph.reachable_key _
    ((RecursiveRowGraph.reachable_iff_derives problem slot ⟨key, weight⟩).mpr derived))

def collect (choose : Key → Option (Semi n)) : List Key → Option (Row n Key)
  | [] => some []
  | key :: rest =>
      match choose key, collect choose rest with
      | some semi, some rows => some ((key, semi) :: rows)
      | _, _ => none

theorem collect_has_results (choose : Key → Option (Semi n)) (names : List Key)
    (rows : Row n Key) (returned : collect choose names = some rows) :
    ∀ key ∈ names, ∃ semi, choose key = some semi := by
  induction names generalizing rows with
  | nil => simp
  | cons name rest ih =>
      cases first : choose name <;> cases tail : collect choose rest <;>
        simp only [collect, first, tail] at returned <;> try contradiction
      case some.some semi remainder =>
        cases Option.some.inj returned
        intro key member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨semi, first⟩
        · exact ih remainder tail key member

theorem collect_meaning [DecidableEq Key] (choose : Key → Option (Semi n))
    (names : List Key) (rows : Row n Key) (returned : collect choose names = some rows)
    (key : Key) (weight : Weight n) :
    Meaning rows key weight ↔
      key ∈ names ∧ ∃ semi, choose key = some semi ∧ SemilinearWeights.Meaning semi weight := by
  induction names generalizing rows with
  | nil =>
      have empty : rows = [] := (Option.some.inj returned).symm
      simp [empty]
  | cons name rest ih =>
      cases first : choose name <;> cases tail : collect choose rest <;>
        simp only [collect, first, tail] at returned <;> try contradiction
      case some.some semi remainder =>
        cases Option.some.inj returned
        rw [SemilinearRowAlgebra.meaning_cons, ih remainder tail]
        constructor
        · rintro (⟨rfl, member⟩ | ⟨member, result⟩)
          · exact ⟨by simp, semi, first, member⟩
          · exact ⟨List.mem_cons_of_mem _ member, result⟩
        · rintro ⟨member, chosen, selected, fact⟩
          rcases List.mem_cons.mp member with rfl | member
          · have same : semi = chosen := Option.some.inj (first.symm.trans selected)
            exact Or.inl ⟨rfl, same ▸ fact⟩
          · exact Or.inr ⟨member, chosen, selected, fact⟩

theorem collect_exists_iff (choose : Key → Option (Semi n)) (names : List Key) :
    (∃ rows, collect choose names = some rows) ↔
      ∀ key ∈ names, ∃ semi, choose key = some semi := by
  constructor
  · rintro ⟨rows, returned⟩
    exact collect_has_results choose names rows returned
  · intro total
    induction names with
    | nil => exact ⟨[], rfl⟩
    | cons name rest ih =>
        obtain ⟨semi, first⟩ := total name (by simp)
        obtain ⟨rows, tail⟩ := ih (fun key member => total key (List.mem_cons_of_mem _ member))
        exact ⟨(name, semi) :: rows, by simp [collect, first, tail]⟩

def summarize [DecidableEq Key] [DecidableEq Slot]
    (problem : RecursiveRows.Problem n Key Slot) (slot : Slot) : Option (Row n Key) :=
  collect (fun key => AutomaticRowSummaries.summarize problem key slot) (keys problem)

theorem summarize_exact [DecidableEq Key] [DecidableEq Slot]
    (problem : RecursiveRows.Problem n Key Slot) (slot : Slot) (rows : Row n Key)
    (returned : summarize problem slot = some rows) (key : Key) (weight : Weight n) :
    Meaning rows key weight ↔ RecursiveRows.Derives problem slot ⟨key, weight⟩ := by
  rw [collect_meaning _ _ _ returned]
  constructor
  · rintro ⟨_, semi, selected, member⟩
    exact (AutomaticRowSummaries.summarize_exact problem key slot semi selected weight).mp member
  · intro derived
    have present := derives_key problem slot key weight derived
    obtain ⟨semi, selected⟩ := collect_has_results _ _ _ returned key present
    exact ⟨present, semi, selected,
      (AutomaticRowSummaries.summarize_exact problem key slot semi selected weight).mpr derived⟩

theorem summarize_decode [DecidableEq Key] [DecidableEq Slot]
    (problem : RecursiveRows.Problem n Key Slot) (slot : Slot) (rows : Row n Key)
    (returned : summarize problem slot = some rows) :
    SemilinearRowAlgebra.decode rows = RecursiveRows.Derives problem slot := by
  funext occurrence
  exact propext (summarize_exact problem slot rows returned occurrence.key occurrence.weights)

theorem summarize_supported_iff [DecidableEq Key] [DecidableEq Slot]
    (problem : RecursiveRows.Problem n Key Slot) (slot : Slot) :
    (∃ rows, summarize problem slot = some rows) ↔
      ∀ key ∈ keys problem,
        GuardedRowErasure.Harmless (CertifiedRowSummaries.normalizedProblem key problem) key := by
  rw [summarize, collect_exists_iff]
  apply forall_congr'
  intro key
  apply forall_congr'
  intro _
  rw [← AutomaticRowSummaries.check_exact]
  simp [AutomaticRowSummaries.summarize]

def querySubset [DecidableEq Key] [DecidableEq Slot]
    (left right : RecursiveRows.Problem n Key Slot) (leftSlot rightSlot : Slot) : Option Bool := do
  let source ← summarize left leftSlot
  let target ← summarize right rightSlot
  pure (SemilinearRowAlgebra.checkSubset source target)

theorem querySubset_exact [DecidableEq Key] [DecidableEq Slot]
    (left right : RecursiveRows.Problem n Key Slot) (leftSlot rightSlot : Slot)
    (answer : Bool) (returned : querySubset left right leftSlot rightSlot = some answer) :
    answer = true ↔ ∀ occurrence,
      RecursiveRows.Derives left leftSlot occurrence → RecursiveRows.Derives right rightSlot occurrence := by
  cases first : summarize left leftSlot with
  | none => simp [querySubset, first] at returned
  | some source =>
      cases second : summarize right rightSlot with
      | none => simp [querySubset, first, second] at returned
      | some target =>
          have same : SemilinearRowAlgebra.checkSubset source target = answer := by
            simpa [querySubset, first, second] using returned
          rw [← same, SemilinearRowAlgebra.checkSubset_sets,
            summarize_decode left leftSlot source first,
            summarize_decode right rightSlot target second]
          rfl

theorem querySubset_rejects [DecidableEq Key] [DecidableEq Slot]
    (left right : RecursiveRows.Problem n Key Slot) (leftSlot rightSlot : Slot)
    (answer : Bool) (returned : querySubset left right leftSlot rightSlot = some answer) :
    answer = false ↔ ∃ occurrence, RecursiveRows.Derives left leftSlot occurrence ∧
      ¬ RecursiveRows.Derives right rightSlot occurrence := by
  classical
  simpa only [Bool.not_eq_true, Classical.not_forall, exists_prop] using
    not_congr (querySubset_exact left right leftSlot rightSlot answer returned)

def queryEqual [DecidableEq Key] [DecidableEq Slot]
    (left right : RecursiveRows.Problem n Key Slot) (leftSlot rightSlot : Slot) : Option Bool := do
  let source ← summarize left leftSlot
  let target ← summarize right rightSlot
  pure (SemilinearRowAlgebra.checkEqual source target)

theorem queryEqual_exact [DecidableEq Key] [DecidableEq Slot]
    (left right : RecursiveRows.Problem n Key Slot) (leftSlot rightSlot : Slot)
    (answer : Bool) (returned : queryEqual left right leftSlot rightSlot = some answer) :
    answer = true ↔ RecursiveRows.Derives left leftSlot = RecursiveRows.Derives right rightSlot := by
  cases first : summarize left leftSlot with
  | none => simp [queryEqual, first] at returned
  | some source =>
      cases second : summarize right rightSlot with
      | none => simp [queryEqual, first, second] at returned
      | some target =>
          have same : SemilinearRowAlgebra.checkEqual source target = answer := by
            simpa [queryEqual, first, second] using returned
          rw [← same, SemilinearRowAlgebra.checkEqual_sets,
            summarize_decode left leftSlot source first,
            summarize_decode right rightSlot target second]

theorem queryEqual_rejects [DecidableEq Key] [DecidableEq Slot]
    (left right : RecursiveRows.Problem n Key Slot) (leftSlot rightSlot : Slot)
    (answer : Bool) (returned : queryEqual left right leftSlot rightSlot = some answer) :
    answer = false ↔ RecursiveRows.Derives left leftSlot ≠ RecursiveRows.Derives right rightSlot := by
  simpa only [Bool.not_eq_true] using
    not_congr (queryEqual_exact left right leftSlot rightSlot answer returned)

end Yulang.SolvedRecursiveRows
