import Yulang.GeneralNominalVersionedPool231

/-! Explicit finite binding enumeration from finite name/endpoint alphabets
and a length bound. These bounds are hypotheses, not a proof that a reachable
trace admits such alphabets or a uniform bound. This is NOT termination. -/
namespace Yulang.GeneralNominalVersionedFiniteBindings231
open GeneralNominalAllocation (Bindings)

/-- All words of length at most the supplied bound, allowing repetition. -/
def words (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n + 1 => [] :: alphabet.flatMap (fun head => (words alphabet n).map (head :: ·))

theorem mem_words (alphabet : List α) (bound : Nat) (items : List α)
    (within : ∀ item ∈ items, item ∈ alphabet) (short : items.length ≤ bound) :
    items ∈ words alphabet bound := by
  induction bound generalizing items with
  | zero =>
    have empty : items = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero short)
    subst items
    exact List.mem_singleton_self _
  | succ bound ih =>
    cases items with
    | nil => exact List.mem_cons_self
    | cons head tail =>
      apply List.mem_cons_of_mem
      apply List.mem_flatMap.mpr
      refine ⟨head,within head (List.mem_cons_self ..),?_⟩
      apply List.mem_map.mpr
      refine ⟨tail,ih tail (fun item member => within item (List.mem_cons_of_mem _ member)) ?_,rfl⟩
      exact Nat.le_of_succ_le_succ short

def alphabet (names endpoints : List Nat) : List (Nat × (Nat × Nat)) :=
  names.flatMap fun name => endpoints.flatMap fun lo => endpoints.map fun hi => (name,lo,hi)

theorem mem_alphabet (hn : name ∈ names) (hl : lo ∈ endpoints) (hh : hi ∈ endpoints) :
    (name,lo,hi) ∈ alphabet names endpoints := by
  exact List.mem_flatMap.mpr ⟨name,hn,List.mem_flatMap.mpr ⟨lo,hl,List.mem_map.mpr ⟨hi,hh,rfl⟩⟩⟩

def candidates (names endpoints : List Nat) (bound : Nat) : List Bindings :=
  words (alphabet names endpoints) bound

theorem bindings_included (bindings : Bindings)
    (within : ∀ entry ∈ bindings, entry.1 ∈ names ∧ entry.2.1 ∈ endpoints ∧ entry.2.2 ∈ endpoints)
    (short : bindings.length ≤ bound) : bindings ∈ candidates names endpoints bound := by
  apply mem_words
  · intro entry member
    obtain ⟨hn,hl,hh⟩ := within entry member
    exact mem_alphabet hn hl hh
  · exact short

theorem reserved_included (bindings : Bindings)
    (within : ∀ entry ∈ bindings, entry.1 ∈ names ∧ entry.2.1 ∈ endpoints ∧ entry.2.2 ∈ endpoints)
    (short : bindings.length ≤ bound) :
    GeneralNominalVersionedAllocation231.reserved state registry root bindings ⊆
      GeneralNominalVersionedPool231.sourcePool state registry root (candidates names endpoints bound) :=
  GeneralNominalVersionedPool231.reserved_included (bindings_included bindings within short)

end Yulang.GeneralNominalVersionedFiniteBindings231
