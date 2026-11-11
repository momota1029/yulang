import Yulang.GeneralRegistryChildOrder

/-!
# Canonical source-obligation order for actual child emission

Checked declaration IDs are retained; where clauses are sorted by their existing
unique clause IDs. No source allocation, implementation priority, or language
semantics is selected. The original declaration is not changed. Canonical views
preserve all declaration checks and exact complete emitted child structures.
This is the local emission prerequisite, not the complete canonicalLocalOrder
bridge for candidate classification at different final states.
-/
namespace Yulang.GeneralCanonicalChildOrder
open GeneralDeclarations GeneralRegistryReordering GeneralDeclarationDemands

private theorem key_injective (key : α → Nat) (xs : List α)
    (unique : (xs.map key).Nodup) (a b : α) (left : a ∈ xs) (right : b ∈ xs)
    (same : key a = key b) : a = b := by
  induction xs with
  | nil => cases left
  | cons head rest ih =>
    have pair := List.nodup_cons.mp unique
    rcases List.mem_cons.mp left with equalA | tailA
    · subst a
      rcases List.mem_cons.mp right with equalB | tailB
      · subst b; rfl
      · exact False.elim (pair.1 (List.mem_map.mpr ⟨b, tailB, same.symm⟩))
    · rcases List.mem_cons.mp right with equalB | tailB
      · subst b
        exact False.elim (pair.1 (List.mem_map.mpr ⟨a, tailA, same⟩))
      · exact ih pair.2 tailA tailB

def canonicalRequirements (clauses : List Clause) : List Clause :=
  clauses.mergeSort (fun a b => a.id ≤ b.id)

theorem canonicalRequirements_perm (clauses : List Clause) :
    clauses.Perm (canonicalRequirements clauses) := (List.mergeSort_perm clauses _).symm

/-- Sorting is independent of the old list order because each actual source ID
identifies one complete clause, not merely a role key. -/
theorem canonicalRequirements_eq (first last : List Clause)
    (unique : (first.map Clause.id).Nodup) (permuted : first.Perm last) :
    canonicalRequirements first = canonicalRequirements last := by
  have firstOrder := canonicalRequirements_perm first
  have lastOrder := canonicalRequirements_perm last
  have ordered (xs : List Clause) :
      (canonicalRequirements xs).Pairwise (fun a b => decide (a.id ≤ b.id) = true) := by
    exact List.pairwise_mergeSort
      (fun a b c ab bc => by simp only [decide_eq_true_eq] at *; exact Nat.le_trans ab bc)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Nat.le_total _ _) xs
  apply List.Perm.eq_of_pairwise _ (ordered first) (ordered last)
    (firstOrder.symm.trans (permuted.trans lastOrder))
  intro a b left right ab ba
  have same : a.id = b.id := Nat.le_antisymm (of_decide_eq_true ab) (of_decide_eq_true ba)
  exact key_injective Clause.id first unique a b (firstOrder.mem_iff.mpr left)
    (permuted.mem_iff.mpr (lastOrder.mem_iff.mpr right)) same

def canonicalDeclaration (declaration : Declaration) : Declaration :=
  { declaration with requirements := canonicalRequirements declaration.requirements }

theorem canonical_checked (declaration : Declaration)
    (checked : DeclarationChecked constructors roles declaration) :
    DeclarationChecked constructors roles (canonicalDeclaration declaration) :=
  checked_permute_requirements declaration _ (canonicalRequirements_perm _) checked

theorem canonical_declaration_eq (order : DeclarationReorders first last)
    (unique : (first.requirements.map Clause.id).Nodup) :
    canonicalDeclaration first = canonicalDeclaration last := by
  calc
    canonicalDeclaration first =
        { first with requirements := canonicalRequirements last.requirements } := by
      unfold canonicalDeclaration
      rw [canonicalRequirements_eq _ _ unique order.requirements]
    _ = canonicalDeclaration last := by
      rw [declarationReorders_update order]
      rfl

/-- An executable view of the existing emitter, using only the checked source
IDs for enumeration. Allocation stays indexed by the actual Clause. -/
def canonicalEmit (invocation : Nat) (declaration : Declaration)
    (checked : DeclarationChecked constructors roles declaration) (capture : Capture)
    (allocate : (clause : Clause) → Allocation roles clause) : List (Emission roles) :=
  emitAll invocation (canonicalDeclaration declaration)
    (canonical_checked declaration checked).signature capture allocate

/-- Exact equality of every emitted child, including materialization requests,
output equations and source IDs, for reordered versions of a checked declaration. -/
theorem canonicalEmit_reorders (invocation : Nat) (order : DeclarationReorders first last)
    (firstChecked : DeclarationChecked constructors roles first)
    (lastChecked : DeclarationChecked constructors roles last) (capture : Capture)
    (allocate : (clause : Clause) → Allocation roles clause) :
    canonicalEmit invocation first firstChecked capture allocate =
      canonicalEmit invocation last lastChecked capture allocate := by
  unfold canonicalEmit
  have same := canonical_declaration_eq order firstChecked.identified.1
  congr 1

/-- The canonical view does not discard, duplicate or fabricate a child. -/
theorem canonicalEmit_perm (invocation : Nat) (declaration : Declaration)
    (checked : DeclarationChecked constructors roles declaration) (capture : Capture)
    (allocate : (clause : Clause) → Allocation roles clause) :
    (emitAll invocation declaration checked.signature capture allocate).Perm
      (canonicalEmit invocation declaration checked capture allocate) :=
  GeneralRegistryChildOrder.emitAll_permute_requirements invocation declaration _
    (canonicalRequirements_perm _) checked.signature
    (canonical_checked declaration checked).signature capture allocate

end Yulang.GeneralCanonicalChildOrder
