import Yulang.GeneralRegistryReordering

/-!
# Reordering laws and unchanged source child obligations

These results relate actual declaration and emitted-child data. They do not
assume equality of resolver outcomes or choose source allocation identities.
A fixed interval capture and clause-indexed allocation are retained through
reordering, so the theorem does not justify a position-based allocator.
-/
namespace Yulang.GeneralRegistryChildOrder
open GeneralDeclarations GeneralRegistryReordering
open CommonRoleOutermostResolver (All₂)
open GeneralDeclarationDemands

private theorem related_reverse {relation : α → β → Prop}
    (related : All₂ relation xs ys) : All₂ (fun b a => relation a b) ys xs := by
  induction related with
  | nil => exact .nil
  | cons pair rest ih => exact .cons pair ih

private theorem perm_related_left {relation : α → β → Prop}
    (permuted : xs.Perm ys) (related : All₂ relation xs zs) :
    ∃ ws, zs.Perm ws ∧ All₂ relation ys ws := by
  induction permuted generalizing zs with
  | nil => cases related; exact ⟨[], .refl _, .nil⟩
  | cons head permutation ih =>
    cases related with
    | cons pair rest =>
      obtain ⟨ws, moved, paired⟩ := ih rest
      exact ⟨_ :: ws, moved.cons _, .cons pair paired⟩
  | swap first last rest =>
    cases related with
    | cons lastPair restPair =>
      cases restPair with
      | cons firstPair remaining =>
        exact ⟨_, List.Perm.swap _ _ _, .cons firstPair (.cons lastPair remaining)⟩
  | trans first last ih1 ih2 =>
    obtain ⟨middle, firstMove, firstPairs⟩ := ih1 related
    obtain ⟨endpoints, lastMove, lastPairs⟩ := ih2 firstPairs
    exact ⟨endpoints, firstMove.trans lastMove, lastPairs⟩

private theorem perm_related_right {relation : α → β → Prop}
    (related : All₂ relation xs ys) (permuted : ys.Perm zs) :
    ∃ ws, xs.Perm ws ∧ All₂ relation ws zs := by
  obtain ⟨ws, moved, paired⟩ := perm_related_left permuted (related_reverse related)
  exact ⟨ws, moved, related_reverse paired⟩

private theorem related_symm (related : All₂ DeclarationReorders xs ys) :
    All₂ DeclarationReorders ys xs := by
  induction related with
  | nil => exact .nil
  | cons pair rest ih => exact .cons (declarationReorders_symm pair) ih

private theorem related_trans (first : All₂ DeclarationReorders xs ys)
    (last : All₂ DeclarationReorders ys zs) : All₂ DeclarationReorders xs zs := by
  induction first generalizing zs with
  | nil => cases last; exact .nil
  | cons pair rest ih =>
    cases last with
    | cons next remaining => exact .cons (declarationReorders_trans pair next) (ih remaining)

theorem reorders_symm (order : Reorders first last) : Reorders last first := by
  obtain ⟨constructors, roles, middle, moved, related⟩ := order
  obtain ⟨target, visible, paired⟩ := perm_related_right (related_symm related) moved.symm
  exact ⟨constructors.symm, roles.symm, target, visible, paired⟩

theorem reorders_trans (ab : Reorders first middle) (bc : Reorders middle last) :
    Reorders first last := by
  obtain ⟨constructors, roles, a, firstMove, firstPairs⟩ := ab
  obtain ⟨constructors', roles', b, lastMove, lastPairs⟩ := bc
  obtain ⟨c, moved, paired⟩ := perm_related_right firstPairs lastMove
  exact ⟨constructors.trans constructors', roles.trans roles', c, firstMove.trans moved,
    related_trans paired lastPairs⟩

theorem reorders_checked_iff (order : Reorders first last) : Checked first ↔ Checked last :=
  ⟨reorders_checked order, reorders_checked (reorders_symm order)⟩

/-- Pure source emission can use a signature proof indexed by the actual clause,
not by its position in the declaration list. -/
theorem emitAll_pmap (invocation : Nat) (declaration : Declaration)
    (valid : declaration.Signature roles) (capture : Capture)
    (allocate : (clause : Clause) → Allocation roles clause) :
    emitAll invocation declaration valid capture allocate =
      declaration.requirements.pmap
        (fun clause signature => emit invocation declaration clause signature capture (allocate clause))
        valid.2.2.2 := by
  rw [List.pmap_eq_map_attach]
  rfl

/-- All generated children, input materialization requests, and repeated named
output equations survive a where-list permutation with their exact identities.
This is an emission theorem, not model satisfaction or candidate success. -/
theorem emitAll_permute_requirements (invocation : Nat) (declaration : Declaration)
    (requirements : List Clause) (order : declaration.requirements.Perm requirements)
    (valid : declaration.Signature roles)
    (valid' : ({ declaration with requirements := requirements } : Declaration).Signature roles)
    (capture : Capture) (allocate : (clause : Clause) → Allocation roles clause) :
    (emitAll invocation declaration valid capture allocate).Perm
      (emitAll invocation { declaration with requirements := requirements } valid' capture allocate) := by
  rw [emitAll_pmap, emitAll_pmap]
  have same (clause : Clause) (signature : clause.Signature roles) :
      emit invocation { declaration with requirements := requirements } clause signature capture
        (allocate clause) = emit invocation declaration clause signature capture (allocate clause) := rfl
  simp only [same]
  exact order.pmap _

end Yulang.GeneralRegistryChildOrder
