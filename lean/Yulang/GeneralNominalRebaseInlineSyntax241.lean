import Yulang.GeneralNominalRebaseInline241
namespace Yulang.GeneralNominalRebaseInlineSyntax241
open Core.PresenceGeneration
open GeneralNominalFiniteEquationRealization236
open GeneralNominalRebaseInline241

theorem outside (absent : ∀ entry ∈ entries, entry.1 ≠ name) :
 substitution entries name = CompTerm.var name := by
 classical
 unfold substitution
 rw [dite_eq_right (by rintro ⟨entry,member,equal⟩; exact absent entry member equal)]

theorem at_entry
 (coherent : ∀ first ∈ entries, ∀ last ∈ entries, first.1 = last.1 → first.2 = last.2)
 (member : entry ∈ entries) : substitution entries entry.1 = ⟨entry.2,.var entry.1⟩ := by
 classical
 have found : ∃ selected ∈ entries, selected.1 = entry.1 := ⟨entry,member,rfl⟩
 unfold substitution
 rw [dite_eq_left found]
 have same := coherent (Classical.choose found) (Classical.choose_spec found).1 entry member (Classical.choose_spec found).2
 rw [same]

theorem singleton_at (name : Nat) (term : TyTerm Nat) :
 substitution [(name,term)] name = ⟨term,.var name⟩ :=
 at_entry (by intro first one last two _; cases List.mem_singleton.mp one; cases List.mem_singleton.mp two; rfl)
   (List.mem_singleton_self _)

theorem singleton_outside (different : actual ≠ privateName) :
 substitution [(privateName,term)] actual = CompTerm.var actual :=
 outside (by intro entry member; cases List.mem_singleton.mp member; exact Ne.symm different)

/-- An escaped value equality is retained as a source expression, not erased.
This is one simultaneous substitution, with no transitive normalization claim. -/
theorem alias_inline (different : actual ≠ privateName) (term : TyTerm Nat) :
 (GeneralNominalAllocation.equations actual (.var privateName)).map
   (atomSubst (substitution [(privateName,term)])) = GeneralNominalAllocation.equations actual term := by
 simp only [GeneralNominalAllocation.equations,List.map_cons,List.map_nil,atomSubst,TyTerm.subst,
   singleton_at,singleton_outside different,CompTerm.var]
end Yulang.GeneralNominalRebaseInlineSyntax241
