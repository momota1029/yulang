import Yulang.GeneralNominalRebaseInline241
namespace Yulang.GeneralNominalRebaseInlineSupport243
open Core.PresenceGeneration
open GeneralNominalState (typeSources rowSources atomSources)
open GeneralNominalRebaseInline241
open GeneralNominalFiniteEquationRealization236 (Entry)

theorem append_support {first last pool : List Nat} (held : first ++ last ⊆ pool) : first ⊆ pool ∧ last ⊆ pool :=
 ⟨fun _ member => held (List.mem_append_left _ member),fun _ member => held (List.mem_append_right _ member)⟩

theorem row_subst (term : RowTerm Nat) (mapping : Nat → CompTerm Nat)
 (mapped : ∀ name ∈ pool, rowSources (mapping name).row ⊆ pool)
 (supported : rowSources term ⊆ pool) : rowSources (term.subst mapping) ⊆ pool := by
 induction term with
 | var name => exact mapped name (supported (List.mem_singleton_self _))
 | empty => exact fun _ member => False.elim (List.not_mem_nil member)
 | join first last ihFirst ihLast =>
   have split := append_support supported
   intro name member
   exact (List.mem_append.mp member).elim (fun h => ihFirst split.1 h) (fun h => ihLast split.2 h)

theorem type_subst (term : TyTerm Nat) (mapping : Nat → CompTerm Nat)
 (mappedType : ∀ name ∈ pool, typeSources (mapping name).ty ⊆ pool)
 (mappedRow : ∀ name ∈ pool, rowSources (mapping name).row ⊆ pool)
 (supported : typeSources term ⊆ pool) : typeSources (term.subst mapping) ⊆ pool := by
 induction term with
 | var name => exact mappedType name (supported (List.mem_singleton_self _))
 | base | bottom | top | emptyRecord | exactEmpty => exact fun _ member => False.elim (List.not_mem_nil member)
 | union first last ihFirst ihLast | inter first last ihFirst ihLast | pair first last ihFirst ihLast | recordDefault label first last ihFirst ihLast | record label first last ihFirst ihLast =>
   have split := append_support supported
   intro name member
   exact (List.mem_append.mp member).elim (fun h => ihFirst split.1 h) (fun h => ihLast split.2 h)
 | required label child ih | variant label child ih => exact ih supported
 | arrow first incoming last outgoing ihFirst ihLast =>
   have split := append_support supported
   have left := append_support split.1
   have more := append_support left.1
   intro name member
   rcases List.mem_append.mp member with rest | out
   · rcases List.mem_append.mp rest with front | back
     · rcases List.mem_append.mp front with arg | row
       · exact ihFirst more.1 arg
       · exact row_subst incoming mapping mappedRow more.2 row
     · exact ihLast left.2 back
   · exact row_subst outgoing mapping mappedRow split.2 out

theorem substitution_type (supported : ∀ entry ∈ entries, typeSources entry.2 ⊆ pool)
 (member : name ∈ pool) : typeSources (substitution entries name).ty ⊆ pool := by
 classical
 unfold substitution
 split
 · rename_i found
   exact supported _ (Classical.choose_spec found).1
 · exact fun _ present => List.mem_singleton.mp present ▸ member

theorem substitution_row (entries : List Entry) (member : name ∈ pool) :
 rowSources (substitution entries name).row ⊆ pool := by
 classical
 unfold substitution
 split <;> exact fun _ present => List.mem_singleton.mp present ▸ member

theorem atom_inline_support (supported : ∀ entry ∈ entries, typeSources entry.2 ⊆ pool)
 (atom : PresenceNormalForm.Atom Nat) (held : atomSources atom ⊆ pool) :
 atomSources (atomSubst (substitution entries) atom) ⊆ pool := by
 cases atom with
 | tyLe first last =>
   have split := append_support held
   intro name member
   exact (List.mem_append.mp member).elim
     (fun h => type_subst first _ (fun _ member => substitution_type supported member) (fun _ member => substitution_row entries member) split.1 h)
     (fun h => type_subst last _ (fun _ member => substitution_type supported member) (fun _ member => substitution_row entries member) split.2 h)
 | rowLe first last =>
   have split := append_support held
   intro name member
   exact (List.mem_append.mp member).elim
     (fun h => row_subst first _ (fun _ member => substitution_row entries member) split.1 h)
     (fun h => row_subst last _ (fun _ member => substitution_row entries member) split.2 h)
end Yulang.GeneralNominalRebaseInlineSupport243
