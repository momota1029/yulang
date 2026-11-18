import Yulang.GeneralPresenceCheckedNormal252
namespace Yulang.GeneralPresenceSourceSupport255
open Core.PresenceGeneration
open GeneralNominalState (typeSources rowSources)

theorem row_subst (term : RowTerm α) (mapping : α → CompTerm Nat)
 (mapped : ∀ name, rowSources (mapping name).row ⊆ pool) :
 rowSources (term.subst mapping) ⊆ pool := by
 induction term with
 | var name => exact mapped name
 | empty => exact fun _ member => False.elim (List.not_mem_nil member)
 | join first last ihFirst ihLast =>
   intro name member
   exact (List.mem_append.mp member).elim (fun h => ihFirst h) (fun h => ihLast h)

theorem type_subst (term : TyTerm α) (mapping : α → CompTerm Nat)
 (mappedType : ∀ name, typeSources (mapping name).ty ⊆ pool)
 (mappedRow : ∀ name, rowSources (mapping name).row ⊆ pool) :
 typeSources (term.subst mapping) ⊆ pool := by
 induction term with
 | var name => exact mappedType name
 | base | bottom | top | emptyRecord | exactEmpty => exact fun _ member => False.elim (List.not_mem_nil member)
 | union first last ihFirst ihLast | inter first last ihFirst ihLast | pair first last ihFirst ihLast | recordDefault label first last ihFirst ihLast | record label first last ihFirst ihLast =>
   intro name member
   exact (List.mem_append.mp member).elim (fun h => ihFirst h) (fun h => ihLast h)
 | required label child ih | variant label child ih => exact ih
 | arrow first incoming last outgoing ihFirst ihLast =>
   intro name member
   rcases List.mem_append.mp member with rest | out
   · rcases List.mem_append.mp rest with front | back
     · rcases List.mem_append.mp front with arg | row
       · exact ihFirst arg
       · exact row_subst incoming mapping mappedRow row
     · exact ihLast back
   · exact row_subst outgoing mapping mappedRow out

theorem row_identity (term : RowTerm Nat) : rowSources (term.subst CompTerm.var) = rowSources term := by
 induction term <;> simp_all [RowTerm.subst,CompTerm.var,rowSources]

theorem type_identity (term : TyTerm Nat) : typeSources (term.subst CompTerm.var) = typeSources term := by
 induction term <;> simp_all [TyTerm.subst,CompTerm.var,typeSources,row_identity]

theorem row_collectors (term : RowTerm Nat) : GeneralPresenceSubstitutionSupport244.rowSources term = rowSources term := by
 induction term <;> simp_all [GeneralPresenceSubstitutionSupport244.rowSources,rowSources]

theorem type_collectors (term : TyTerm Nat) : GeneralPresenceSubstitutionSupport244.typeSources term = typeSources term := by
 induction term <;> simp_all [GeneralPresenceSubstitutionSupport244.typeSources,typeSources,row_collectors]

theorem union_atom_sources (term atom : TyTerm Nat) (present : atom ∈ GeneralPresenceUnionNormal252.atoms term) :
 typeSources atom ⊆ typeSources term := by
 induction term <;> simp_all [GeneralPresenceUnionNormal252.atoms,typeSources]
 case union first last ihFirst ihLast =>
   intro name member
   rcases present with one | two
   · exact List.mem_append_left _ (ihFirst one member)
   · exact List.mem_append_right _ (ihLast two member)

theorem inter_atom_sources (term atom : TyTerm Nat) (present : atom ∈ GeneralPresenceInterNormal252.atoms term) :
 typeSources atom ⊆ typeSources term := by
 induction term <;> simp_all [GeneralPresenceInterNormal252.atoms,typeSources]
 case inter first last ihFirst ihLast =>
   intro name member
   rcases present with one | two
   · exact List.mem_append_left _ (ihFirst one member)
   · exact List.mem_append_right _ (ihLast two member)
end Yulang.GeneralPresenceSourceSupport255
