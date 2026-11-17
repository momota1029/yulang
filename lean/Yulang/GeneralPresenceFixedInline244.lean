import Yulang.GeneralPresenceCrossRead244
/-! One fixed external definition block is syntactically idempotent under its
own inlining. Changing blocks or alternating owners is a different operation. -/
namespace Yulang.GeneralPresenceFixedInline244
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244
open GeneralPresenceSubstitutionSupport244
open GeneralPresenceOwnerRewrite244
open GeneralPresenceCrossRead244
variable {Name : Type} [DecidableEq Name]

theorem row_fixed (entries : List (Entry Name)) (term : RowTerm Name) :
 term.subst (substitution entries) = term := by
 induction term <;> simp_all [RowTerm.subst,substitution]

omit [DecidableEq Name] in
theorem avoid_append (held : Avoid entries (first ++ last)) : Avoid entries first ∧ Avoid entries last :=
 ⟨fun source member => held source (List.mem_append_left _ member),
 fun source member => held source (List.mem_append_right _ member)⟩

theorem type_fixed (entries : List (Entry Name)) (term : TyTerm Name)
 (outside : Avoid entries (typeSources term)) : term.subst (substitution entries) = term := by
 induction term with
 | var name => exact target_unchanged (outside name (by simp [typeSources]))
 | base | bottom | top | emptyRecord | exactEmpty => rfl
 | union first last one two =>
   simp only [TyTerm.subst,one (avoid_append outside).1,two (avoid_append outside).2]
 | inter first last one two =>
   simp only [TyTerm.subst,one (avoid_append outside).1,two (avoid_append outside).2]
 | pair first last one two =>
   simp only [TyTerm.subst,one (avoid_append outside).1,two (avoid_append outside).2]
 | record label first last one two =>
   simp only [TyTerm.subst,one (avoid_append outside).1,two (avoid_append outside).2]
 | recordDefault label first last one two =>
   simp only [TyTerm.subst,one (avoid_append outside).1,two (avoid_append outside).2]
 | required label child ih => simp only [TyTerm.subst,ih outside]
 | variant label child ih => simp only [TyTerm.subst,ih outside]
 | arrow first incoming last outgoing one two =>
   have split := avoid_append outside
   have left := avoid_append split.1
   have front := avoid_append left.1
   simp only [TyTerm.subst,one front.1,two left.2,row_fixed]

theorem rhs_fixed (entries : List (Entry Name)) (external : External entries) (name : Name) :
 (substitution entries name).ty.subst (substitution entries) = (substitution entries name).ty := by
 cases found : lookup entries name with
 | none => simp [substitution,found,TyTerm.subst]
 | some term =>
   have outside := external (name,term) (lookup_member found)
   simpa [substitution,found] using type_fixed entries term outside

theorem type_idempotent (entries : List (Entry Name)) (external : External entries) (term : TyTerm Name) :
 (term.subst (substitution entries)).subst (substitution entries) = term.subst (substitution entries) := by
 induction term with
 | var name => exact rhs_fixed entries external name
 | base | bottom | top | emptyRecord | exactEmpty => rfl
 | union first last one two => simp only [TyTerm.subst,one,two]
 | inter first last one two => simp only [TyTerm.subst,one,two]
 | pair first last one two => simp only [TyTerm.subst,one,two]
 | record label first last one two => simp only [TyTerm.subst,one,two]
 | recordDefault label first last one two => simp only [TyTerm.subst,one,two]
 | required label child ih => simp only [TyTerm.subst,ih]
 | variant label child ih => simp only [TyTerm.subst,ih]
 | arrow first incoming last outgoing one two => simp only [TyTerm.subst,one,two,row_fixed]

theorem atom_idempotent (entries : List (Entry Name)) (external : External entries)
 (atom : PresenceNormalForm.Atom Name) :
 atomSubst (substitution entries) (atomSubst (substitution entries) atom) = atomSubst (substitution entries) atom := by
 cases atom <;> simp only [atomSubst,type_idempotent entries external,row_fixed]

theorem block_idempotent (entries : List (Entry Name)) (external : External entries)
 (atoms : List (PresenceNormalForm.Atom Name)) :
 (atoms.map (atomSubst (substitution entries))).map (atomSubst (substitution entries)) =
 atoms.map (atomSubst (substitution entries)) := by
 simp only [List.map_map,Function.comp_def,atom_idempotent entries external]
end Yulang.GeneralPresenceFixedInline244
