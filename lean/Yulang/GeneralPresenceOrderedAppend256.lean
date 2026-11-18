import Yulang.GeneralPresenceOrderedSyntax247
namespace Yulang.GeneralPresenceOrderedAppend256
open Core.PresenceGeneration
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralPresenceOrderedSubstitution247 (mapping)
open GeneralPresenceOwnerRewrite244 (substitution)
variable {Name : Type} [DecidableEq Name]

omit [DecidableEq Name] in
theorem row_comp (term : RowTerm Name) (first last : Name → CompTerm Name) :
 (term.subst first).subst last = term.subst (fun name => (first name).subst last) := by
 induction term <;> simp_all [RowTerm.subst,CompTerm.subst]

omit [DecidableEq Name] in
theorem type_comp (term : TyTerm Name) (first last : Name → CompTerm Name) :
 (term.subst first).subst last = term.subst (fun name => (first name).subst last) := by
 induction term <;> simp_all [TyTerm.subst,CompTerm.subst,row_comp]

omit [DecidableEq Name] in
theorem row_identity (term : RowTerm Name) : term.subst CompTerm.var = term := by
 induction term <;> simp_all [RowTerm.subst,CompTerm.var]

omit [DecidableEq Name] in
theorem type_identity (term : TyTerm Name) : term.subst CompTerm.var = term := by
 induction term <;> simp_all [TyTerm.subst,CompTerm.var,row_identity]

theorem mapping_row (entries : List (Entry Name)) (name : Name) :
 (mapping entries name).row = .var name := by cases entries <;> rfl

theorem mapping_append (first last : List (Entry Name)) (name : Name) :
 (mapping (first ++ last) name).ty = (mapping last name).ty.subst (mapping first) := by
 induction first with
 | nil => exact (type_identity _).symm
 | cons entry rest ih =>
   change ((mapping (rest ++ last) name).ty.subst (substitution [entry])) = _
   rw [ih,type_comp]
   congr 1
   funext source
   change CompTerm.mk _ ((mapping rest source).row.subst (substitution [entry])) = CompTerm.mk _ (.var source)
   rw [mapping_row]
   rfl

theorem mapping_snoc (entries : List (Entry Name)) (entry : Entry Name) :
 (mapping (entries ++ [entry]) entry.1).ty = entry.2.subst (mapping entries) := by
 rw [mapping_append]
 simp [mapping,CompTerm.var,TyTerm.subst,substitution,GeneralPresenceOwnerRewrite244.lookup]
end Yulang.GeneralPresenceOrderedAppend256
