import Yulang.GeneralPresenceOrderedRecovery247
import Yulang.GeneralPresenceOwnerRewrite244
/-! A finite executable Presence substitution for sequential definition writes.
Unlike regular guarded closure environments, this representation stays within
actual TyTerm/Atom syntax. It is not a claim that arbitrary cyclic definitions
have a finite textual expansion. -/
namespace Yulang.GeneralPresenceOrderedSubstitution247
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOwnerRewrite244
open GeneralPresenceOrderedBlock247
variable {Name : Type} [DecidableEq Name]

def mapping : List (Entry Name) → Name → CompTerm Name
 | [], name => .var name
 | entry :: rest, name => ⟨(mapping rest name).ty.subst (substitution [entry]),.var name⟩

theorem singleton_eval (model : Model) (assignment : Name → Comp model) (entry : Entry Name) :
 (fun name => (substitution [entry] name).eval model assignment) =
 put model assignment entry.1 (entry.2.eval model assignment) := by
 funext name
 by_cases same : entry.1 = name
 · subst name
   simp [substitution,lookup,put,CompTerm.eval,RowTerm.eval]
 · simp [substitution,lookup,put,same,Ne.symm same,CompTerm.eval,TyTerm.eval,RowTerm.eval]

theorem mapping_eval (entries : List (Entry Name)) (model : Model)
 (assignment : Name → Comp model) (name : Name) :
 (mapping entries name).eval model assignment = solve model entries assignment name := by
 induction entries generalizing assignment with
 | nil => rfl
 | cons entry rest ih =>
   apply Prod.ext
   · change ((mapping rest name).ty.subst (substitution [entry])).eval model assignment =
       (solve model rest (put model assignment entry.1 (entry.2.eval model assignment)) name).1
     rw [TyTerm.eval_subst,singleton_eval]
     exact congrArg Prod.fst (ih (put model assignment entry.1 (entry.2.eval model assignment)))
   · exact (solve_rows model (entry::rest) assignment name).symm

theorem row_fixed (entries : List (Entry Name)) (row : RowTerm Name) : row.subst (mapping entries) = row := by
 induction row with
 | var name => cases entries <;> rfl
 | empty => rfl
 | join first last one two => simp only [RowTerm.subst,one,two]

def rewrite (entries : List (Entry Name)) (atoms : List (Atom Name)) : List (Atom Name) :=
 atoms.map (atomSubst (mapping entries))

theorem rewrite_exact (entries : List (Entry Name)) (atoms : List (Atom Name))
 (model : Model) (assignment : Name → Comp model) :
 All model assignment (rewrite entries atoms) ↔ All model (solve model entries assignment) atoms := by
 have same : (fun name => (mapping entries name).eval model assignment) = solve model entries assignment :=
   funext (mapping_eval entries model assignment)
 simp only [rewrite,All,List.forall_mem_map,atom_exact,same]

theorem alias_chain : (mapping ([(2,.var 0),(3,.union (.var 2) (.var 1))] : List (Entry Nat)) 3).ty =
 .union (.var 0) (.var 1) := rfl

theorem alias_row_unchanged : (mapping ([(2,.var 0),(3,.union (.var 2) (.var 1))] : List (Entry Nat)) 3).row = .var 3 := rfl
end Yulang.GeneralPresenceOrderedSubstitution247
