import Yulang.GeneralRebaseRowIrrelevance273

namespace Yulang.GeneralRebaseTypeOnlyAtoms273
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open Core.PresenceGeneration (TyTerm Comp)
open PresenceNormalForm (Atom All)

def typeOnly : TyTerm α → Bool
 | .arrow .. => false
 | .pair a b | .union a b | .inter a b | .record _ a b | .recordDefault _ a b =>
   typeOnly a && typeOnly b
 | .required _ a | .variant _ a => typeOnly a
 | _ => true

def atomTypeOnly : Atom α → Bool
 | .rowLe .. => false
 | .tyLe a b => typeOnly a && typeOnly b

theorem term_eq {first last : α → Comp model} (same : ∀ id, (first id).1 = (last id).1)
 (t : TyTerm α) (good : typeOnly t = true) :
 t.eval model first = t.eval model last := by
 induction t with
 | var n => exact same n
 | arrow => cases good
 | base | bottom | top | emptyRecord | exactEmpty => rfl
 | required label t ih | variant label t ih =>
   simp only [Core.PresenceGeneration.TyTerm.eval,ih good]
 | pair a b ihA ihB | union a b ihA ihB | inter a b ihA ihB
 | record label a b ihA ihB | recordDefault label a b ihA ihB =>
   obtain ⟨one,two⟩ := Bool.and_eq_true_iff.mp good
   simp only [Core.PresenceGeneration.TyTerm.eval,ihA one,ihB two]

theorem atom_iff {first last : α → Comp model} (same : ∀ id, (first id).1 = (last id).1)
 (a : Atom α) (good : atomTypeOnly a = true) :
 a.Holds model first ↔ a.Holds model last := by
 cases a with
 | rowLe => cases good
 | tyLe a b =>
   obtain ⟨x,y⟩ := Bool.and_eq_true_iff.mp good
   simp only [Atom.Holds,term_eq same a x,term_eq same b y]

theorem all_iff {first last : α → Comp model} (same : ∀ id, (first id).1 = (last id).1)
 (atoms : List (Atom α)) (good : atoms.all atomTypeOnly = true) :
 All model first atoms ↔ All model last atoms :=
 forall_congr' fun a => forall_congr' fun member => atom_iff same a (List.all_eq_true.mp good a member)

end Yulang.GeneralRebaseTypeOnlyAtoms273
