import Yulang.PresenceNormalForm

/-! Explicit constructor laws for replacing type values by mutual-subtyping
 equivalents while keeping row values equal. The bare Model signature supplies
 none of these laws. The nominal Common law producer is supplied separately in GeneralPresenceCommonLaws245;
 this interface does not assume congruence of term evaluation as a premise. -/
namespace Yulang.GeneralPresenceModelCongruence245
open Core.PresenceGeneration PresenceNormalForm

def Equiv (model : Model) (a b : model.Ty) : Prop :=
  model.subTy a b ∧ model.subTy b a

structure Laws (model : Model) : Prop where
  refl : ∀ a, model.subTy a a
  trans : ∀ a b c, model.subTy a b → model.subTy b c → model.subTy a c
  union_congr : ∀ a a' b b', Equiv model a a' → Equiv model b b' →
    Equiv model (model.union a b) (model.union a' b')
  inter_congr : ∀ a a' b b', Equiv model a a' → Equiv model b b' →
    Equiv model (model.inter a b) (model.inter a' b')
  pair_congr : ∀ a a' b b', Equiv model a a' → Equiv model b b' →
    Equiv model (model.pair a b) (model.pair a' b')
  record_congr : ∀ label a a' b b', Equiv model a a' → Equiv model b b' →
    Equiv model (model.record label a b) (model.record label a' b')
  recordDefault_congr : ∀ label a a' b b', Equiv model a a' → Equiv model b b' →
    Equiv model (model.recordDefault label a b) (model.recordDefault label a' b')
  required_congr : ∀ label a a', Equiv model a a' →
    Equiv model (model.required label a) (model.required label a')
  variant_congr : ∀ label a a', Equiv model a a' →
    Equiv model (model.variant label a) (model.variant label a')
  arrow_congr : ∀ a a' b b' incoming outgoing, Equiv model a a' → Equiv model b b' →
    Equiv model (model.arrow a incoming b outgoing) (model.arrow a' incoming b' outgoing)

def Compatible (model : Model) (first last : Name → Comp model) : Prop :=
  ∀ name, Equiv model (first name).1 (last name).1 ∧ (first name).2 = (last name).2

theorem tyEq_refl (laws : Laws model) (value : model.Ty) : Equiv model value value :=
  ⟨laws.refl value, laws.refl value⟩

theorem tyEq_symm (equal : Equiv model a b) : Equiv model b a := ⟨equal.2,equal.1⟩

theorem tyEq_trans (laws : Laws model) (first : Equiv model a b) (last : Equiv model b c) :
    Equiv model a c :=
  ⟨laws.trans _ _ _ first.1 last.1,laws.trans _ _ _ last.2 first.2⟩

theorem row_eval_equal (model : Model) (first last : Name → Comp model)
    (equal : ∀ name, (first name).2 = (last name).2) (term : RowTerm Name) :
    term.eval model first = term.eval model last := by
  induction term with
  | var name => exact equal name
  | empty => rfl
  | join a b one two => simp only [RowTerm.eval,one,two]

theorem type_eval_equiv (model : Model) (laws : Laws model)
    (first last : Name → Comp model) (equal : Compatible model first last)
    (term : TyTerm Name) : Equiv model (term.eval model first) (term.eval model last) := by
  induction term with
  | var name => exact (equal name).1
  | base value => exact tyEq_refl laws _
  | bottom => exact tyEq_refl laws _
  | top => exact tyEq_refl laws _
  | emptyRecord => exact tyEq_refl laws _
  | exactEmpty => exact tyEq_refl laws _
  | union a b one two => exact laws.union_congr _ _ _ _ one two
  | inter a b one two => exact laws.inter_congr _ _ _ _ one two
  | pair a b one two => exact laws.pair_congr _ _ _ _ one two
  | record label a b one two => exact laws.record_congr _ _ _ _ _ one two
  | recordDefault label a b one two => exact laws.recordDefault_congr _ _ _ _ _ one two
  | required label a ih => exact laws.required_congr _ _ _ ih
  | variant label a ih => exact laws.variant_congr _ _ _ ih
  | arrow a incoming b outgoing one two =>
    have inEq := row_eval_equal model first last (fun name => (equal name).2) incoming
    have outEq := row_eval_equal model first last (fun name => (equal name).2) outgoing
    simp only [TyTerm.eval,inEq,outEq]
    exact laws.arrow_congr _ _ _ _ _ _ one two

theorem subTy_iff (laws : Laws model) (left : Equiv model a a') (right : Equiv model b b') :
    model.subTy a b ↔ model.subTy a' b' := by
  constructor
  · intro held
    exact laws.trans _ _ _ left.2 (laws.trans _ _ _ held right.1)
  · intro held
    exact laws.trans _ _ _ left.1 (laws.trans _ _ _ held right.2)

theorem atom_holds_iff (model : Model) (laws : Laws model)
    (first last : Name → Comp model) (equal : Compatible model first last)
    (atom : Atom Name) : atom.Holds model first ↔ atom.Holds model last := by
  cases atom with
  | tyLe a b =>
    exact subTy_iff laws
      (type_eval_equiv model laws first last equal a)
      (type_eval_equiv model laws first last equal b)
  | rowLe a b =>
    simp only [Atom.Holds,row_eval_equal model first last (fun name => (equal name).2)]

theorem all_iff {model : Model} (laws : Laws model)
    {first last : Name → Comp model} (equal : Compatible model first last)
    (atoms : List (Atom Name)) : All model first atoms ↔ All model last atoms := by
  constructor
  · intro valid atom member
    exact (atom_holds_iff model laws first last equal atom).mp (valid atom member)
  · intro valid atom member
    exact (atom_holds_iff model laws first last equal atom).mpr (valid atom member)

end Yulang.GeneralPresenceModelCongruence245
