import Yulang.CommonPatternConstraintGrammar

/-! The extended pattern endpoint grammar survives actual finite formula
normalization and binder packing. This is syntax provenance only. -/

namespace Yulang.CommonPatternFormulaGrammar

open Core.PresenceGeneration
open PresenceNormalForm
open CommonPatternBoundInspection (Upper)
open PresenceGeneratedChildGrammar (lower)
open CommonPatternConstraintGrammar (GoodAtoms)

theorem Upper.rename {type : TyTerm α} (good : Upper type) (rename : α → β) :
    Upper (type.rename rename) := by
  cases good with
  | old good => exact .old (by simpa using good)
  | variant good => exact .variant (by simpa using good)
  | optional good => exact .optional (by simpa using good)

def GoodFormula : Formula α → Prop
  | .top | .bot | .rowLe _ _ => True
  | .and first last | .or first last => GoodFormula first ∧ GoodFormula last
  | .tyLe first last => lower first = true ∧ Upper last
  | .existsSlot formula => GoodFormula formula

theorem of_old {formula : Formula α} (good : PresenceGeneratedChildGrammar.GoodFormula formula) :
    GoodFormula formula := by
  induction formula with
  | top | bot | rowLe => trivial
  | and first last ihf ihl | or first last ihf ihl => exact ⟨ihf good.1, ihl good.2⟩
  | tyLe first last => exact ⟨good.1, .old good.2⟩
  | existsSlot formula ih => exact ih good

theorem GoodAtoms.rename {atoms : List (Atom α)} (good : GoodAtoms atoms) (rename : α → β) :
    GoodAtoms (atoms.map (Atom.rename rename)) := by
  intro first last member
  obtain ⟨atom, included, same⟩ := List.mem_map.mp member
  cases atom with
  | rowLe => cases same
  | tyLe source target =>
      cases same
      have original := good source target included
      exact ⟨by simpa using original.1, Upper.rename original.2 rename⟩

theorem GoodAtoms.append {first last : List (Atom α)} (left : GoodAtoms first) (right : GoodAtoms last) :
    GoodAtoms (first ++ last) := by
  intro source target member
  exact (List.mem_append.mp member).elim (left source target) (right source target)

theorem GoodAtoms.combine {first last : Clause α}
    (left : GoodAtoms first.atoms) (right : GoodAtoms last.atoms) : GoodAtoms (first.combine last).atoms :=
  GoodAtoms.append (GoodAtoms.rename left (leftName first.locals last.locals))
    (GoodAtoms.rename right (rightName first.locals last.locals))

theorem GoodAtoms.close {clause : Clause (Option α)} (good : GoodAtoms clause.atoms) :
    GoodAtoms clause.close.atoms := GoodAtoms.rename good (closeName clause.locals)

theorem good_singleton (atom : Atom α)
    (good : match atom with
      | .tyLe first last => lower first = true ∧ Upper last
      | .rowLe _ _ => True) : GoodAtoms (Clause.singleton atom).atoms := by
  apply GoodAtoms.rename (atoms := [atom]) (rename := Sum.inr)
  intro first last member
  have same := List.mem_singleton.mp member
  subst atom
  exact good

theorem good_normalise {formula : Formula α} (good : GoodFormula formula)
    (clause : Clause α) (member : clause ∈ normalise formula) : GoodAtoms clause.atoms := by
  induction formula with
  | top =>
      have same := List.mem_singleton.mp member
      subst clause
      intro source target absent
      cases absent
  | bot => cases member
  | tyLe | rowLe =>
      have same := List.mem_singleton.mp member
      subst clause
      exact good_singleton _ good
  | and first last ihf ihl =>
      obtain ⟨left, included, member⟩ := List.mem_flatMap.mp member
      obtain ⟨right, present, rfl⟩ := List.mem_map.mp member
      exact GoodAtoms.combine (ihf good.1 left included) (ihl good.2 right present)
  | or first last ihf ihl =>
      exact (List.mem_append.mp member).elim (ihf good.1 clause) (ihl good.2 clause)
  | existsSlot formula ih =>
      obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
      exact GoodAtoms.close (ih good original present)

theorem good_pack {clause : Clause (Option Empty)} (good : GoodAtoms clause.atoms) :
    GoodAtoms clause.pack := GoodAtoms.rename good (resultName clause.locals)

end Yulang.CommonPatternFormulaGrammar
