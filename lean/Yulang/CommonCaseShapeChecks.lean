import Yulang.CommonCaseBaseCells

/-! Executable domain membership and transport along complete structural
cells. This is used to retain all requirements when record declarations
mention the same label more than once. No duplicate-label policy is added. -/

namespace Yulang.CommonCaseShapeChecks

open CaseValues
open CommonCaseBaseCells (Shape InShape ValueEquivalent)

def check : Shape → Value Empty → Bool
  | .base kind, .literal value => decide (Core.CommonData.literalBase value = kind)
  | .pair first last, .pair left right => check first left && check last right
  | .variant tag payload, .variant actual value => decide (tag = actual) && check payload value
  | .choice first last, value => check first value || check last value
  | _, _ => false

theorem check_exact (shape : Shape) (value : Value Empty) : check shape value = true ↔ InShape shape value := by
  induction shape generalizing value with
  | base kind =>
      cases value <;> simp only [check, decide_eq_true_eq, Bool.false_eq_true]
      all_goals try exact ⟨False.elim, fun typed => by cases typed⟩
      exact ⟨InShape.base, fun typed => by cases typed; assumption⟩
  | pair first last ihf ihl =>
      cases value <;> simp only [check, Bool.and_eq_true, Bool.false_eq_true]
      all_goals try exact ⟨False.elim, fun typed => by cases typed⟩
      constructor
      · rintro ⟨left, right⟩; exact .pair (ihf _ |>.mp left) (ihl _ |>.mp right)
      · intro typed; cases typed with | pair left right => exact ⟨(ihf _).mpr left, (ihl _).mpr right⟩
  | variant tag payload ih =>
      cases value <;> simp only [check, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true]
      all_goals try exact ⟨False.elim, fun typed => by cases typed⟩
      constructor
      · rintro ⟨rfl, child⟩; exact .variant ((ih _).mp child)
      · intro typed; cases typed with | variant child => exact ⟨rfl, (ih _).mpr child⟩
  | choice first last ihf ihl =>
      simp only [check, Bool.or_eq_true, ihf, ihl]
      constructor
      · rintro (left | right)
        · exact .left left
        · exact .right right
      · intro typed
        cases typed with
        | left child => exact Or.inl child
        | right child => exact Or.inr child

theorem equivalent_symm (same : ValueEquivalent bounds texts first last) : ValueEquivalent bounds texts last first := by
  induction same with
  | literal scalar =>
      cases scalar with
      | integer comparisons => exact .literal (.integer (fun bound member =>
          ⟨(comparisons bound member).1.symm, (comparisons bound member).2.symm⟩))
      | string comparisons => exact .literal (.string (fun text member => (comparisons text member).symm))
      | boolean => exact .literal .boolean
      | unit => exact .literal .unit
  | pair left right ihl ihr => exact .pair ihl ihr
  | variant child ih => exact .variant ih

theorem shape_preserved (typed : InShape shape first) (same : ValueEquivalent bounds texts first last) : InShape shape last := by
  induction typed generalizing last with
  | base kind =>
      cases same with
      | literal scalar => exact .base ((CommonCaseLiteralCoverage.equivalent_base_eq scalar).symm.trans kind)
  | pair left right ihl ihr =>
      cases same with | pair first last => exact .pair (ihl first) (ihr last)
  | variant child ih =>
      cases same with | variant childSame => exact .variant (ih childSame)
  | left child ih => exact .left (ih same)
  | right child ih => exact .right (ih same)

theorem shape_iff (same : ValueEquivalent bounds texts first last) : InShape shape first ↔ InShape shape last :=
  ⟨fun typed => shape_preserved typed same, fun typed => shape_preserved typed (equivalent_symm same)⟩

end Yulang.CommonCaseShapeChecks
