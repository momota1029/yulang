import Yulang.GeneralDictionaryInspectionHeads215
import Yulang.GeneralNominalCenteredHeadMatHeadParts

/-! Root inversion for closed normalized counted patterns does not assume
constructor coverage or old finite-Expr representability. Undefined applications
remain bottom and cannot lie above a concrete observable constructor. -/
namespace Yulang.GeneralDictionaryCountedRoot216
open CommonNominalFullCarrier GeneralDeclarationPatterns GeneralPatternNormalForm
open GeneralNominalCenteredHeadMatPatternSemantics
open GeneralNominalCenteredHeadMatCompilerSemantics (algebra application)
open GeneralDictionaryInspectionHeads215
open GeneralNominalRecursiveInspection

inductive RootForm (pattern : Pattern) (value : Ty) : Prop
  | bottom : Equivalent value .bottom → RootForm pattern value
  | scalar (base : Inference.Base) : Equivalent value (.base base) → RootForm pattern value
  | nominal (name : Nat) (arguments : List Argument) : Equivalent value (nominal name arguments) → RootForm pattern value
  | structural (shape : GeneralNormalizedObservation.Shape) (values : List Ty) :
      shape.Canonical → values.length = shape.arity → Equivalent value (shapeValue shape values) → RootForm pattern value
  | record (label : Nat) (payload tail : Ty) : (∃ label a b, pattern = .record label a b) → Equivalent value (record label payload tail) → RootForm pattern value

theorem root_form (pattern : Pattern) (normal : Normal pattern) :
    RootForm pattern (eval (algebra constructors interpretation) (fun _ => .bottom) pattern) := by
  cases pattern with
  | var => exact .bottom (eqv_refl _)
  | join => simp only [Normal] at normal
  | record label payload tail => exact .record label _ _ ⟨label,payload,tail,rfl⟩ (eqv_refl _)
  | variant tag payload => exact .structural (.variant tag) [_] trivial rfl (eqv_refl _)
  | app name arguments =>
      simp only [eval,algebra,application]
      split
      · rename_i primitive found
        cases primitive with
        | scalar base =>
            cases arguments with
            | nil => exact .scalar base (eqv_refl _)
            | cons => exact .bottom (eqv_refl _)
        | emptyRecord =>
            cases arguments with
            | nil => exact .structural (.record []) [] (by simp [GeneralNormalizedObservation.Shape.Canonical]) rfl (eqv_refl _)
            | cons => exact .bottom (eqv_refl _)
        | exactEmpty =>
            cases arguments with
            | nil => exact .structural .exactEmpty [] trivial rfl (eqv_refl _)
            | cons => exact .bottom (eqv_refl _)
        | pair =>
            cases arguments with
            | nil => exact .bottom (eqv_refl _)
            | cons first rest => cases rest with
              | nil => exact .bottom (eqv_refl _)
              | cons last rest => cases rest with
                | nil => exact .structural .pair [_,_] trivial rfl (eqv_refl _)
                | cons => exact .bottom (eqv_refl _)
      · split
        · rename_i declaration found
          exact .nominal declaration.name _ (eqv_refl _)
        · exact .bottom (eqv_refl _)

theorem tagged_record (label : Nat) (payload tail : Ty) : Tagged (record label payload tail) .records := by
  intro env; rfl

theorem tagged_not_bottom (known : Tagged value tag) : ¬ Subtype value .bottom := by
  intro below
  let env : CommonNominalFullDemand.Environment Row := ⟨fun _ => .bottom,fun _ => []⟩
  have held := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (below 0) 0 env (.role 0) trivial
  exact List.not_mem_nil ((known env).mp held)

theorem scalar_rigid (normal : Normal pattern)
    (below : Subtype (.base base) (eval (algebra constructors interpretation) (fun _ => .bottom) pattern)) :
    Equivalent (eval (algebra constructors interpretation) (fun _ => .bottom) pattern) (.base base) := by
  cases root_form pattern normal with
  | bottom equal => exact False.elim (tagged_not_bottom (tagged_scalar base) (subtype_trans below equal.1))
  | scalar other equal =>
      have same := tag_subtype (tagged_scalar base) (tagged_scalar other) (subtype_trans below equal.1)
      cases CommonNominalFullDemand.Head.base.inj same
      exact equal
  | nominal name args equal =>
      have bad := tag_subtype (tagged_scalar base) (tagged_nominal name args) (subtype_trans below equal.1)
      cases bad
  | structural shape values canonical length equal =>
      have bad := tag_subtype (tagged_scalar base) (tagged_shape shape values length) (subtype_trans below equal.1)
      cases shape <;> cases bad
  | record label payload tail source equal =>
      have bad := tag_subtype (tagged_scalar base) (tagged_record label payload tail) (subtype_trans below equal.1)
      cases bad

theorem nominal_rigid (normal : Normal pattern)
    (below : Subtype (nominal name arguments) (eval (algebra constructors interpretation) (fun _ => .bottom) pattern)) :
    Equivalent (eval (algebra constructors interpretation) (fun _ => .bottom) pattern) (nominal name arguments) := by
  cases root_form pattern normal with
  | bottom equal => exact False.elim (tagged_not_bottom (tagged_nominal name arguments) (subtype_trans below equal.1))
  | scalar other equal =>
      have bad := tag_subtype (tagged_nominal name arguments) (tagged_scalar other) (subtype_trans below equal.1)
      cases bad
  | nominal other args equal =>
      have compare := subtype_trans below equal.1
      exact ⟨subtype_trans equal.1 (GeneralDictionaryDefaultNominalFallback215.nominal_reverse compare),below⟩
  | structural shape values canonical length equal =>
      have bad := tag_subtype (tagged_nominal name arguments) (tagged_shape shape values length) (subtype_trans below equal.1)
      cases shape <;> cases bad
  | record label payload tail source equal =>
      have bad := tag_subtype (tagged_nominal name arguments) (tagged_record label payload tail) (subtype_trans below equal.1)
      cases bad

end Yulang.GeneralDictionaryCountedRoot216
