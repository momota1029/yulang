import Yulang.CommonNominalTemplateLowering

/-!
# Congruence of full field templates, including whole parameters

Equivalent values may replace every shared argument at every original
occurrence, including positive same-depth sources, contravariant arrow
inputs and invariant nominal arguments. The computed mask support depends
only on the original body. No covariance or finite old-carrier restriction
is assumed for payloads.
-/

namespace Yulang.CommonNominalTemplateCongruence

open CommonNominalCarrier
open CommonNominalFieldTemplates (Body Template)
open CommonNominalTemplateLowering (LowerBody lower values)

theorem merged_congr (firstValues lastValues : Fin nodes → Ty) (firstArguments lastArguments : Fin types → Ty)
    (internal : ∀ index, Equivalent (firstValues index) (lastValues index))
    (arguments : ∀ index, Equivalent (firstArguments index) (lastArguments index)) :
    ∀ index, Equivalent (values firstValues firstArguments index) (values lastValues lastArguments index) := by
  intro index
  refine Fin.addCases ?_ ?_ index
  · intro original
    simpa only [CommonNominalTemplateLowering.value_internal] using internal original
  · intro parameter
    simpa only [CommonNominalTemplateLowering.value_parameter] using arguments parameter

theorem lowered_evaluate_congr (rowValues : Fin rows → Row) (body : LowerBody nodes types labels rows)
    (firstValues lastValues : Fin nodes → Ty) (firstArguments lastArguments : Fin types → Ty)
    (internal : ∀ index, Equivalent (firstValues index) (lastValues index))
    (arguments : ∀ index, Equivalent (firstArguments index) (lastArguments index)) :
    Equivalent (CommonNominalTemplateLowering.evaluate rowValues firstValues firstArguments body)
      (CommonNominalTemplateLowering.evaluate rowValues lastValues lastArguments body) := by
  have same := merged_congr firstValues lastValues firstArguments lastArguments internal arguments
  apply CommonNominalPresenceTailRegular.Body.quote_eval_congr
  · intro reference
    cases reference with
    | inl index => exact same index
    | inr state => exact equivalent_refl _
  · exact same

theorem body_evaluate_congr (rowValues : Fin rows → Row) (body : Body nodes types rows)
    (firstValues lastValues : Fin nodes → Ty) (firstArguments lastArguments : Fin types → Ty)
    (internal : ∀ index, Equivalent (firstValues index) (lastValues index))
    (arguments : ∀ index, Equivalent (firstArguments index) (lastArguments index)) :
    Equivalent (CommonNominalTemplateEquations.evaluate firstArguments rowValues firstValues body)
      (CommonNominalTemplateEquations.evaluate lastArguments rowValues lastValues body) := by
  let labels := CommonNominalOuterLabels.fresh (CommonNominalTemplateLowering.maskLabels body)
  have bound : ∀ label ∈ CommonNominalTemplateLowering.maskLabels body, label < labels :=
    CommonNominalOuterLabels.member_lt_fresh _
  exact equivalent_trans
    (equivalent_symm (CommonNominalTemplateLowering.lower_eval rowValues firstValues firstArguments body bound))
    (equivalent_trans (lowered_evaluate_congr rowValues (lower labels body)
      firstValues lastValues firstArguments lastArguments internal arguments)
      (CommonNominalTemplateLowering.lower_eval rowValues lastValues lastArguments body bound))

theorem models_congr (template : Template types rows) (rowValues : Fin rows → Row)
    (firstValues lastValues : Fin template.nodes → Ty) (firstArguments lastArguments : Fin types → Ty)
    (internal : ∀ index, Equivalent (firstValues index) (lastValues index))
    (arguments : ∀ index, Equivalent (firstArguments index) (lastArguments index)) :
    CommonNominalTemplateEquations.Models template firstArguments rowValues firstValues ↔
      CommonNominalTemplateEquations.Models template lastArguments rowValues lastValues := by
  have equations (index : Fin template.nodes) := body_evaluate_congr rowValues (template.body index)
    firstValues lastValues firstArguments lastArguments internal arguments
  constructor
  · intro model index
    exact equivalent_trans (equivalent_symm (equations index))
      (equivalent_trans (model index) (internal index))
  · intro model index
    exact equivalent_trans (equations index) (equivalent_trans (model index) (equivalent_symm (internal index)))

theorem all_nodes_congr (template : Template types rows) (rowValues : Fin rows → Row)
    (first last : Fin types → Ty) (same : ∀ index, Equivalent (first index) (last index)) :
    ∀ index, Equivalent (CommonNominalTemplateEquations.instantiate template first rowValues index)
      (CommonNominalTemplateEquations.instantiate template last rowValues index) := by
  have moved := (models_congr template rowValues _ _ first last (fun _ => equivalent_refl _) same).mp
    (CommonNominalTemplateEquations.all_parameters_models template first rowValues)
  have recovered := (CommonNominalTemplateEquations.models_exact template last rowValues _).mp moved
  exact fun index => equivalent_symm (recovered index)

/-- Every shared argument remains interchangeable at every original field
occurrence. Rows are unchanged literally; no kind or arity is dropped. -/
theorem template_eval_congr (template : Template types rows) (rowValues : Fin rows → Row)
    (first last : Fin types → Ty) (same : ∀ index, Equivalent (first index) (last index)) :
    Equivalent (template.eval first rowValues) (template.eval last rowValues) := by
  rw [CommonNominalTemplateEquations.root_eval, CommonNominalTemplateEquations.root_eval]
  cases template.root with
  | inl index => exact all_nodes_congr template rowValues first last same index
  | inr parameter => exact same parameter

end Yulang.CommonNominalTemplateCongruence
