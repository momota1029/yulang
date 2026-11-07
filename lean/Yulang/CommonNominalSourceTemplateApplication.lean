import Yulang.CommonNominalTemplateArgumentSubstitution
import Yulang.CommonNominalTemplateRowSubstitution

/-!
# Full actual field-term applications in one ambient template graph

Both type and row arguments are the actual source generator's finite terms.
The compiler computes their shared collector and substitutes rows over the
same original ambient slots. Exact models retain all original outer nodes,
all argument subterms and all original type/row arguments.

Every packed ordinary/full-template term now has an actual finite template
graph whose every model recovers its original meaning. Bound constraints and
runtime casts remain separate obligations.
-/

namespace Yulang.CommonNominalSourceTemplateApplication

open CommonNominalCarrier
open Core.PresenceGeneration (Comp TyTerm RowTerm)
open CommonNominalFieldTemplates (Template Term)
open CommonNominalTemplateEquations (Models chosen)
open CommonNominalTemplateArgumentSubstitution (argumentPool OrdinaryModels provided)

def rowReplacement (rowArguments : Fin rows → RowTerm (Fin inputs)) :=
  fun index => CommonNominalOrdinaryTemplates.row (rowArguments index)

def withRows (original : Template types rows) (rowArguments : Fin rows → RowTerm (Fin inputs)) : Template types inputs :=
  CommonNominalTemplateRowSubstitution.template original (rowReplacement rowArguments)

def compile (original : Template types rows) (typeArguments : Fin types → TyTerm (Fin inputs))
    (rowArguments : Fin rows → RowTerm (Fin inputs)) : Template inputs inputs :=
  CommonNominalTemplateArgumentSubstitution.template (withRows original rowArguments) typeArguments

theorem models_exact (original : Template types rows) (typeArguments : Fin types → TyTerm (Fin inputs))
    (rowArguments : Fin rows → RowTerm (Fin inputs)) (assignment : Fin inputs → Comp model)
    (originalValues : Fin original.nodes → Ty) (argumentValues : Fin (argumentPool typeArguments).size → Ty) :
    Models (compile original typeArguments rowArguments)
      (fun index => (assignment index).1) (fun index => (assignment index).2)
      (CommonNominalTemplateAllocation.mergedValues originalValues argumentValues) ↔
        OrdinaryModels (argumentPool typeArguments) assignment argumentValues ∧
        Models original (fun parameter => (typeArguments parameter).eval model assignment)
          (fun parameter => (rowArguments parameter).eval model assignment) originalValues := by
  let ambientRows : Fin inputs → Row := fun index => (assignment index).2
  let originalRows : Fin rows → Row := fun index => (rowArguments index).eval model assignment
  have rowsSame : (fun index => (rowReplacement rowArguments index).eval ambientRows) = originalRows :=
    funext fun index => CommonNominalOrdinaryTemplates.row_eval assignment (rowArguments index)
  apply (CommonNominalTemplateArgumentSubstitution.models_exact (withRows original rowArguments)
    typeArguments assignment originalValues argumentValues).trans
  constructor
  · rintro ⟨ordinaryModel, substituted⟩
    have source := (CommonNominalTemplateRowSubstitution.models_exact original (rowReplacement rowArguments)
      (provided typeArguments argumentValues) ambientRows originalValues).mp substituted
    rw [rowsSame] at source
    have parametersSame := CommonNominalTemplateArgumentSubstitution.provided_actual typeArguments assignment argumentValues ordinaryModel
    exact ⟨ordinaryModel, (CommonNominalTemplateCongruence.models_congr original originalRows originalValues originalValues
      _ _ (fun _ => equivalent_refl _) parametersSame).mp source⟩
  · rintro ⟨ordinaryModel, source⟩
    have parametersSame := CommonNominalTemplateArgumentSubstitution.provided_actual typeArguments assignment argumentValues ordinaryModel
    have substituted := (CommonNominalTemplateCongruence.models_congr original originalRows originalValues originalValues
      _ _ (fun _ => equivalent_refl _) parametersSame).mpr source
    rw [← rowsSame] at substituted
    exact ⟨ordinaryModel, (CommonNominalTemplateRowSubstitution.models_exact original (rowReplacement rowArguments)
      (provided typeArguments argumentValues) ambientRows originalValues).mpr substituted⟩

/-- All arbitrary original outer models extend while retaining all their
original node values and literal rows; argument nodes are actually generated. -/
theorem extend_source_model (original : Template types rows) (typeArguments : Fin types → TyTerm (Fin inputs))
    (rowArguments : Fin rows → RowTerm (Fin inputs)) (assignment : Fin inputs → Comp model)
    (originalValues : Fin original.nodes → Ty)
    (sourceModel : Models original (fun parameter => (typeArguments parameter).eval model assignment)
      (fun parameter => (rowArguments parameter).eval model assignment) originalValues) :
    Models (compile original typeArguments rowArguments)
      (fun index => (assignment index).1) (fun index => (assignment index).2)
      (CommonNominalTemplateAllocation.mergedValues originalValues
        (CommonNominalOrdinaryTemplates.canonical (argumentPool typeArguments) assignment)) :=
  (models_exact original typeArguments rowArguments assignment originalValues _).mpr
    ⟨CommonNominalTemplateArgumentSubstitution.canonical_ordinary_models _ assignment, sourceModel⟩

theorem model_source_root_recovery (original : Template types rows) (typeArguments : Fin types → TyTerm (Fin inputs))
    (rowArguments : Fin rows → RowTerm (Fin inputs)) (assignment : Fin inputs → Comp model)
    (originalValues : Fin original.nodes → Ty) (argumentValues : Fin (argumentPool typeArguments).size → Ty)
    (combined : Models (compile original typeArguments rowArguments)
      (fun index => (assignment index).1) (fun index => (assignment index).2)
      (CommonNominalTemplateAllocation.mergedValues originalValues argumentValues)) :
    Equivalent ((Term.template original typeArguments rowArguments).eval assignment)
      (chosen (CommonNominalTemplateAllocation.mergedValues originalValues argumentValues)
        (fun index => (assignment index).1) (compile original typeArguments rowArguments).root) := by
  have recovered := CommonNominalTemplateArgumentSubstitution.model_source_root_recovery
    (withRows original rowArguments) typeArguments assignment originalValues argumentValues combined
  have literal := CommonNominalTemplateRowSubstitution.actual_row_arguments original rowArguments assignment
    (fun parameter => (typeArguments parameter).eval model assignment)
  exact Eq.mp (congrArg (fun type => Equivalent type
    (chosen (CommonNominalTemplateAllocation.mergedValues originalValues argumentValues)
      (fun index => (assignment index).1) (compile original typeArguments rowArguments).root)) literal) recovered

theorem compile_eval (original : Template types rows) (typeArguments : Fin types → TyTerm (Fin inputs))
    (rowArguments : Fin rows → RowTerm (Fin inputs)) (assignment : Fin inputs → Comp model) :
    Equivalent ((compile original typeArguments rowArguments).eval
      (fun index => (assignment index).1) (fun index => (assignment index).2))
      ((Term.template original typeArguments rowArguments).eval assignment) := by
  let originalValues := CommonNominalTemplateEquations.instantiate original
    (fun parameter => (typeArguments parameter).eval model assignment)
    (fun parameter => (rowArguments parameter).eval model assignment)
  let argumentValues := CommonNominalOrdinaryTemplates.canonical (argumentPool typeArguments) assignment
  have combined := extend_source_model original typeArguments rowArguments assignment originalValues
    (CommonNominalTemplateEquations.all_parameters_models _ _ _)
  have first := CommonNominalTemplateEquations.model_root_recovery (compile original typeArguments rowArguments)
    (fun index => (assignment index).1) (fun index => (assignment index).2)
    (CommonNominalTemplateAllocation.mergedValues originalValues argumentValues) combined
  have last := model_source_root_recovery original typeArguments rowArguments assignment originalValues argumentValues combined
  exact equivalent_trans first (equivalent_symm last)

def term : Term (Fin inputs) → Template inputs inputs
  | .ordinary original => CommonNominalOrdinaryTemplates.template
      (PresenceOpenTailGenerationLowering.collect [original]) original
      (PresenceOpenTailGenerationLowering.collect_covers [original] original (by simp))
  | .template original types rows => compile original types rows

theorem term_eval (original : Term (Fin inputs)) (assignment : Fin inputs → Comp model) :
    Equivalent ((term original).eval (fun index => (assignment index).1) (fun index => (assignment index).2))
      (original.eval assignment) := by
  cases original with
  | ordinary original => exact CommonNominalOrdinaryTemplates.template_eval _ assignment original _
  | template original types rows => exact compile_eval original types rows assignment

/-- Every model of the actual compiled term graph recovers its original
full source term at the same root; the node assignment is unrestricted. -/
theorem term_model_root_recovery (original : Term (Fin inputs)) (assignment : Fin inputs → Comp model)
    (values : Fin (term original).nodes → Ty)
    (model : Models (term original) (fun index => (assignment index).1) (fun index => (assignment index).2) values) :
    Equivalent (original.eval assignment) (chosen values (fun index => (assignment index).1) (term original).root) :=
  equivalent_trans (equivalent_symm (term_eval original assignment))
    (CommonNominalTemplateEquations.model_root_recovery _ _ _ values model)

end Yulang.CommonNominalSourceTemplateApplication
