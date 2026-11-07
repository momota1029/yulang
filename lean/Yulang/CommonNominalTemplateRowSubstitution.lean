import Yulang.CommonNominalOrdinaryTemplates
import Yulang.CommonNominalTemplateLowering

/-!
# Original symbolic row arguments in one ambient field-template context

Finite row substitution retains literal signed heads, joins and every shared
ambient slot. It changes no internal node, type-argument position, root,
constructor identity or guard. Actual source RowTerm arguments are lowered
without choosing or checking a concrete row assignment.
-/

namespace Yulang.CommonNominalTemplateRowSubstitution

open CommonNominalCarrier
open CommonNominalFieldTemplates (Body Template TemplateRow)
open Core.PresenceGeneration (Comp RowTerm)

def row (replacement : Fin before → TemplateRow after) : TemplateRow before → TemplateRow after
  | .var index => replacement index
  | .empty => .empty
  | .heads original => .heads original
  | .join first last => .join (row replacement first) (row replacement last)

theorem row_eval (replacement : Fin before → TemplateRow after) (rows : Fin after → Row) (original : TemplateRow before) :
    (row replacement original).eval rows = original.eval (fun index => (replacement index).eval rows) := by
  induction original <;> simp_all [row, TemplateRow.eval]

def body (replacement : Fin before → TemplateRow after) : Body nodes types before → Body nodes types after
  | .parameter index => .parameter index
  | .base scalar => .base scalar
  | .float => .float
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (body replacement first) (body replacement last)
  | .inter first last => .inter (body replacement first) (body replacement last)
  | .pair first last => .pair first last
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty
  | .record label payload tail => .record label payload (body replacement tail)
  | .recordDefault label source fallback => .recordDefault label (body replacement source) fallback
  | .variant label payload => .variant label payload
  | .arrow input incoming output outgoing => .arrow input (row replacement incoming) output (row replacement outgoing)
  | .mask hidden source => .mask hidden (body replacement source)
  | .nominal name args => .nominal name (args.map (Sum.map id (row replacement)))

/-- Literal, full-depth preservation for arbitrary type arguments and rows. -/
theorem body_instantiate (replacement : Fin before → TemplateRow after) (arguments : Fin types → Ty)
    (rows : Fin after → Row) (original : Body nodes types before) :
    (body replacement original).instantiate arguments rows =
      original.instantiate arguments (fun index => (replacement index).eval rows) := by
  induction original with
  | nominal name args =>
      simp only [body, Body.instantiate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro argument _
      cases argument <;> simp [row_eval]
  | _ => simp_all [body, Body.instantiate, row_eval]

def template (original : Template types before) (replacement : Fin before → TemplateRow after) : Template types after :=
  ⟨original.nodes, fun index => body replacement (original.body index), original.root⟩

theorem template_eval (original : Template types before) (replacement : Fin before → TemplateRow after)
    (arguments : Fin types → Ty) (rows : Fin after → Row) :
    (template original replacement).eval arguments rows =
      original.eval arguments (fun index => (replacement index).eval rows) := by
  cases found : original.root with
  | inr parameter => simp only [template, Template.eval, found]
  | inl index =>
      simp only [template, Template.eval, found]
      congr 3
      funext index
      exact body_instantiate replacement arguments rows (original.body index)

theorem mask_labels_unchanged (replacement : Fin before → TemplateRow after) (original : Body nodes types before) :
    CommonNominalTemplateLowering.maskLabels (body replacement original) = CommonNominalTemplateLowering.maskLabels original := by
  induction original <;> simp_all [body, CommonNominalTemplateLowering.maskLabels]

theorem body_evaluate (replacement : Fin before → TemplateRow after) (arguments : Fin types → Ty)
    (rows : Fin after → Row) (values : Fin nodes → Ty) (original : Body nodes types before) :
    CommonNominalTemplateEquations.evaluate arguments rows values (body replacement original) =
      CommonNominalTemplateEquations.evaluate arguments (fun index => (replacement index).eval rows) values original := by
  have first := CommonNominalTemplateEquations.body_instantiate_map arguments rows values (body replacement original)
  have last := CommonNominalTemplateEquations.body_instantiate_map arguments
    (fun index => (replacement index).eval rows) values original
  rw [body_instantiate] at first
  exact first.symm.trans last

theorem models_exact (original : Template types before) (replacement : Fin before → TemplateRow after)
    (arguments : Fin types → Ty) (rows : Fin after → Row) (values : Fin original.nodes → Ty) :
    CommonNominalTemplateEquations.Models (template original replacement) arguments rows values ↔
      CommonNominalTemplateEquations.Models original arguments (fun index => (replacement index).eval rows) values := by
  simp only [CommonNominalTemplateEquations.Models, template, body_evaluate]

/-- The real source row arguments share precisely their original ambient
row IDs. The equality holds for every original computation assignment. -/
theorem actual_row_arguments (original : Template types rows) (rowArguments : Fin rows → RowTerm (Fin inputs))
    (assignment : Fin inputs → Comp model) (arguments : Fin types → Ty) :
    (template original (fun index => CommonNominalOrdinaryTemplates.row (rowArguments index))).eval arguments
        (fun index => (assignment index).2) =
      original.eval arguments (fun index => (rowArguments index).eval model assignment) := by
  refine (template_eval original (fun index => CommonNominalOrdinaryTemplates.row (rowArguments index))
    arguments (fun index => (assignment index).2)).trans ?_
  congr 1
  funext index
  exact CommonNominalOrdinaryTemplates.row_eval assignment (rowArguments index)

end Yulang.CommonNominalTemplateRowSubstitution
