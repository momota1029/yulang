import Yulang.CommonNominalFieldTemplates
import Yulang.CommonNominalClosedBlock

/-!
# Independent equations for every original full field template

Whole parameters and guarded internal references keep their original depth.
The equation interpreter has no closure, inference or solver in its
definition. Actual template regular closure satisfies these equations and
recovers every original internal-node model simultaneously.
-/

namespace Yulang.CommonNominalTemplateEquations

open CommonNominalCarrier
open CommonNominalFieldTemplates (Body Template TemplateRow reference)

def chosen (values : Fin nodes → Ty) (arguments : Fin types → Ty) : Fin nodes ⊕ Fin types → Ty :=
  Sum.elim values arguments

def evaluate (arguments : Fin types → Ty) (rows : Fin rowCount → Row) (values : Fin nodes → Ty) :
    Body nodes types rowCount → Ty
  | .parameter index => arguments index
  | .base scalar => .base scalar
  | .float => .float
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (evaluate arguments rows values first) (evaluate arguments rows values last)
  | .inter first last => .inter (evaluate arguments rows values first) (evaluate arguments rows values last)
  | .pair first last => pair (chosen values arguments first) (chosen values arguments last)
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty
  | .record label payload tail => record label (chosen values arguments payload) (evaluate arguments rows values tail)
  | .recordDefault label source fallback => recordDefault label (evaluate arguments rows values source) (chosen values arguments fallback)
  | .variant label payload => variant label (chosen values arguments payload)
  | .arrow input incoming output outgoing => arrow (chosen values arguments input) (incoming.eval rows)
      (chosen values arguments output) (outgoing.eval rows)
  | .mask hidden source => mask hidden (evaluate arguments rows values source)
  | .nominal name args => nominal name (args.map (Sum.map (chosen values arguments) (TemplateRow.eval rows)))

@[simp] theorem chosen_reference (values : Fin nodes → Ty) (arguments : Fin types → Ty)
    (original : Fin nodes ⊕ Fin types) :
    CommonNominalClosedBlock.valueReference values (reference arguments original) =
      CommonNominalSyntax.State.node (chosen values arguments original) := by
  cases original <;> rfl

/-- Literal agreement with the original template body, including inlined
whole parameters. No added payload guard or lost original occurrence. -/
theorem body_instantiate_map (arguments : Fin types → Ty) (rows : Fin rowCount → Row) (values : Fin nodes → Ty)
    (body : Body nodes types rowCount) :
    (body.instantiate arguments rows).map (CommonNominalClosedBlock.valueReference values) =
      evaluate arguments rows values body := by
  induction body with
  | parameter index =>
      simp only [Body.instantiate, evaluate, CommonNominalSyntax.Layer.map_comp]
      change (arguments index).map id = arguments index
      exact CommonNominalSyntax.Layer.map_id _
  | nominal name args =>
      simp only [Body.instantiate, CommonNominalSyntax.Layer.map, evaluate, nominal, List.map_map]
      congr 1
      apply List.map_congr_left
      intro argument _
      cases argument <;> simp only [Function.comp_apply, Sum.map_inl, Sum.map_inr, chosen_reference]
  | _ => simp_all [Body.instantiate, evaluate, CommonNominalSyntax.Layer.map,
      chosen_reference, pair, record, recordDefault, variant, arrow, mask]

def block (template : Template types rows) (arguments : Fin types → Ty) (rowValues : Fin rows → Row) :
    CommonNominalClosedBlock.Body template.nodes :=
  fun index => (template.body index).instantiate arguments rowValues

def instantiate (template : Template types rows) (arguments : Fin types → Ty) (rowValues : Fin rows → Row) :
    Fin template.nodes → Ty := CommonNominalClosedBlock.instantiate (block template arguments rowValues)

def Models (template : Template types rows) (arguments : Fin types → Ty) (rowValues : Fin rows → Row)
    (values : Fin template.nodes → Ty) : Prop :=
  ∀ index, Equivalent (evaluate arguments rowValues values (template.body index)) (values index)

theorem models_block_exact (template : Template types rows) (arguments : Fin types → Ty) (rowValues : Fin rows → Row)
    (values : Fin template.nodes → Ty) :
    Models template arguments rowValues values ↔ CommonNominalClosedBlock.Models (block template arguments rowValues) values := by
  simp only [Models, CommonNominalClosedBlock.Models, CommonNominalClosedBlock.equation, block, body_instantiate_map]

theorem all_parameters_models (template : Template types rows) (arguments : Fin types → Ty) (rowValues : Fin rows → Row) :
    Models template arguments rowValues (instantiate template arguments rowValues) :=
  (models_block_exact template arguments rowValues _).mpr (CommonNominalClosedBlock.all_parameter_sound _)

theorem models_exact (template : Template types rows) (arguments : Fin types → Ty) (rowValues : Fin rows → Row)
    (values : Fin template.nodes → Ty) :
    Models template arguments rowValues values ↔
      ∀ index, Equivalent (instantiate template arguments rowValues index) (values index) := by
  rw [models_block_exact]
  exact CommonNominalClosedBlock.models_exact _ values

theorem root_eval (template : Template types rows) (arguments : Fin types → Ty) (rowValues : Fin rows → Row) :
    template.eval arguments rowValues = Sum.elim (instantiate template arguments rowValues) arguments template.root := by
  cases root : template.root <;> simp only [Template.eval, root] <;> rfl

/-- All original internal nodes, all original shared parameters and their
chosen root remain part of the same independent model. -/
theorem model_root_recovery (template : Template types rows) (arguments : Fin types → Ty) (rowValues : Fin rows → Row)
    (values : Fin template.nodes → Ty) (model : Models template arguments rowValues values) :
    Equivalent (template.eval arguments rowValues) (Sum.elim values arguments template.root) := by
  rw [root_eval]
  cases template.root with
  | inl index => exact (models_exact template arguments rowValues values).mp model index
  | inr parameter => exact equivalent_refl _

end Yulang.CommonNominalTemplateEquations
