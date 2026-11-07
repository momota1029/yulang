import Yulang.CommonNominalTemplateEquations
import Yulang.CommonNominalClampedGraphFamily
import Yulang.CommonNominalDefault
import Yulang.CommonNominalOuterLabels

/-!
# Full original field templates as finite shared equation pools

Every template node and every shared type-argument slot receives a distinct
fixed ID. Whole parameters are same-depth references; original payloads keep
their guards. A finite mask inventory is computed from the original body,
without inspecting any chosen type argument or row. Rows remain unchanged.

This is exact model-preserving graph lowering, not full bound saturation.
-/

namespace Yulang.CommonNominalTemplateLowering

open CommonNominalCarrier
open CommonNominalFieldTemplates (Body Template TemplateRow)
open CommonNominalTemplateEquations (chosen)

def index : Fin nodes ⊕ Fin types → Fin (nodes + types) :=
  Sum.elim (Fin.castAdd types) (Fin.natAdd nodes)

def values (internal : Fin nodes → Ty) (arguments : Fin types → Ty) : Fin (nodes + types) → Ty :=
  Fin.addCases internal arguments

@[simp] theorem value_parameter (internal : Fin nodes → Ty) (arguments : Fin types → Ty) (parameter : Fin types) :
    values internal arguments (Fin.natAdd nodes parameter) = arguments parameter := by simp [values]

@[simp] theorem value_internal (internal : Fin nodes → Ty) (arguments : Fin types → Ty) (original : Fin nodes) :
    values internal arguments (Fin.castAdd types original) = internal original := by simp [values]

private theorem equivalent_of_eq {first last : Ty} (same : first = last) : Equivalent first last := by
  subst last
  exact equivalent_refl _

@[simp] theorem value_index (internal : Fin nodes → Ty) (arguments : Fin types → Ty) (original : Fin nodes ⊕ Fin types) :
    values internal arguments (index original) = chosen internal arguments original := by
  cases original <;> simp [values, index, chosen]

def maskLabels : Body nodes types rows → List Nat
  | .union first last | .inter first last => maskLabels first ++ maskLabels last
  | .record _ _ tail => maskLabels tail
  | .recordDefault _ source _ => maskLabels source
  | .mask hidden source => hidden ++ maskLabels source
  | _ => []

def maskFor (labels : Nat) (hidden : List Nat) : PresenceTailElimination.Mask labels :=
  fun label => decide (label.val ∈ hidden)

theorem mask_names (hidden : List Nat) (bound : ∀ label ∈ hidden, label < labels) (label : Nat) :
    label ∈ (maskFor labels hidden).names ↔ label ∈ hidden := by
  constructor
  · intro member
    obtain ⟨original, included, rfl⟩ := List.mem_map.mp member
    have selected := (List.mem_filter.mp included).2
    simpa only [maskFor, decide_eq_true_eq] using selected
  · intro member
    let original : Fin labels := ⟨label, bound label member⟩
    exact List.mem_map.mpr ⟨original, List.mem_filter.mpr ⟨by simp, by simpa only [maskFor, decide_eq_true_eq] using member⟩, rfl⟩

abbrev LowerBody (nodes types labels rows : Nat) :=
  CommonNominalClampedGraphFamily.OpenBody (nodes + types) labels rows

def lower (labels : Nat) : Body nodes types rows → LowerBody nodes types labels rows
  | .parameter parameter => .ref (Fin.natAdd nodes parameter)
  | .base scalar => .atom (.base scalar)
  | .float => .atom .float
  | .bottom => .atom .bottom
  | .top => .atom .top
  | .union first last => .union (lower labels first) (lower labels last)
  | .inter first last => .inter (lower labels first) (lower labels last)
  | .pair first last => .atom (.pair (.inl (index first)) (.inl (index last)))
  | .emptyRecord => .atom .emptyRecord
  | .exactEmpty => .atom .exactEmpty
  | .record label payload tail => .record label (.inl (index payload)) (lower labels tail)
  | .recordDefault label source fallback => .recordDefault label (lower labels source) (.inl (index fallback))
  | .variant label payload => .atom (.variant label (.inl (index payload)))
  | .arrow input incoming output outgoing => .atom (.arrow (.inl (index input)) incoming (.inl (index output)) outgoing)
  | .mask hidden source => .mask (maskFor labels hidden) (lower labels source)
  | .nominal name args => .atom (.nominal name (args.map (Sum.map (fun original => .inl (index original)) id)))

def evaluate (rowValues : Fin rows → Row) (internal : Fin nodes → Ty) (arguments : Fin types → Ty)
    (body : LowerBody nodes types labels rows) : Ty :=
  CommonNominalClampedGraphFamily.evaluate (values internal arguments) (body.atRows rowValues)

theorem lower_eval (rowValues : Fin rows → Row) (internal : Fin nodes → Ty) (arguments : Fin types → Ty)
    (body : Body nodes types rows) (bound : ∀ label ∈ maskLabels body, label < labels) :
    Equivalent (evaluate rowValues internal arguments (lower labels body))
      (CommonNominalTemplateEquations.evaluate arguments rowValues internal body) := by
  induction body with
  | union first last ihFirst ihLast =>
      have left := ihFirst (fun label member => bound label (List.mem_append_left _ member))
      have right := ihLast (fun label member => bound label (List.mem_append_right _ member))
      exact ⟨common_union_mono left.1 right.1, common_union_mono left.2 right.2⟩
  | inter first last ihFirst ihLast =>
      have left := ihFirst (fun label member => bound label (List.mem_append_left _ member))
      have right := ihLast (fun label member => bound label (List.mem_append_right _ member))
      exact ⟨common_inter_mono left.1 right.1, common_inter_mono left.2 right.2⟩
  | record label payload tail ih =>
      have same := ih bound
      simpa [Equivalent, evaluate, lower, CommonNominalClampedGraphFamily.evaluate, CommonNominalOpenTailSolver.Body.atRows,
        CommonNominalPresenceTailLayers.Body.quote, CommonNominalPresenceTailElimination.Body.eval,
        CommonNominalPresenceTailRegular.payload, CommonNominalTemplateEquations.evaluate] using
        And.intro (common_record_mono label (subtype_refl (chosen internal arguments payload)) same.1)
          (common_record_mono label (subtype_refl (chosen internal arguments payload)) same.2)
  | recordDefault label source fallback ih =>
      have same := ih bound
      simpa [evaluate, lower, CommonNominalClampedGraphFamily.evaluate, CommonNominalOpenTailSolver.Body.atRows,
        CommonNominalPresenceTailLayers.Body.quote, CommonNominalPresenceTailElimination.Body.eval,
        CommonNominalPresenceTailRegular.payload, CommonNominalTemplateEquations.evaluate] using
        common_default_congr label same (equivalent_refl (chosen internal arguments fallback))
  | mask hidden source ih =>
      have same := ih (fun label member => bound label (List.mem_append_right _ member))
      have namesSame := common_mask_congr (maskFor labels hidden).names hidden
        (mask_names hidden (fun label member => bound label (List.mem_append_left _ member)))
        (CommonNominalTemplateEquations.evaluate arguments rowValues internal source)
      exact equivalent_trans (common_mask_type_congr _ same) namesSame
  | nominal name args =>
      have literal : evaluate rowValues internal arguments (lower labels (.nominal name args)) =
          CommonNominalTemplateEquations.evaluate arguments rowValues internal (.nominal name args) := by
        simp only [evaluate, lower, CommonNominalClampedGraphFamily.evaluate, CommonNominalOpenTailSolver.Body.atRows,
          CommonNominalPresenceTailLayers.Body.quote, CommonNominalPresenceTailElimination.Body.eval,
          CommonNominalPresenceTailLayers.quoteLayer, CommonNominalFieldTemplates.rowsLayer,
          CommonNominalSyntax.Layer.map, CommonNominalTemplateEquations.evaluate, nominal, List.map_map]
        congr 1
        apply List.map_congr_left
        intro argument _
        cases argument <;> simp [CommonNominalPresenceTailRegular.payload, value_index]
      rw [literal]
      exact equivalent_refl _
  | _ =>
      apply equivalent_of_eq
      simp [evaluate, lower, CommonNominalClampedGraphFamily.evaluate, CommonNominalOpenTailSolver.Body.atRows,
        CommonNominalPresenceTailLayers.Body.quote, CommonNominalPresenceTailElimination.Body.eval,
        CommonNominalPresenceTailLayers.quoteLayer, CommonNominalFieldTemplates.rowsLayer,
        CommonNominalSyntax.Layer.map, CommonNominalPresenceTailRegular.payload,
        CommonNominalTemplateEquations.evaluate, pair, arrow, variant]

def support (template : Template types rows) : List Nat :=
  (List.finRange template.nodes).flatMap fun index => maskLabels (template.body index)

def labelCount (template : Template types rows) : Nat := CommonNominalOuterLabels.fresh (support template)

theorem body_bound (template : Template types rows) (original : Fin template.nodes) :
    ∀ label ∈ maskLabels (template.body original), label < labelCount template := by
  intro label member
  exact CommonNominalOuterLabels.member_lt_fresh (support template) label
    (List.mem_flatMap.mpr ⟨original, by simp, member⟩)

def pool (template : Template types rows) :
    CommonNominalClampedGraphFamily.Pool (template.nodes + types) (labelCount template) rows :=
  ⟨Fin.addCases (fun original => some (lower (labelCount template) (template.body original))) (fun _ => none)⟩

theorem pool_models_exact (template : Template types rows) (rowValues : Fin rows → Row)
    (internal : Fin template.nodes → Ty) (arguments : Fin types → Ty) :
    CommonNominalClampedGraphFamily.Realizes (pool template) rowValues (values internal arguments) ↔
      CommonNominalTemplateEquations.Models template arguments rowValues internal := by
  constructor
  · intro model original
    have equation := model (Fin.castAdd types original)
    change Equivalent (CommonNominalClampedGraphFamily.evaluate (values internal arguments)
      (CommonNominalClampedGraphFamily.originalGraph (pool template) rowValues (Fin.castAdd types original)))
      (values internal arguments (Fin.castAdd types original)) at equation
    simp only [CommonNominalClampedGraphFamily.originalGraph, pool, Fin.addCases_left, value_internal] at equation
    exact equivalent_trans (equivalent_symm (lower_eval rowValues internal arguments (template.body original)
      (body_bound template original))) equation
  · intro model original
    refine Fin.addCases ?_ ?_ original
    · intro original
      change Equivalent (CommonNominalClampedGraphFamily.evaluate (values internal arguments)
        (CommonNominalClampedGraphFamily.originalGraph (pool template) rowValues (Fin.castAdd types original)))
        (values internal arguments (Fin.castAdd types original))
      simp only [CommonNominalClampedGraphFamily.originalGraph, pool, Fin.addCases_left, value_internal]
      exact equivalent_trans (lower_eval rowValues internal arguments (template.body original)
        (body_bound template original)) (model original)
    · intro parameter
      change Equivalent (CommonNominalClampedGraphFamily.evaluate (values internal arguments)
        (CommonNominalClampedGraphFamily.originalGraph (pool template) rowValues (Fin.natAdd template.nodes parameter)))
        (values internal arguments (Fin.natAdd template.nodes parameter))
      simpa only [CommonNominalClampedGraphFamily.originalGraph, pool, Fin.addCases_right,
        CommonNominalClampedGraphFamily.evaluate, CommonNominalPresenceTailLayers.Body.quote,
        CommonNominalPresenceTailElimination.Body.eval] using equivalent_refl (values internal arguments _)

theorem all_arguments_pool_models (template : Template types rows) (rowValues : Fin rows → Row)
    (arguments : Fin types → Ty) :
    CommonNominalClampedGraphFamily.Realizes (pool template) rowValues
      (values (CommonNominalTemplateEquations.instantiate template arguments rowValues) arguments) :=
  (pool_models_exact template rowValues _ arguments).mpr
    (CommonNominalTemplateEquations.all_parameters_models template arguments rowValues)

theorem merged_eta (original : Fin (nodes + types) → Ty) :
    values (fun node => original (Fin.castAdd types node)) (fun parameter => original (Fin.natAdd nodes parameter)) = original := by
  funext node
  refine Fin.addCases ?_ ?_ node <;> intro _ <;> simp [values]

/-- Every actual full-pool model retains the original root's value, all
internal nodes and exactly the same original shared argument slots. -/
theorem pool_model_root_recovery (template : Template types rows) (rowValues : Fin rows → Row)
    (original : Fin (template.nodes + types) → Ty)
    (model : CommonNominalClampedGraphFamily.Realizes (pool template) rowValues original) :
    Equivalent (template.eval (fun parameter => original (Fin.natAdd template.nodes parameter)) rowValues)
      (original (index template.root)) := by
  let internal : Fin template.nodes → Ty := fun node => original (Fin.castAdd types node)
  let arguments : Fin types → Ty := fun parameter => original (Fin.natAdd template.nodes parameter)
  have same : values internal arguments = original := merged_eta original
  have mergedModel : CommonNominalClampedGraphFamily.Realizes (pool template) rowValues (values internal arguments) := by
    rw [same]
    exact model
  have root := CommonNominalTemplateEquations.model_root_recovery template arguments rowValues internal
    ((pool_models_exact template rowValues internal arguments).mp mergedModel)
  change Equivalent (template.eval arguments rowValues) (chosen internal arguments template.root) at root
  rw [← value_index, same] at root
  exact root

end Yulang.CommonNominalTemplateLowering
