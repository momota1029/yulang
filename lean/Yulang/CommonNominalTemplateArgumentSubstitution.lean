import Yulang.CommonNominalTemplateAllocation
import Yulang.CommonNominalTemplateCongruence
import Yulang.CommonNominalOrdinaryTemplates

/-!
# Actual type arguments in a shared full-template graph

The original finite TyTerm collector allocates every argument subterm. Whole
argument occurrences inline their original finite body, while guarded
occurrences point to the very same collected root. Internal template nodes
and argument nodes receive disjoint IDs. All ambient parameters stay shared.

This module proves the local substitution law and independent component
model recovery. It does not solve generated bound inequalities.
-/

namespace Yulang.CommonNominalTemplateArgumentSubstitution

open CommonNominalCarrier
open Core.PresenceGeneration (Comp TyTerm)
open CommonNominalFieldTemplates (Body Template)
open CommonNominalTemplateEquations (chosen evaluate)
open PresenceOpenTailGenerationLowering (Pool collect collect_covers)

def argumentPool (arguments : Fin types → TyTerm (Fin inputs)) : Pool inputs := collect (List.ofFn arguments)

theorem argument_mem (arguments : Fin types → TyTerm (Fin inputs)) (parameter : Fin types) :
    arguments parameter ∈ (argumentPool arguments).terms :=
  collect_covers (List.ofFn arguments) _ (List.mem_ofFn.mpr ⟨parameter, rfl⟩)

def root (arguments : Fin types → TyTerm (Fin inputs)) (parameter : Fin types) : Fin (argumentPool arguments).size :=
  (argumentPool arguments).reference (arguments parameter) (argument_mem arguments parameter)

def provided (arguments : Fin types → TyTerm (Fin inputs)) (values : Fin (argumentPool arguments).size → Ty) : Fin types → Ty :=
  fun parameter => values (root arguments parameter)

def reference (nodes : Nat) (arguments : Fin types → TyTerm (Fin inputs)) :
    Fin nodes ⊕ Fin types → Fin (nodes + (argumentPool arguments).size) ⊕ Fin inputs
  | .inl original => .inl (Fin.castAdd (argumentPool arguments).size original)
  | .inr parameter => .inl (Fin.natAdd nodes (root arguments parameter))

def body (arguments : Fin types → TyTerm (Fin inputs)) :
    Body nodes types inputs → Body (nodes + (argumentPool arguments).size) inputs inputs
  | .parameter parameter => CommonNominalTemplateAllocation.rename (Fin.natAdd nodes)
      (CommonNominalOrdinaryTemplates.body (argumentPool arguments) (arguments parameter) (argument_mem arguments parameter))
  | .base scalar => .base scalar
  | .float => .float
  | .bottom => .bottom
  | .top => .top
  | .union first last => .union (body arguments first) (body arguments last)
  | .inter first last => .inter (body arguments first) (body arguments last)
  | .pair first last => .pair (reference nodes arguments first) (reference nodes arguments last)
  | .emptyRecord => .emptyRecord
  | .exactEmpty => .exactEmpty
  | .record label payload tail => .record label (reference nodes arguments payload) (body arguments tail)
  | .recordDefault label source fallback => .recordDefault label (body arguments source) (reference nodes arguments fallback)
  | .variant label payload => .variant label (reference nodes arguments payload)
  | .arrow input incoming output outgoing => .arrow (reference nodes arguments input) incoming (reference nodes arguments output) outgoing
  | .mask hidden source => .mask hidden (body arguments source)
  | .nominal name args => .nominal name (args.map (Sum.map (reference nodes arguments) id))

def OrdinaryModels (pool : Pool inputs) (assignment : Fin inputs → Comp model) (values : Fin pool.size → Ty) : Prop :=
  ∀ index, Equivalent
    (evaluate (fun index => (assignment index).1) (fun index => (assignment index).2) values
      (CommonNominalOrdinaryTemplates.body pool (pool.termAt index) (pool.at_mem index))) (values index)

theorem ordinary_values_exact (pool : Pool inputs) (assignment : Fin inputs → Comp model) (values : Fin pool.size → Ty) :
    OrdinaryModels pool assignment values ↔
      ∀ index, Equivalent (values index) ((pool.termAt index).eval model assignment) := by
  constructor
  · intro model index
    have original := (CommonNominalOrdinaryTemplates.all_nodes_exact pool assignment
      (pool.termAt index) (pool.at_mem index) values).mp model
    exact original index
  · intro same index
    have model := (CommonNominalOrdinaryTemplates.all_nodes_exact pool assignment
      (pool.termAt index) (pool.at_mem index) values).mpr same
    exact model index

theorem canonical_ordinary_models (pool : Pool inputs) (assignment : Fin inputs → Comp model) :
    OrdinaryModels pool assignment (CommonNominalOrdinaryTemplates.canonical pool assignment) := by
  intro index
  rw [CommonNominalOrdinaryTemplates.body_evaluate]
  exact equivalent_refl _

@[simp] theorem reference_value (arguments : Fin types → TyTerm (Fin inputs))
    (originalValues : Fin nodes → Ty) (argumentValues : Fin (argumentPool arguments).size → Ty)
    (ambient : Fin inputs → Ty) (original : Fin nodes ⊕ Fin types) :
    chosen (CommonNominalTemplateAllocation.mergedValues originalValues argumentValues) ambient
      (reference nodes arguments original) = chosen originalValues (provided arguments argumentValues) original := by
  cases original <;> simp [reference, chosen, CommonNominalTemplateAllocation.mergedValues, provided]

private theorem equivalent_of_eq {first last : Ty} (same : first = last) : Equivalent first last := by
  subst last
  exact equivalent_refl _

/-- Every original argument occurrence uses the same collected root. The
only premise is the independent original argument-body equation model. -/
theorem body_evaluate (arguments : Fin types → TyTerm (Fin inputs)) (assignment : Fin inputs → Comp model)
    (originalValues : Fin nodes → Ty) (argumentValues : Fin (argumentPool arguments).size → Ty)
    (argumentModel : OrdinaryModels (argumentPool arguments) assignment argumentValues) (original : Body nodes types inputs) :
    Equivalent
      (evaluate (fun index => (assignment index).1) (fun index => (assignment index).2)
        (CommonNominalTemplateAllocation.mergedValues originalValues argumentValues) (body arguments original))
      (evaluate (provided arguments argumentValues) (fun index => (assignment index).2) originalValues original) := by
  let ambient : Fin inputs → Ty := fun index => (assignment index).1
  let rows : Fin inputs → Row := fun index => (assignment index).2
  change Equivalent (evaluate ambient rows (CommonNominalTemplateAllocation.mergedValues originalValues argumentValues)
    (body arguments original)) (evaluate (provided arguments argumentValues) rows originalValues original)
  induction original with
  | parameter parameter =>
      have equation := argumentModel (root arguments parameter)
      simp only [body, CommonNominalTemplateAllocation.evaluate_rename, CommonNominalTemplateAllocation.merged_right,
        evaluate]
      simpa only [root, Pool.termAt_reference] using equation
  | union first last ihFirst ihLast =>
      exact ⟨common_union_mono ihFirst.1 ihLast.1, common_union_mono ihFirst.2 ihLast.2⟩
  | inter first last ihFirst ihLast =>
      exact ⟨common_inter_mono ihFirst.1 ihLast.1, common_inter_mono ihFirst.2 ihLast.2⟩
  | record label payload tail ih =>
      simpa only [body, evaluate, reference_value, Equivalent] using
        And.intro (common_record_mono label (subtype_refl (chosen originalValues (provided arguments argumentValues) payload)) ih.1)
          (common_record_mono label (subtype_refl (chosen originalValues (provided arguments argumentValues) payload)) ih.2)
  | recordDefault label source fallback ih =>
      simpa only [body, evaluate, reference_value] using
        common_default_congr label ih (equivalent_refl (chosen originalValues (provided arguments argumentValues) fallback))
  | mask hidden source ih => exact common_mask_type_congr hidden ih
  | nominal name args =>
      have literal : evaluate ambient rows
          (CommonNominalTemplateAllocation.mergedValues originalValues argumentValues) (body arguments (.nominal name args)) =
          evaluate (provided arguments argumentValues) rows originalValues (.nominal name args) := by
        simp only [body, evaluate, nominal, List.map_map]
        congr 1
        apply List.map_congr_left
        intro argument _
        cases argument <;> simp [reference_value]
      rw [literal]
      exact equivalent_refl _
  | _ =>
      apply equivalent_of_eq
      simp only [body, evaluate, reference_value]

end Yulang.CommonNominalTemplateArgumentSubstitution
