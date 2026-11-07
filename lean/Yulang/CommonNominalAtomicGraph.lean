import Yulang.CommonNominalSourceTemplateApplication
import Yulang.CommonNominalTemplateLowering
import Yulang.CommonNominalFieldNormalForm

/-!
# One actual finite graph for packed full field/source atoms

Every ordinary/full-template term is compiled with all of its original
nodes. Disjoint node allocation shares the same ambient type/row slots.
The result contains only a full finite template, ordinary directed subtype
edges between shared references, and finite symbolic row inequalities.

This is exact source-atom graph generation. Solving its arbitrary mixed root
bounds into unrestricted schemes is a separate obligation.
-/

namespace Yulang.CommonNominalAtomicGraph

open CommonNominalCarrier
open Core.PresenceGeneration (Comp)
open CommonNominalFieldTemplates (Template TemplateRow)
open CommonNominalFieldNormalForm (Atom All)
open CommonNominalTemplateEquations (chosen)

structure Graph (inputs : Nat) where
  template : Template inputs inputs
  edges : List ((Fin template.nodes ⊕ Fin inputs) × (Fin template.nodes ⊕ Fin inputs))
  rows : CommonNominalTemplateRowPatterns.Problem inputs

def EdgeModels (edges : List ((Fin nodes ⊕ Fin inputs) × (Fin nodes ⊕ Fin inputs)))
    (arguments : Fin inputs → Ty) (values : Fin nodes → Ty) : Prop :=
  ∀ edge ∈ edges, Subtype (chosen values arguments edge.1) (chosen values arguments edge.2)

def Graph.Models (graph : Graph inputs) (assignment : Fin inputs → Comp model) (values : Fin graph.template.nodes → Ty) : Prop :=
  CommonNominalTemplateEquations.Models graph.template (fun index => (assignment index).1) (fun index => (assignment index).2) values ∧
    EdgeModels graph.edges (fun index => (assignment index).1) values ∧
    CommonNominalTemplateRowPatterns.Models graph.rows (fun index => (assignment index).2)

def merge (first last : Graph inputs) : Graph inputs where
  template := CommonNominalTemplateAllocation.merge first.template last.template
  edges := first.edges.map (Prod.map (Sum.map (Fin.castAdd last.template.nodes) id) (Sum.map (Fin.castAdd last.template.nodes) id)) ++
    last.edges.map (Prod.map (Sum.map (Fin.natAdd first.template.nodes) id) (Sum.map (Fin.natAdd first.template.nodes) id))
  rows := first.rows ++ last.rows

theorem edges_append (first last : List ((Fin nodes ⊕ Fin inputs) × (Fin nodes ⊕ Fin inputs)))
    (arguments : Fin inputs → Ty) (values : Fin nodes → Ty) :
    EdgeModels (first ++ last) arguments values ↔ EdgeModels first arguments values ∧ EdgeModels last arguments values := by
  simp only [EdgeModels, List.forall_mem_append]

theorem edges_rename (injection : Fin before → Fin after)
    (edges : List ((Fin before ⊕ Fin inputs) × (Fin before ⊕ Fin inputs)))
    (arguments : Fin inputs → Ty) (values : Fin after → Ty) :
    EdgeModels (edges.map (Prod.map (Sum.map injection id) (Sum.map injection id))) arguments values ↔
      EdgeModels edges arguments (values ∘ injection) := by
  simp only [EdgeModels, List.forall_mem_map, Prod.map, CommonNominalTemplateAllocation.chosen_rename]

theorem models_merge (first last : Graph inputs) (assignment : Fin inputs → Comp model)
    (firstValues : Fin first.template.nodes → Ty) (lastValues : Fin last.template.nodes → Ty) :
    (merge first last).Models assignment (CommonNominalTemplateAllocation.mergedValues firstValues lastValues) ↔
      first.Models assignment firstValues ∧ last.Models assignment lastValues := by
  let arguments : Fin inputs → Ty := fun index => (assignment index).1
  let rows : Fin inputs → Row := fun index => (assignment index).2
  have templateParts := CommonNominalTemplateAllocation.models_merge first.template last.template arguments rows firstValues lastValues
  have edgeParts : EdgeModels (merge first last).edges arguments (CommonNominalTemplateAllocation.mergedValues firstValues lastValues) ↔
      EdgeModels first.edges arguments firstValues ∧ EdgeModels last.edges arguments lastValues := by
    have before := edges_rename (Fin.castAdd last.template.nodes) first.edges arguments
      (CommonNominalTemplateAllocation.mergedValues firstValues lastValues)
    have after := edges_rename (Fin.natAdd first.template.nodes) last.edges arguments
      (CommonNominalTemplateAllocation.mergedValues firstValues lastValues)
    rw [CommonNominalTemplateAllocation.merged_left] at before
    rw [CommonNominalTemplateAllocation.merged_right] at after
    exact (edges_append _ _ arguments (CommonNominalTemplateAllocation.mergedValues firstValues lastValues)).trans
      (and_congr before after)
  have rowParts : CommonNominalTemplateRowPatterns.Models (merge first last).rows rows ↔
      CommonNominalTemplateRowPatterns.Models first.rows rows ∧ CommonNominalTemplateRowPatterns.Models last.rows rows := by
    simp only [merge, CommonNominalTemplateRowPatterns.Models, List.forall_mem_append]
  constructor
  · rintro ⟨templates, edges, rowModel⟩
    exact ⟨⟨(templateParts.mp templates).1, (edgeParts.mp edges).1, (rowParts.mp rowModel).1⟩,
      ⟨(templateParts.mp templates).2, (edgeParts.mp edges).2, (rowParts.mp rowModel).2⟩⟩
  · rintro ⟨⟨firstTemplate, firstEdges, firstRows⟩, ⟨lastTemplate, lastEdges, lastRows⟩⟩
    exact ⟨templateParts.mpr ⟨firstTemplate, lastTemplate⟩, edgeParts.mpr ⟨firstEdges, lastEdges⟩,
      rowParts.mpr ⟨firstRows, lastRows⟩⟩

theorem merged_eta (values : Fin (before + after) → Ty) :
    CommonNominalTemplateAllocation.mergedValues
      (values ∘ Fin.castAdd after) (values ∘ Fin.natAdd before) = values := by
  funext index
  refine Fin.addCases ?_ ?_ index <;> intro _ <;> simp [CommonNominalTemplateAllocation.mergedValues]

theorem models_merge_all (first last : Graph inputs) (assignment : Fin inputs → Comp model)
    (values : Fin (first.template.nodes + last.template.nodes) → Ty) :
    (merge first last).Models assignment values ↔
      first.Models assignment (values ∘ Fin.castAdd last.template.nodes) ∧
        last.Models assignment (values ∘ Fin.natAdd first.template.nodes) := by
  have actual := models_merge first last assignment
    (values ∘ Fin.castAdd last.template.nodes) (values ∘ Fin.natAdd first.template.nodes)
  simpa only [merged_eta] using actual

def empty (inputs : Nat) : Graph inputs := ⟨⟨1, fun _ => .bottom, .inl 0⟩, [], []⟩

theorem empty_models (assignment : Fin inputs → Comp model) :
    ∃ values, (empty inputs).Models assignment values := by
  refine ⟨CommonNominalTemplateEquations.instantiate (empty inputs).template
    (fun index => (assignment index).1) (fun index => (assignment index).2),
    CommonNominalTemplateEquations.all_parameters_models _ _ _, ?_, ?_⟩
  · intro edge member; cases member
  · simp [empty, CommonNominalTemplateRowPatterns.Models]

def atom : Atom (Fin inputs) → Graph inputs
  | .tyLe first last =>
      let before := CommonNominalSourceTemplateApplication.term first
      let after := CommonNominalSourceTemplateApplication.term last
      let combined := CommonNominalTemplateAllocation.merge before after
      ⟨combined, [(combined.root, CommonNominalTemplateAllocation.rightRoot before after)], []⟩
  | .rowLe first last =>
      ⟨(empty inputs).template, [], [(CommonNominalOrdinaryTemplates.row first, CommonNominalOrdinaryTemplates.row last)]⟩

theorem atom_exact (original : Atom (Fin inputs)) (assignment : Fin inputs → Comp model) :
    original.Models assignment ↔ ∃ values, (atom original).Models assignment values := by
  cases original with
  | rowLe first last =>
      constructor
      · intro comparison
        obtain ⟨values, equationModel, _, _⟩ := empty_models assignment
        refine ⟨values, equationModel, (by intro edge member; cases member), ?_⟩
        intro edge member
        have same : edge = (CommonNominalOrdinaryTemplates.row first, CommonNominalOrdinaryTemplates.row last) :=
          List.mem_singleton.mp member
        subst edge
        simpa only [Atom.Models, CommonNominalOrdinaryTemplates.row_eval] using comparison
      · rintro ⟨values, _, _, rowModel⟩
        have comparison := rowModel (CommonNominalOrdinaryTemplates.row first, CommonNominalOrdinaryTemplates.row last)
          (List.mem_singleton_self _)
        simpa only [Atom.Models, CommonNominalOrdinaryTemplates.row_eval] using comparison
  | tyLe first last =>
      let before := CommonNominalSourceTemplateApplication.term first
      let after := CommonNominalSourceTemplateApplication.term last
      let arguments : Fin inputs → Ty := fun index => (assignment index).1
      let rows : Fin inputs → Row := fun index => (assignment index).2
      constructor
      · intro comparison
        let firstValues := CommonNominalTemplateEquations.instantiate before arguments rows
        let lastValues := CommonNominalTemplateEquations.instantiate after arguments rows
        have firstModel := CommonNominalTemplateEquations.all_parameters_models before arguments rows
        have lastModel := CommonNominalTemplateEquations.all_parameters_models after arguments rows
        have firstSame := CommonNominalSourceTemplateApplication.term_model_root_recovery first assignment firstValues firstModel
        have lastSame := CommonNominalSourceTemplateApplication.term_model_root_recovery last assignment lastValues lastModel
        refine ⟨CommonNominalTemplateAllocation.mergedValues firstValues lastValues,
          (CommonNominalTemplateAllocation.models_merge before after arguments rows firstValues lastValues).mpr ⟨firstModel, lastModel⟩,
          ?_, by simp [atom, CommonNominalTemplateRowPatterns.Models]⟩
        intro edge member
        have edgeSame : edge = ((CommonNominalTemplateAllocation.merge before after).root,
            CommonNominalTemplateAllocation.rightRoot before after) := List.mem_singleton.mp member
        subst edge
        change Subtype (chosen (CommonNominalTemplateAllocation.mergedValues firstValues lastValues) arguments
          (CommonNominalTemplateAllocation.merge before after).root)
          (chosen (CommonNominalTemplateAllocation.mergedValues firstValues lastValues) arguments
            (CommonNominalTemplateAllocation.rightRoot before after))
        rw [CommonNominalTemplateAllocation.chosen_left_root before after arguments firstValues lastValues,
          CommonNominalTemplateAllocation.chosen_right_root before after arguments firstValues lastValues]
        exact subtype_trans firstSame.2 (subtype_trans comparison lastSame.1)
      · rintro ⟨values, equationModel, edgeModel, _⟩
        let firstValues : Fin before.nodes → Ty := values ∘ Fin.castAdd after.nodes
        let lastValues : Fin after.nodes → Ty := values ∘ Fin.natAdd before.nodes
        have prepared : CommonNominalTemplateEquations.Models
            (CommonNominalTemplateAllocation.merge before after) arguments rows values := equationModel
        have eta : CommonNominalTemplateAllocation.mergedValues firstValues lastValues = values := merged_eta values
        have combinedModel : CommonNominalTemplateEquations.Models (CommonNominalTemplateAllocation.merge before after)
            arguments rows (CommonNominalTemplateAllocation.mergedValues firstValues lastValues) :=
          Eq.mpr (congrArg (CommonNominalTemplateEquations.Models
            (CommonNominalTemplateAllocation.merge before after) arguments rows) eta) prepared
        have actual := (CommonNominalTemplateAllocation.models_merge before after arguments rows firstValues lastValues).mp combinedModel
        have firstSame := CommonNominalSourceTemplateApplication.term_model_root_recovery first assignment firstValues actual.1
        have lastSame := CommonNominalSourceTemplateApplication.term_model_root_recovery last assignment lastValues actual.2
        have comparison := edgeModel ((CommonNominalTemplateAllocation.merge before after).root,
          CommonNominalTemplateAllocation.rightRoot before after) (List.mem_singleton_self _)
        change Subtype (chosen values arguments (CommonNominalTemplateAllocation.merge before after).root)
          (chosen values arguments (CommonNominalTemplateAllocation.rightRoot before after)) at comparison
        simp only [CommonNominalTemplateAllocation.merge, CommonNominalTemplateAllocation.rightRoot,
          ] at comparison
        have beforeRoot := CommonNominalTemplateAllocation.chosen_rename (Fin.castAdd after.nodes) values arguments before.root
        have afterRoot := CommonNominalTemplateAllocation.chosen_rename (Fin.natAdd before.nodes) values arguments after.root
        have moved := Eq.mp (congrArg2 Subtype beforeRoot afterRoot) comparison
        exact subtype_trans firstSame.1 (subtype_trans moved lastSame.2)

def compile : List (Atom (Fin inputs)) → Graph inputs
  | [] => empty inputs
  | first :: rest => merge (atom first) (compile rest)

/-- Every original packed computation assignment is kept unchanged. The
existential ranges over all nodes allocated from all actual original terms. -/
theorem compile_atoms_exact (atoms : List (Atom (Fin inputs))) (assignment : Fin inputs → Comp model) :
    All assignment atoms ↔ ∃ values, (compile atoms).Models assignment values := by
  induction atoms with
  | nil => exact ⟨fun _ => empty_models assignment, fun _ => CommonNominalFieldNormalForm.all_nil _⟩
  | cons first rest ih =>
      constructor
      · intro original
        have firstModel := (atom_exact first assignment).mp (original first (by simp))
        have restModel := ih.mp (fun atom member => original atom (List.mem_cons_of_mem _ member))
        obtain ⟨before, beforeModel⟩ := firstModel
        obtain ⟨after, afterModel⟩ := restModel
        exact ⟨CommonNominalTemplateAllocation.mergedValues before after,
          (models_merge (atom first) (compile rest) assignment before after).mpr ⟨beforeModel, afterModel⟩⟩
      · rintro ⟨values, actual⟩
        have parts := (models_merge_all (atom first) (compile rest) assignment values).mp actual
        have firstModel := (atom_exact first assignment).mpr ⟨_, parts.1⟩
        have restModel := ih.mpr ⟨_, parts.2⟩
        intro atom member
        rcases List.mem_cons.mp member with same | remaining
        · subst atom; exact firstModel
        · exact restModel atom remaining

end Yulang.CommonNominalAtomicGraph
