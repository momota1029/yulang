import Yulang.CommonNominalClampedGraphFamily

/-!
# Disjoint finite allocation without losing original mixed pool models

Renaming acts on both guarded payloads and same-depth references. External
states, fixed labels, masks and symbolic row identities are unchanged.
Merging keeps both original node inventories and has exactly the product of
their independent equation models. Explicit shared aliases can subsequently
be added as ordinary bidirectional edges.
-/

namespace Yulang.CommonNominalPoolMerge

open CommonNominalCarrier
open CommonNominalClampedGraphFamily (Pool OpenBody evaluate Realizes)
open CommonNominalPresenceTailRegular (Payload)
open CommonNominalFieldTemplates (rowsLayer)
open CommonNominalTypeFlow (Edge)

def rename (injection : Fin source → Fin target) : OpenBody source labels rows → OpenBody target labels rows
  | .atom layer => .atom (layer.map (Sum.map injection id))
  | .ref index => .ref (injection index)
  | .union first last => .union (rename injection first) (rename injection last)
  | .inter first last => .inter (rename injection first) (rename injection last)
  | .mask hidden source => .mask hidden (rename injection source)
  | .record label payload tail => .record label (Sum.map injection id payload) (rename injection tail)
  | .recordDefault label source fallback =>
      .recordDefault label (rename injection source) (Sum.map injection id fallback)

theorem rows_layer_map (rowValues : Fin rows → Row) (function : α → β)
    (layer : CommonNominalSyntax.Layer (CommonNominalFieldTemplates.TemplateRow rows) α) :
    rowsLayer rowValues (layer.map function) = (rowsLayer rowValues layer).map function := by
  induction layer <;> simp_all [rowsLayer, CommonNominalSyntax.Layer.map, List.map_map]

theorem payload_map (injection : Fin source → Fin target) (values : Fin target → Ty) (reference : Payload source) :
    CommonNominalPresenceTailRegular.payload values (Sum.map injection id reference) =
      CommonNominalPresenceTailRegular.payload (values ∘ injection) reference := by
  cases reference <;> rfl

/-- Literal commutation at the full regular carrier, not just a finite
observation or a canonical source assignment. Injection is not required for
the local substitution law; disjoint allocation supplies it below. -/
theorem rename_evaluate (injection : Fin source → Fin target) (rowValues : Fin rows → Row)
    (values : Fin target → Ty) (body : OpenBody source labels rows) :
    evaluate values ((rename injection body).atRows rowValues) =
      evaluate (values ∘ injection) (body.atRows rowValues) := by
  induction body with
  | atom layer =>
      simp only [rename, CommonNominalOpenTailSolver.Body.atRows, evaluate,
        CommonNominalPresenceTailLayers.Body.quote, CommonNominalPresenceTailElimination.Body.eval,
        rows_layer_map, CommonNominalPresenceTailLayers.quoteLayer_map]
      congr 1
      funext reference
      exact payload_map injection values reference
  | ref => rfl
  | union first last ihFirst ihLast | inter first last ihFirst ihLast =>
      simp_all [rename, CommonNominalOpenTailSolver.Body.atRows, evaluate,
        CommonNominalPresenceTailLayers.Body.quote, CommonNominalPresenceTailElimination.Body.eval]
  | mask hidden source ih =>
      simpa only [rename, CommonNominalOpenTailSolver.Body.atRows, evaluate,
        CommonNominalPresenceTailLayers.Body.quote, CommonNominalPresenceTailElimination.Body.eval] using
        congrArg (mask hidden.names) ih
  | record label payload tail ih =>
      simpa only [rename, CommonNominalOpenTailSolver.Body.atRows, evaluate,
        CommonNominalPresenceTailLayers.Body.quote, CommonNominalPresenceTailElimination.Body.eval, payload_map] using
        congrArg (record label (CommonNominalPresenceTailRegular.payload (values ∘ injection) payload)) ih
  | recordDefault label source fallback ih =>
      simpa only [rename, CommonNominalOpenTailSolver.Body.atRows, evaluate,
        CommonNominalPresenceTailLayers.Body.quote, CommonNominalPresenceTailElimination.Body.eval, payload_map] using
        congrArg (fun source => recordDefault label source
          (CommonNominalPresenceTailRegular.payload (values ∘ injection) fallback)) ih

theorem realizes_defined_exact (pool : Pool nodes labels rows) (rowValues : Fin rows → Row) (values : Fin nodes → Ty) :
    Realizes pool rowValues values ↔ ∀ index body, pool.definition index = some body →
      Equivalent (evaluate values (body.atRows rowValues)) (values index) := by
  constructor
  · intro model index body found
    have equation := model index
    simpa only [CommonNominalClampedGraphFamily.originalGraph, found, evaluate] using equation
  · intro model index
    cases found : pool.definition index with
    | none =>
        simpa only [CommonNominalClampedGraphFamily.originalGraph, found,
          CommonNominalPresenceTailLayers.Body.quote, CommonNominalPresenceTailElimination.Body.eval] using
          equivalent_refl (values index)
    | some body => simpa only [CommonNominalClampedGraphFamily.originalGraph, found, evaluate] using model index body found

def merge (first : Pool before labels rows) (last : Pool after labels rows) : Pool (before + after) labels rows :=
  ⟨Fin.addCases
    (fun index => (first.definition index).map (rename (Fin.castAdd after)))
    (fun index => (last.definition index).map (rename (Fin.natAdd before)))⟩

def mergedValues (first : Fin before → Ty) (last : Fin after → Ty) : Fin (before + after) → Ty := Fin.addCases first last

@[simp] theorem merged_left (first : Fin before → Ty) (last : Fin after → Ty) :
    mergedValues first last ∘ Fin.castAdd after = first := by funext index; simp [mergedValues]

@[simp] theorem merged_right (first : Fin before → Ty) (last : Fin after → Ty) :
    mergedValues first last ∘ Fin.natAdd before = last := by funext index; simp [mergedValues]

theorem realizes_merge (first : Pool before labels rows) (last : Pool after labels rows) (rowValues : Fin rows → Row)
    (firstValues : Fin before → Ty) (lastValues : Fin after → Ty) :
    Realizes (merge first last) rowValues (mergedValues firstValues lastValues) ↔
      Realizes first rowValues firstValues ∧ Realizes last rowValues lastValues := by
  simp only [realizes_defined_exact]
  constructor
  · intro model
    constructor
    · intro index body found
      have actual := model (Fin.castAdd after index) (rename (Fin.castAdd after) body)
        (by simp [merge, found])
      simpa [rename_evaluate, mergedValues] using actual
    · intro index body found
      have actual := model (Fin.natAdd before index) (rename (Fin.natAdd before) body)
        (by simp [merge, found])
      simpa [rename_evaluate, mergedValues] using actual
  · rintro ⟨firstModel, lastModel⟩ index
    refine Fin.addCases ?_ ?_ index
    · intro index body found
      cases original : first.definition index with
      | none => simp [merge, original] at found
      | some originalBody =>
          have equal : body = rename (Fin.castAdd after) originalBody := by simpa [merge, original] using found.symm
          subst body
          simpa [rename_evaluate, mergedValues] using firstModel index originalBody original
    · intro index body found
      cases original : last.definition index with
      | none => simp [merge, original] at found
      | some originalBody =>
          have equal : body = rename (Fin.natAdd before) originalBody := by simpa [merge, original] using found.symm
          subst body
          simpa [rename_evaluate, mergedValues] using lastModel index originalBody original

def renameEdges (injection : Fin source → Fin target) (edges : List (Edge source)) : List (Edge target) :=
  edges.map (Prod.map injection injection)

theorem renamed_edges_exact (injection : Fin source → Fin target) (edges : List (Edge source)) (values : Fin target → Ty) :
    CommonNominalTypeFlow.Models (renameEdges injection edges) values ↔
      CommonNominalTypeFlow.Models edges (values ∘ injection) := by
  simp only [CommonNominalTypeFlow.Models, renameEdges, List.forall_mem_map]
  rfl

end Yulang.CommonNominalPoolMerge
