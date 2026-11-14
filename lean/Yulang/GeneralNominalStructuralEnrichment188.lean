import Yulang.GeneralNominalMixedOriginEnrichment188
import Yulang.GeneralNominalInspectionTransport188

/-! A completed structural point head enriches its actual child projections.
Immediate queries may mix variables, scalars and arbitrary nominal subtrees.
No point restriction is imposed beneath a nominal boundary. -/
namespace Yulang.GeneralNominalStructuralEnrichment188
open GeneralNominalRecursiveInspection GeneralNominalOriginAlias181
open GeneralNominalStructuralOrigin188 GeneralNominalReportTransport188
open GeneralNominalPointOriginEnrichment188 GeneralNominalMixedOriginEnrichment188
open GeneralNominalInspection (Bounds Query)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

 theorem structural_enrichment (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (slot : Fin state.base.slots)
    (kind : Fin state.view.kinds)
    (children : Fin (state.view.shapes kind).arity → Fin state.base.slots)
    (recorded : state.view.heads slot = .structural kind children)
    (patterns : List Query) (supported : ∀ query ∈ patterns, Supported query)
    (finished : Finished (inspect state (.node (state.view.shapes kind) patterns) (slot,slot) none))
    (raw : ProjectionModels state (inspect state (.node (state.view.shapes kind) patterns) (slot,slot) none) model)
    (compatible : GeneralNominalAllocation.Compatible
      (bindings state (inspect state (.node (state.view.shapes kind) patterns) (slot,slot) none)) model) :
    ProjectionModels state (inspect state (.node (state.view.shapes kind) patterns) (slot,slot)
      (some (.source (state.base.source slot)))) model := by
  let bounds : List (Bounds state) := List.ofFn fun index => (children index,children index)
  let origins : Nat → Option Origin := fun index =>
    if h : index < (state.view.shapes kind).arity then
      some (.source (state.base.source (children ⟨index,h⟩)))
    else some (.structural (.source (state.base.source slot)) (state.view.shapes kind) index)
  have zipped : (List.ofFn children).zip (List.ofFn children) = bounds :=
    GeneralNominalInspectionPositions.zip_reindex rfl rfl children children
  have bodyFinished : Finished (inspectMany state patterns bounds (fun _ => none) 0) := by
    simpa only [inspect,recorded,and_self,↓reduceIte,zipped,Option.map_none,
      GeneralNominalInspectionAlignment.finished_visit] using finished
  have body : ProjectionModels state (inspectMany state patterns bounds (fun _ => none) 0) model := by
    simpa only [inspect,recorded,and_self,↓reduceIte,zipped,Option.map_none,projection_visit_none] using raw
  have cross : GeneralNominalAllocation.Compatible (bindings state (inspectMany state patterns bounds (fun _ => none) 0)) model := by
    simpa only [inspect,recorded,and_self,↓reduceIte,zipped,Option.map_none,bindings,Report.visit] using compatible
  have points : ∀ index interval, bounds[index]? = some interval →
      interval.1 = interval.2 ∧ origins (0+index) = some (.source (state.base.source interval.1)) := by
    intro index interval found
    simp only [bounds,List.getElem?_ofFn] at found
    split at found
    · rename_i bounded
      cases Option.some.inj found
      exact ⟨rfl,by simp only [origins,Nat.zero_add,bounded,↓reduceDIte]⟩
    · cases found
  have sourceProjection := mixed_many state model valid patterns supported bounds origins 0 points bodyFinished body cross
  have related : ∀ index, Optional model
      (some (.structural (.source (state.base.source slot)) (state.view.shapes kind) index)) (origins index) := by
    intro index
    unfold origins
    split
    · rename_i bounded
      exact .some (same_similar (structural_slot_same state model valid slot kind children recorded ⟨index,bounded⟩))
    · exact .some (similar_refl _ _)
  have projected := GeneralNominalReportTransport188.projection state _ _
    (GeneralNominalInspectionTransport188.many_related state patterns bounds _ origins 0 related) sourceProjection
  simp only [inspect,recorded,and_self,↓reduceIte,zipped,Option.map_some]
  apply projection_visit state _ _ _ _ model projected
  · exact ⟨⟨_,.source _⟩,by intro actual seen; cases seen; exact ⟨subtype_refl _,subtype_refl _⟩⟩
  · intro actual seen
    cases seen
    refine ⟨List.ofFn (fun index => (model (state.base.source (children index))).1),List.length_ofFn,?_⟩
    exact GeneralNominalFiniteBracket.structural_slot state model valid slot kind children recorded rfl

 theorem structural_point (state : GeneralNominalState.State) (model : Assignment)
    (valid : GeneralNominalState.Models state model) (slot : Fin state.base.slots)
    (shape : GeneralNormalizedObservation.Shape) (patterns : List Query)
    (supported : ∀ query ∈ patterns, Supported query)
    (finished : Finished (inspect state (.node shape patterns) (slot,slot) none))
    (raw : ProjectionModels state (inspect state (.node shape patterns) (slot,slot) none) model)
    (compatible : GeneralNominalAllocation.Compatible
      (bindings state (inspect state (.node shape patterns) (slot,slot) none)) model) :
    ProjectionModels state (inspect state (.node shape patterns) (slot,slot)
      (some (.source (state.base.source slot)))) model := by
  cases head : state.view.heads slot with
  | scalar base => simp [inspect,head,Finished,Report.visit] at finished
  | deferred reason => simp [inspect,head,Finished,Report.visit,block] at finished
  | structural kind children =>
    by_cases same : state.view.shapes kind = shape
    · subst shape
      exact structural_enrichment state model valid slot kind children head patterns supported finished raw compatible
    · simp [inspect,head,same,Finished,Report.visit,block] at finished

end Yulang.GeneralNominalStructuralEnrichment188
