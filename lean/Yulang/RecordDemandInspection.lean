import Yulang.OpenRecordConstraintGraph
import Yulang.ShadowRecordDemands
import Yulang.ShadowRegularInferenceModel

/-!
# Exact inspection of open supplies against singleton record demands

The graph inspector keeps every original node. For a matching demanded
field it emits a head comparison and a tail-to-empty comparison, using
the demand's existing empty-tail node. For a different field it forwards
the whole demand to the original tail reference. No new type slot or
masked-demand node is allocated.

`none` means that this inspector does not handle the node pair; it is
not a conflict result. The total expansion leaves such edges unchanged.
For every realization, expansion preserves exactly all original subtype
constraints and output instances. This is an inspection/rewriting stage,
not saturation or construction of a free-parameter principal solution.
-/

namespace Yulang.RecordDemandInspection

open Inference OpenRecordConstraintGraph

variable {m n : Nat}

/-- The three laws used by this graph transformation. They are proved
below for the finite and regular decision-40 type models, rather than assumed
of an inference run or its unknown assignment. -/
structure Laws (model : Model) : Prop where
  empty : ∀ label value rest,
    model.subTy (model.record label value rest) model.emptyRecord ↔
      model.subTy rest model.emptyRecord
  same : ∀ label value rest expected,
    model.subTy (model.record label value rest)
        (model.record label expected model.emptyRecord) ↔
      model.subTy value expected ∧ model.subTy rest model.emptyRecord
  other : ∀ label demanded, label ≠ demanded → ∀ value rest expected,
    model.subTy (model.record label value rest)
        (model.record demanded expected model.emptyRecord) ↔
      model.subTy rest (model.record demanded expected model.emptyRecord)

/-- Only the source, target and possible demanded-tail tags are read.
Every emitted endpoint belongs to the original finite graph. -/
def inspect (nodes : Graph m n) (source target : Fin n) : Option (List (Edge n)) :=
  match nodes source, nodes target with
  | .recordExtend _ _ tail, .emptyRecord => some [(tail, target)]
  | .recordExtend label head tail, .recordExtend demanded expected remainder =>
      match nodes remainder with
      | .emptyRecord =>
          if label = demanded then some [(head, expected), (tail, remainder)]
          else some [(tail, target)]
      | _ => none
  | _, _ => none

/-- The emitted obligations are necessary and sufficient, including the
tail-shape check when the visible payload already meets the demand. -/
theorem inspect_exact (model : Model) (laws : Laws model)
    (input : Fin m → model.Ty) (rows : Fin m → model.Row)
    (nodes : Graph m n) (value : Fin n → model.Ty)
    (realizes : Realizes model input rows nodes value)
    (source target : Fin n) (requirements : List (Edge n))
    (inspected : inspect nodes source target = some requirements) :
    Satisfies model requirements value ↔ model.subTy (value source) (value target) := by
  cases sourceNode : nodes source with
  | recordExtend label head tail =>
      have sourceValue : value source = model.record label (value head) (value tail) := by
        simpa only [sourceNode, Node.eval] using realizes source
      cases targetNode : nodes target with
      | emptyRecord =>
          have targetValue : value target = model.emptyRecord := by
            simpa only [targetNode, Node.eval] using realizes target
          have same : requirements = [(tail, target)] := by
            simpa only [inspect, sourceNode, targetNode, Option.some.injEq] using inspected.symm
          subst requirements
          simpa [Satisfies, sourceValue, targetValue] using
            (laws.empty label (value head) (value tail)).symm
      | recordExtend demanded expected remainder =>
          have targetValue : value target =
              model.record demanded (value expected) (value remainder) := by
            simpa only [targetNode, Node.eval] using realizes target
          cases remainderNode : nodes remainder with
          | emptyRecord =>
              have emptyValue : value remainder = model.emptyRecord := by
                simpa only [remainderNode, Node.eval] using realizes remainder
              by_cases labels : label = demanded
              · subst demanded
                have same : requirements = [(head, expected), (tail, remainder)] := by
                  simpa [inspect, sourceNode, targetNode, remainderNode] using inspected.symm
                subst requirements
                simpa [Satisfies, sourceValue, targetValue, emptyValue] using
                  (laws.same label (value head) (value tail) (value expected)).symm
              · have same : requirements = [(tail, target)] := by
                  simpa [inspect, sourceNode, targetNode, remainderNode, labels] using inspected.symm
                subst requirements
                simpa [Satisfies, sourceValue, targetValue, emptyValue] using
                  (laws.other label demanded labels (value head) (value tail) (value expected)).symm
          | _ => simp [inspect, sourceNode, targetNode, remainderNode] at inspected
      | _ => simp [inspect, sourceNode, targetNode] at inspected
  | _ => simp [inspect, sourceNode] at inspected

/-- Unsupported pairs retain their original constraint. -/
def expandEdge (nodes : Graph m n) (edge : Edge n) : List (Edge n) :=
  (inspect nodes edge.1 edge.2).getD [edge]

def expand (nodes : Graph m n) (constraints : List (Edge n)) : List (Edge n) :=
  constraints.flatMap (expandEdge nodes)

theorem expandEdge_exact (model : Model) (laws : Laws model)
    (input : Fin m → model.Ty) (rows : Fin m → model.Row)
    (nodes : Graph m n) (value : Fin n → model.Ty)
    (realizes : Realizes model input rows nodes value) (edge : Edge n) :
    Satisfies model (expandEdge nodes edge) value ↔
      model.subTy (value edge.1) (value edge.2) := by
  cases inspected : inspect nodes edge.1 edge.2 with
  | none => simp [expandEdge, inspected, Satisfies]
  | some requirements =>
      simpa only [expandEdge, inspected, Option.getD_some] using
        inspect_exact model laws input rows nodes value realizes edge.1 edge.2 requirements inspected

/-- Expansion preserves every original assignment; no satisfiability,
solver success or choice of inferred parameters is assumed. -/
theorem expand_exact (model : Model) (laws : Laws model)
    (input : Fin m → model.Ty) (rows : Fin m → model.Row)
    (nodes : Graph m n) (value : Fin n → model.Ty)
    (realizes : Realizes model input rows nodes value) (constraints : List (Edge n)) :
    Satisfies model (expand nodes constraints) value ↔
      Satisfies model constraints value := by
  constructor
  · intro held edge member
    apply (expandEdge_exact model laws input rows nodes value realizes edge).mp
    intro child present
    exact held child (List.mem_flatMap.mpr ⟨edge, member, present⟩)
  · intro held child present
    obtain ⟨edge, member, included⟩ := List.mem_flatMap.mp present
    exact (expandEdge_exact model laws input rows nodes value realizes edge).mpr
      (held edge member) child included

/-- The graph, input references, rows and node provenance are unchanged. -/
def expandCompiled (compiled : Compiled m) : Compiled m :=
  { compiled with constraints := expand compiled.graph compiled.constraints }

theorem expandCompiled_models_iff (model : Model) (laws : Laws model)
    (compiled : Compiled m) (value : Fin compiled.size → model.Ty)
    (rows : Fin m → model.Row) :
    (expandCompiled compiled).Models model value rows ↔ compiled.Models model value rows := by
  change (Realizes model (compiled.restrict value) rows compiled.graph value ∧
      Satisfies model (expand compiled.graph compiled.constraints) value ∧
        ConstraintProblems.RowHolds model rows compiled.rows) ↔ _
  constructor
  · rintro ⟨realizes, held, rowHeld⟩
    exact ⟨realizes,
      (expand_exact model laws _ rows _ value realizes compiled.constraints).mp held, rowHeld⟩
  · rintro ⟨realizes, held, rowHeld⟩
    exact ⟨realizes,
      (expand_exact model laws _ rows _ value realizes compiled.constraints).mpr held, rowHeld⟩

/-- Every target instance and all shared construction slots are retained. -/
theorem expandCompiled_instances_exact (model : Model) (laws : Laws model)
    (compiled : Compiled m) (output : Fin m) (target : Comp model) :
    (expandCompiled compiled).Instance model output target ↔
      compiled.Instance model output target := by
  constructor
  · rintro ⟨value, rows, modeled, bounded⟩
    exact ⟨value, rows, (expandCompiled_models_iff model laws compiled value rows).mp modeled, bounded⟩
  · rintro ⟨value, rows, modeled, bounded⟩
    exact ⟨value, rows, (expandCompiled_models_iff model laws compiled value rows).mpr modeled, bounded⟩

/-- The decision-40 relation discharges every semantic requirement of the
inspector, for arbitrary rows and arbitrary raw supplied head/tail types. -/
theorem shadowLaws {Row : Type u} (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) : Laws (ShadowSemanticRecords.model Row empty join leRow) where
  empty := ShadowRecordDemands.record_empty_exact
  same := ShadowRecordDemands.record_singleton_same_exact
  other := ShadowRecordDemands.record_singleton_other_exact

/-- A concrete endpoint for the new finite relation. It applies to every
compiled problem, including each total `compileSource` alternative. -/
theorem shadow_expand_instances_exact {Row : Type u} (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) (compiled : Compiled m) (output : Fin m)
    (target : Comp (ShadowSemanticRecords.model Row empty join leRow)) :
    (expandCompiled compiled).Instance (ShadowSemanticRecords.model Row empty join leRow) output target ↔
      compiled.Instance (ShadowSemanticRecords.model Row empty join leRow) output target :=
  expandCompiled_instances_exact _ (shadowLaws empty join leRow) compiled output target

/-- The same inspector is exact when original slots contain regular
values, including arbitrary cyclic payloads in the existing carrier. -/
theorem shadowRegularLaws {Row : Type u} (empty : Row) (join : Row → Row → Row)
    (leRow : Row → Row → Prop) : Laws (ShadowRegularInferenceModel.model Row empty join leRow) where
  empty := ShadowRegularInferenceModel.record_empty_exact
  same := ShadowRegularInferenceModel.record_singleton_same_exact
  other := ShadowRegularInferenceModel.record_singleton_other_exact

theorem shadow_regular_expand_instances_exact {Row : Type u}
    (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (compiled : Compiled m) (output : Fin m)
    (target : Comp (ShadowRegularInferenceModel.model Row empty join leRow)) :
    (expandCompiled compiled).Instance (ShadowRegularInferenceModel.model Row empty join leRow) output target ↔
      compiled.Instance (ShadowRegularInferenceModel.model Row empty join leRow) output target :=
  expandCompiled_instances_exact _ (shadowRegularLaws empty join leRow) compiled output target

end Yulang.RecordDemandInspection
