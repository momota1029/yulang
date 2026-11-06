import Yulang.RecordDemandInspection
import Yulang.SingletonRecordGraph

/-!
# Record-demand inspection on the original source compiler's output

Every original source alternative is retained, together with its node pool,
row problem and output reference. A single pass expands inspectable record
comparisons. The resulting family has exactly the same instances as original
source typing in both finite and regular decision-40 models.

Graph `Models` conditions remain in these instance statements. No saturation,
free-parameter solution construction, or full-core inference success theorem
is claimed by this compilation/inspection stage.
-/

namespace Yulang.SourceRecordDemandInspection

open Inference OpenRecordConstraintGraph RecordDemandInspection

def expandAlternative (alternative : SourceAlternative) : SourceAlternative :=
  { alternative with compiled := expandCompiled alternative.compiled }

def prepareSource (expression : Expr) : List SourceAlternative :=
  (compileSource expression).map expandAlternative

/-- Every record-to-record constraint in the actual original source output
is handled by the inspector. The required empty-tail tag is derived from
the generator, not supplied as a shape certificate or inferred type. -/
theorem source_record_pair_inspected (expression : Expr) (alternative : SourceAlternative)
    (member : alternative ∈ compileSource expression) (edge : Edge alternative.compiled.size)
    (present : edge ∈ alternative.compiled.constraints) (label demanded : Nat)
    (head tail expected remainder : Fin alternative.compiled.size)
    (sourceNode : alternative.compiled.graph edge.1 = .recordExtend label head tail)
    (targetNode : alternative.compiled.graph edge.2 = .recordExtend demanded expected remainder) :
    inspect alternative.compiled.graph edge.1 edge.2 =
      some (if label = demanded then [(head, expected), (tail, remainder)] else [(tail, edge.2)]) := by
  have emptyTail := (SingletonRecordGraph.compileSource_upper_record_tail
    expression alternative member edge present demanded expected remainder targetNode).2
  simp only [inspect, sourceNode, targetNode, emptyTail]
  split <;> rfl

theorem alternative_instances_exact (model : Model) (laws : Laws model)
    (alternative : SourceAlternative) (target : Comp model) :
    (expandAlternative alternative).Instance model target ↔ alternative.Instance model target :=
  expandCompiled_instances_exact model laws alternative.compiled alternative.output target

/-- The actual executable pass preserves every original source alternative
and every target instance, rather than selecting one typing or solution. -/
theorem source_instances_exact (model : Model) (laws : Laws model)
    (expression : Expr) (target : Comp model) :
    SourceInstance model (prepareSource expression) target ↔
      SourceInstance model (compileSource expression) target := by
  constructor
  · rintro ⟨expanded, present, accepted⟩
    obtain ⟨original, member, rfl⟩ := List.mem_map.mp present
    exact ⟨original, member, (alternative_instances_exact model laws original target).mp accepted⟩
  · rintro ⟨original, member, accepted⟩
    exact ⟨expandAlternative original, List.mem_map.mpr ⟨original, member, rfl⟩,
      (alternative_instances_exact model laws original target).mpr accepted⟩

/-- Every original core constructor is covered in the finite shadow model.
The row assumptions are the existing preorder assumptions of source typing. -/
theorem shadow_source_typing_exact {Row : Type u}
    (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (expression : Expr) (target : Comp (ShadowSemanticRecords.model Row empty join leRow)) :
    SourceInstance (ShadowSemanticRecords.model Row empty join leRow)
        (prepareSource expression) target ↔
      Typing (ShadowSemanticRecords.model Row empty join leRow) [] expression target :=
  (source_instances_exact _ (shadowLaws empty join leRow) expression target).trans
    (compileSource_instances_exact (ShadowSemanticRecords.model Row empty join leRow)
      ShadowSemanticRecords.union_is_join
      ShadowSemanticRecords.Subtype.refl ShadowSemanticRecords.Subtype.trans
      rowRefl rowTrans expression target)

/-- The same whole-source statement holds in the common regular carrier.
It does not identify its extra existential regular witnesses with finite ones. -/
theorem shadow_regular_source_typing_exact {Row : Type u}
    (empty : Row) (join : Row → Row → Row) (leRow : Row → Row → Prop)
    (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (expression : Expr) (target : Comp (ShadowRegularInferenceModel.model Row empty join leRow)) :
    SourceInstance (ShadowRegularInferenceModel.model Row empty join leRow)
        (prepareSource expression) target ↔
      Typing (ShadowRegularInferenceModel.model Row empty join leRow) [] expression target :=
  (source_instances_exact _ (shadowRegularLaws empty join leRow) expression target).trans
    (compileSource_instances_exact (ShadowRegularInferenceModel.model Row empty join leRow)
      ShadowRegularValueTypes.union_is_join
      (ShadowRegularInferenceModel.subtype_refl leRow) ShadowRegularInferenceModel.subtype_trans
      rowRefl rowTrans expression target)

end Yulang.SourceRecordDemandInspection
