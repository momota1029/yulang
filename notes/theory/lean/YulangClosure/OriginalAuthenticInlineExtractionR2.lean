import YulangClosure.OriginalAuthenticInlineExtractionTraceR2

/-!
Finite consumer of the executed r2 trace (SHA-256
73a4a8aa65e5d7d44611a70e52b9d2b6ac5940c2292a7c06e01e69834f2ac5e3).
These theorems inspect serialized data, not Rust pointer brands or a universal
frontend refinement. Original allocation and every whole parent remain OPEN.
In particular Apply's MlArgument range is its tail node, not a whole-call span.
-/
namespace YulangClosure.OriginalAuthenticInlineExtractionR2

open OriginalAuthenticInlineExtractionTraceR2

def ValidRange (span : Nat × Nat) : Prop :=
  span.1 < span.2 ∧ span.2 ≤ inputByteLength

/-- Byte indexing is performed on UTF-8 bytes, not character offsets. -/
def bytesAt (span : Nat × Nat) : List UInt8 :=
  (inputUtf8.toUTF8.data.toList.drop span.1).take (span.2 - span.1)

theorem input_byte_length : inputUtf8.toUTF8.size = inputByteLength := by decide

theorem all_position_ranges : ∀ row ∈ sourcePositions, ValidRange row.byteRange := by
  unfold ValidRange
  decide

theorem exact_binder_bytes :
    bytesAt outerBinderTokenRange = "x".toUTF8.data.toList ∧
    bytesAt innerBinderTokenRange = "x".toUTF8.data.toList := by decide

/-- These are exact token-position rows; the separate literal registered-range
flags are not used as evidence of a Rust equality. -/
theorem binder_position_rows :
    (sourcePositions.filter (fun row => row.kind == "token")).map
      (fun row => (row.label, row.byteRange)) =
    [("outer-binder-token", outerBinderTokenRange),
     ("inner-binder-token", innerBinderTokenRange)] := by decide

/-- All six serialized fields are retained for the one actual projection edge. -/
theorem group_projection_incidence :
    groupProjectionPath.map (fun edge =>
      (edge.groupIndex, edge.innerIndex, edge.groupOccurrence,
       edge.innerOccurrence, edge.groupRange, edge.innerRange)) =
    [(rawApplyCalleeIndexOrdinal, projectedInnerLambdaIndexOrdinal,
      rawApplyCalleeOccurrenceOrdinal, innerLambdaOccurrenceOrdinal,
      rawApplyCalleeRange, innerLambdaRange)] ∧
    rawApplyCalleeIndexOrdinal ≠ projectedInnerLambdaIndexOrdinal ∧
    rawApplyCalleeForm = "Group" ∧ projectedCalleeForm = "Lambda" :=
  ⟨rfl, by decide, rfl, rfl⟩

theorem group_range_contains_projected_lambda :
    rawApplyCalleeRange.1 < innerLambdaRange.1 ∧
    innerLambdaRange.2 < rawApplyCalleeRange.2 := by decide

/-- Preserve the actual MlArgument owner convention; no callee containment in
applyRange is asserted. The raw argument and whole-call callee remain distinct. -/
theorem apply_tail_range :
    applySourceForm = "MlArgument" ∧
    applyRange = rawApplyArgumentRange ∧
    rawApplyCalleeRange.2 < applyRange.1 ∧
    rawApplyCalleeIndexOrdinal ≠ rawApplyArgumentIndexOrdinal := by decide

/-- All seven fields of every direct body entry are checked, including the
statement/final split. This fixture has no binding-statement initializer. -/
theorem complete_direct_body_incidence :
    outerBodyForm = "StatementBlock" ∧
    outerBodyIncidence.map (fun row =>
      (row.kind, row.sourceOrder, row.localSourceIndex, row.bindingOrdinal,
       row.occurrenceOrdinal, row.byteRange, row.sourcePositionOrdinal)) =
    [("statement-expression", 0, some applyIndexOrdinal, none,
        some applyOccurrenceOrdinal, some applyRange, some 39),
     ("final-expression", 1, some 2, none, some 8, some (32, 33), some 48)] := ⟨rfl, rfl⟩

/-- Name rows preserve spelling, owner-local parameter ordinals and source
positions. Equality of these ordinals is not equality of unbranded Rust IDs. -/
theorem exact_name_resolution_rows :
    nameResolutions.map (fun row =>
      (row.label, row.sourceIndex, row.occurrenceOrdinal, row.spelling,
       row.resolutionKind, row.parameterOrdinal, row.sourcePositionOrdinal,
       row.byteRange)) =
    [("apply-argument", rawApplyArgumentIndexOrdinal,
        rawApplyArgumentOccurrenceOrdinal, outerParameterSpelling, "Parameter",
        outerParameterOrdinal, 41, rawApplyArgumentRange),
     ("inner-body", innerBodyIndexOrdinal, innerBodyOccurrenceOrdinal,
        innerParameterSpelling, "Parameter", innerParameterOrdinal, 34, (25, 27)),
     ("restored-sibling", 2, 8, outerParameterSpelling, "Parameter",
        outerParameterOrdinal, 48, (32, 33))] ∧
    outerParameterSpelling = innerParameterSpelling ∧
    outerParameterOrdinal ≠ innerParameterOrdinal :=
  ⟨rfl, rfl, by decide⟩

/-- Each resolved Name locates a node row with the same exact position/range. -/
theorem names_have_source_positions : ∀ name ∈ nameResolutions,
    ∃ position ∈ sourcePositions,
      position.kind = "node" ∧
      position.positionOrdinal = name.sourcePositionOrdinal ∧
      position.byteRange = name.byteRange := by decide

/-- The later direct final expression restores the outer ordinal after the
inner Name row. This checks the snapshot, not the Rust restore algorithm. -/
theorem shadow_and_restoration_snapshot :
    nameResolutions.map (fun row => row.parameterOrdinal) =
      [outerParameterOrdinal, innerParameterOrdinal, outerParameterOrdinal] ∧
    outerBodyIncidence.map (fun row => row.sourceOrder) = [0, 1] ∧
    outerBodyIncidence.map (fun row => row.localSourceIndex) =
      [some applyIndexOrdinal, some 2] ∧
    applyRange.2 < 32 := by decide

/-- The producer's four report strings are data, not a Rust rejection theorem. -/
theorem foreign_report_inventory :
    foreignOwnerChecks =
      ["equal-text foreign SourceNodeKey rejected as ForeignParse",
       "foreign parameter identity rejected as ForeignHirArtifact",
       "foreign parse artifact rejected selected parameter origin as ForeignParse",
       "foreign HIR occurrence rejected by selected HIR"] := rfl

end YulangClosure.OriginalAuthenticInlineExtractionR2
