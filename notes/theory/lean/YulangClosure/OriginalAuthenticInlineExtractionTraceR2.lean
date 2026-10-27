-- Generated only by the authenticated Rust owner path in tools/inline-authentic-extraction/src/main.rs.
-- This is a finite source/HIR trace, not an allocation law or a parent theorem.
namespace YulangClosure.OriginalAuthenticInlineExtractionTraceR2

structure TraceSourcePosition where
  label : String
  kind : String
  positionOrdinal : Nat
  byteRange : Nat × Nat

structure TraceBodyEntry where
  kind : String
  sourceOrder : Nat
  localSourceIndex : Option Nat
  bindingOrdinal : Option Nat
  occurrenceOrdinal : Option Nat
  byteRange : Option (Nat × Nat)
  sourcePositionOrdinal : Option Nat

structure TraceGroupProjection where
  groupIndex : Nat
  innerIndex : Nat
  groupOccurrence : Nat
  innerOccurrence : Nat
  groupRange : Nat × Nat
  innerRange : Nat × Nat

structure TraceNameResolution where
  label : String
  sourceIndex : Nat
  occurrenceOrdinal : Nat
  spelling : String
  resolutionKind : String
  parameterOrdinal : Nat
  sourcePositionOrdinal : Nat
  byteRange : Nat × Nat

def traceSchemaVersion : Nat := 1
def inputUtf8 : String := "my value = \\x -> { (\\x -> x) x; x }"
def inputByteLength : Nat := 35
def sourceModule : String := "inline-authentic-extraction"
def sourceFile : String := "inline_authentic_extraction.yu"
def sourceRootKind : String := "Definition"
def definitionSourcePositionOrdinal : Nat := 1
def definitionSourceRange : Nat × Nat := (0, 35)
def outerLambdaRange : Nat × Nat := (11, 35)
def outerLambdaOccurrenceOrdinal : Nat := 1
def outerParameterOrdinal : Nat := 0
def outerParameterSpelling : String := "x"
def outerBinderTokenRange : Nat × Nat := (12, 13)
def outerBinderEqualsRegisteredRange : Bool := true
def outerLambdaIndexOrdinal : Nat := 0
def outerBodyForm : String := "StatementBlock"
def outerBodyRange : Nat × Nat := (16, 35)
def outerBodyOccurrenceOrdinal : Nat := 2
def outerBodyIndexOrdinal : Nat := 1
def applyIndexOrdinal : Nat := 3
def applyOccurrenceOrdinal : Nat := 3
def applyRange : Nat × Nat := (29, 30)
def applySourceForm : String := "MlArgument"
def rawApplyCalleeIndexOrdinal : Nat := 4
def rawApplyCalleeOccurrenceOrdinal : Nat := 4
def rawApplyCalleeForm : String := "Group"
def rawApplyCalleeRange : Nat × Nat := (19, 28)
def rawApplyArgumentIndexOrdinal : Nat := 5
def rawApplyArgumentOccurrenceOrdinal : Nat := 7
def rawApplyArgumentForm : String := "Name"
def rawApplyArgumentRange : Nat × Nat := (29, 30)
def projectedInnerLambdaIndexOrdinal : Nat := 6
def projectedCalleeForm : String := "Lambda"
def innerLambdaRange : Nat × Nat := (20, 27)
def innerLambdaOccurrenceOrdinal : Nat := 5
def innerParameterOrdinal : Nat := 1
def innerParameterSpelling : String := "x"
def innerBinderTokenRange : Nat × Nat := (21, 22)
def innerBinderEqualsRegisteredRange : Bool := true
def innerBodyIndexOrdinal : Nat := 7
def innerBodyOccurrenceOrdinal : Nat := 6
def sameSpellingNestedParametersAreDistinct : Bool := true
def originalAllocationStatus : String := "open_not_established_by_this_trace"
def sourcePositions : List TraceSourcePosition := [
  { label := "definition", kind := "node", positionOrdinal := 1, byteRange := (0, 35) },
  { label := "local-expression-0", kind := "node", positionOrdinal := 13, byteRange := (11, 35) },
  { label := "local-expression-1", kind := "node", positionOrdinal := 19, byteRange := (16, 35) },
  { label := "local-expression-2", kind := "node", positionOrdinal := 48, byteRange := (32, 33) },
  { label := "local-expression-3", kind := "node", positionOrdinal := 39, byteRange := (29, 30) },
  { label := "local-expression-4", kind := "node", positionOrdinal := 25, byteRange := (19, 28) },
  { label := "local-expression-5", kind := "node", positionOrdinal := 41, byteRange := (29, 30) },
  { label := "local-expression-6", kind := "node", positionOrdinal := 28, byteRange := (20, 27) },
  { label := "local-expression-7", kind := "node", positionOrdinal := 34, byteRange := (25, 27) },
  { label := "outer-parameter-lambda-key", kind := "node", positionOrdinal := 13, byteRange := (11, 35) },
  { label := "outer-binder-token", kind := "token", positionOrdinal := 15, byteRange := (12, 13) },
  { label := "inner-parameter-lambda-key", kind := "node", positionOrdinal := 28, byteRange := (20, 27) },
  { label := "inner-binder-token", kind := "token", positionOrdinal := 30, byteRange := (21, 22) },
  { label := "raw-apply-callee", kind := "node", positionOrdinal := 25, byteRange := (19, 28) },
  { label := "raw-apply-argument", kind := "node", positionOrdinal := 41, byteRange := (29, 30) },
  { label := "apply", kind := "node", positionOrdinal := 39, byteRange := (29, 30) },
  { label := "outer-body", kind := "node", positionOrdinal := 19, byteRange := (16, 35) },
  { label := "projected-inner-lambda", kind := "node", positionOrdinal := 28, byteRange := (20, 27) },
  { label := "group-projection-0", kind := "node", positionOrdinal := 25, byteRange := (19, 28) },
  { label := "group-projection-0-inner", kind := "node", positionOrdinal := 28, byteRange := (20, 27) },
  { label := "outer-body-entry-0", kind := "node", positionOrdinal := 39, byteRange := (29, 30) },
  { label := "outer-body-entry-1", kind := "node", positionOrdinal := 48, byteRange := (32, 33) },
]
def outerBodyIncidence : List TraceBodyEntry := [
  { kind := "statement-expression", sourceOrder := 0, localSourceIndex := some 3, bindingOrdinal := none, occurrenceOrdinal := some 3, byteRange := some (29, 30), sourcePositionOrdinal := some 39 },
  { kind := "final-expression", sourceOrder := 1, localSourceIndex := some 2, bindingOrdinal := none, occurrenceOrdinal := some 8, byteRange := some (32, 33), sourcePositionOrdinal := some 48 },
]
def groupProjectionPath : List TraceGroupProjection := [
  { groupIndex := 4, innerIndex := 6, groupOccurrence := 4, innerOccurrence := 5, groupRange := (19, 28), innerRange := (20, 27) },
]
def nameResolutions : List TraceNameResolution := [
  { label := "apply-argument", sourceIndex := 5, occurrenceOrdinal := 7, spelling := "x", resolutionKind := "Parameter", parameterOrdinal := 0, sourcePositionOrdinal := 41, byteRange := (29, 30) },
  { label := "inner-body", sourceIndex := 7, occurrenceOrdinal := 6, spelling := "x", resolutionKind := "Parameter", parameterOrdinal := 1, sourcePositionOrdinal := 34, byteRange := (25, 27) },
  { label := "restored-sibling", sourceIndex := 2, occurrenceOrdinal := 8, spelling := "x", resolutionKind := "Parameter", parameterOrdinal := 0, sourcePositionOrdinal := 48, byteRange := (32, 33) },
]
def rawCalleeIsNotProjectedIdentity : Bool := true
def foreignOwnerChecks : List String := ["equal-text foreign SourceNodeKey rejected as ForeignParse", "foreign parameter identity rejected as ForeignHirArtifact", "foreign parse artifact rejected selected parameter origin as ForeignParse", "foreign HIR occurrence rejected by selected HIR"]
def originalSiteNameContextEventAllocation : String := "not supplied; no Rust ordinal is interpreted as an original coordinate"
end YulangClosure.OriginalAuthenticInlineExtractionTraceR2
