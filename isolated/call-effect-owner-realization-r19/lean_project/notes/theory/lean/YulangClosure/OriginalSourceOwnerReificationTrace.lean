import YulangClosure.OriginalSourceOwnerReification

namespace YulangClosure.OriginalSourceOwnerReificationTrace

open OriginalSourceOwnerReification

def originTable : OriginTable := {
  inputUtf8 := "my value = \\x -> { (\\x -> x) x; x }", sourceModule := "inline-authentic-extraction", sourceFile := "inline_authentic_extraction.yu",
  physical := [
  { key := .definition, sourceLocator := { positionOrdinal := 1, byteRange := (0, 35) }, localSourceIndex := none, occurrenceOrdinal := none },
  { key := .outerLambda, sourceLocator := { positionOrdinal := 13, byteRange := (11, 35) }, localSourceIndex := some 0, occurrenceOrdinal := some 1 },
  { key := .outerBody, sourceLocator := { positionOrdinal := 19, byteRange := (16, 35) }, localSourceIndex := some 1, occurrenceOrdinal := some 2 },
  { key := .application, sourceLocator := { positionOrdinal := 39, byteRange := (29, 30) }, localSourceIndex := some 3, occurrenceOrdinal := some 3 },
  { key := .rawCallee, sourceLocator := { positionOrdinal := 25, byteRange := (19, 28) }, localSourceIndex := some 4, occurrenceOrdinal := some 4 },
  { key := .argument, sourceLocator := { positionOrdinal := 41, byteRange := (29, 30) }, localSourceIndex := some 5, occurrenceOrdinal := some 7 },
  { key := .innerLambda, sourceLocator := { positionOrdinal := 28, byteRange := (20, 27) }, localSourceIndex := some 6, occurrenceOrdinal := some 5 },
  { key := .innerBody, sourceLocator := { positionOrdinal := 34, byteRange := (25, 27) }, localSourceIndex := some 7, occurrenceOrdinal := some 6 },
  { key := .sibling, sourceLocator := { positionOrdinal := 48, byteRange := (32, 33) }, localSourceIndex := some 2, occurrenceOrdinal := some 8 },
  ],
  formals := [
  { key := .outer, lambda := .outerLambda, parameterOrdinal := 0, binderToken := { positionOrdinal := 15, byteRange := (12, 13) }, spelling := "x" },
  { key := .inner, lambda := .innerLambda, parameterOrdinal := 1, binderToken := { positionOrdinal := 30, byteRange := (21, 22) }, spelling := "x" },
  ], wilds := [{ key := .outer, formal := .outer }, { key := .inner, formal := .inner }],
  names := [
    { key := .declaration, owner := .declaration .value, spelling := "value" },
    { key := .outer, owner := .parameter .outer, spelling := "x" },
    { key := .inner, owner := .parameter .inner, spelling := "x" },
  ], declarations := [{ key := .value, sourceNode := .definition, definitionRootOrdinal := 0 }],
  statements := [{ key := .application, block := .outerBody, sourceOrder := 0, expression := .application }],
  resolutions := [
  { occurrence := .argument, name := .outer, parameterOrdinal := 0 },
  { occurrence := .innerBody, name := .inner, parameterOrdinal := 1 },
  { occurrence := .sibling, name := .outer, parameterOrdinal := 0 },
  ], groups := [{ group := .rawCallee, projected := .innerLambda }],
  body := [
    { sourceOrder := 0, occurrence := .application, kind := .statementExpression },
    { sourceOrder := 1, occurrence := .sibling, kind := .finalExpression },
  ], callerContext := none }

def callerContextStatus : String := "OPEN: runner lowers with SemanticImports.empty and receives no source-module Context/scope owner"
def declarationCoordinateStatus : String := "authentic HIR DefinitionRoot/DefId ordinal recorded; OriginalSource.Declaration allocation is not exposed by Rust"
def eventTelescopeStatus : String := "OPEN: no caller Context or full-root sourceOwners telescope is allocated by this runner"
def sourceOwnersStatus : String := "CST key/range, LocalSource index, and HIR occurrence joins were checked by this execution"
def foreignParseStatus : String := "REJECTED before publication: identical bytes from another ParsedFile do not own selected source keys"
def foreignHirStatus : String := "REJECTED before publication: foreign occurrence is not owned by selected HirModule"
def fixtureInputByteLength : Nat := 35
def sameSpellingParametersDistinct : Bool := true
def rawCalleeIsGroupAndNotProjectedLambda : Bool := true
def executionCwd : String := "/home/momota1029/rust/yulang"
def absoluteOutputTarget : String := "/home/momota1029/rust/yulang/notes/theory/lean/YulangClosure/OriginalSourceOwnerReificationTrace.lean"
end YulangClosure.OriginalSourceOwnerReificationTrace
