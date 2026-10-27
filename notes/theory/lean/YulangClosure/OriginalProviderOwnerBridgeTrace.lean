import Std

namespace YulangClosure.OriginalProviderOwnerBridgeTrace

structure ProviderOwner where
  inputUtf8 : String
  sourceSha256 : String
  moduleName : String
  sourceFile : String
  declarationName : String
  declarationByteRange : Nat × Nat
  namedFormal : String
  formalByteRange : Nat × Nat
  localSourceLambdaIndex : Nat
  bodySpelling : String
  bodyByteRange : Nat × Nat
  localSourceBodyIndex : Nat
  hirOccurrenceOrdinal : Nat
  parserDiagnostics : String
  parseOwnedKeysChecked : Bool
  hirOwnedOccurrenceChecked : Bool
  deriving DecidableEq, Repr

structure ConsumerExposure where
  exposedName : String
  providerModule : String
  providerName : String
  providerDeclarationRange : Nat × Nat
  matchesSameProviderIdentity : Bool
  deriving DecidableEq, Repr

def providerOwner : ProviderOwner := {
  inputUtf8 := "pub id x = x\n", sourceSha256 := "9b830a0650483a3387ced1724463b5fb18434366fb5a082f8cf7597ca8e7519e", moduleName := "std::core", sourceFile := "lib/std/core.yu",
  declarationName := "id", declarationByteRange := (0, 12), namedFormal := "x",
  formalByteRange := (7, 8), localSourceLambdaIndex := 0, bodySpelling := "x",
  bodyByteRange := (11, 12), localSourceBodyIndex := 1, hirOccurrenceOrdinal := 3,
  parserDiagnostics := "[]", parseOwnedKeysChecked := true, hirOwnedOccurrenceChecked := true
}

def consumerExposures : List ConsumerExposure := [
  { exposedName := "identity", providerModule := "std::core", providerName := "id", providerDeclarationRange := (0, 12), matchesSameProviderIdentity := true },
  { exposedName := "id", providerModule := "std::core", providerName := "id", providerDeclarationRange := (0, 12), matchesSameProviderIdentity := true },]
/-- The source/HIR rows above establish provenance and identity joins only. They do not execute the initializer or provide original logical event payloads. -/
def traceBoundary : String := "HIR/CST provenance only; initializer execution and Return/Shared payloads absent"

def originalSourceAttempt : String := "OPEN: no actual Rust owner constructs the corresponding OriginalSource.Source and incoming Context from this HIR/CST evidence"

def firstMissingOwner : String := "provider Source/Context introduction: the Rust owner path exposes declaration/formal/body provenance but no Source Site/Name/Declaration allocation, Context, or independent local source admission"

def initializerEventStatus : String := "OPEN: no semantic initializer execution, Return-rebind frame, Shared frame, or captures supplied"

def fixedPublicationMapStatus : String := "OPEN: no actual PublicationRecord or independently justified Environment.publications equation supplied"

def explicitIdentityResolvesToProvider : Bool := true
def implicitPreludeIdResolvesToProvider : Bool := true

/-- Source-owner row schema from inspected Rust types; values below summarize r2 predicates but were not emitted by the r1 adapter. -/
structure DeclarationOwnerRow where
  carrierType : String
  declarationName : String
  moduleNamespace : String
  isPublic : Bool
  byteRange : Nat × Nat
  sourceOwnerChecked : Bool
  deriving DecidableEq, Repr

structure FormalOwnerRow where
  carrierType : String
  spelling : String
  byteRange : Nat × Nat
  joinsHirNamedParameter : Bool
  sourceOwnerChecked : Bool
  deriving DecidableEq, Repr

structure BodyOwnerRow where
  carrierType : String
  spelling : String
  resolution : String
  byteRange : Nat × Nat
  sourceOwnerChecked : Bool
  deriving DecidableEq, Repr

def declarationOwnerRow : DeclarationOwnerRow := {
  carrierType := "yu_hir::HirBinding + yu_hir::SourceExportDeclaration",
  declarationName := "id", moduleNamespace := "std::core", isPublic := true,
  byteRange := (0, 12), sourceOwnerChecked := true
}

def formalOwnerRow : FormalOwnerRow := {
  carrierType := "yu_hir::LocalSourceNamedFormal / LocalSourceParameter",
  spelling := "x", byteRange := (7, 8), joinsHirNamedParameter := true,
  sourceOwnerChecked := true
}

def bodyOwnerRow : BodyOwnerRow := {
  carrierType := "yu_hir::LocalSourceExpr",
  spelling := "x", resolution := "LocalSourceResolution::Parameter(same HirParameterId)",
  byteRange := (11, 12), sourceOwnerChecked := true
}

/-- HIR vector/occurrence ordinals are retained as carrier provenance only. -/
def carrierIndices : String := "named lambda LocalSourceIndex=0; terminal body LocalSourceIndex=1; HirOccurrenceId ordinal=3; no index is a logical OriginalSource coordinate"

def lexicalImportPreparation : String := "consumer text imports std::core::id as identity and uses prelude id; SemanticImports::with_source_imports retains parse-bound SourceImportEnvironment; identity and id resolve to equal exact SourceExportId(std::core,id,[0,12))"

def sourceConstructionBoundary : String := "LocalSource is produced during HIR lowering; source_exports indexes parse-owned declarations/use trees; with_source_imports resolves imported names. No inspected Rust constructor or consumer maps these values to OriginalSource.Site/Name/Declaration, constructs an incoming logical Context, or independently admits a local SourceJudgment."

def adapterExecutionStatus : String := "r2 executable trace values reused. The r2 Rust checks join the formal to the HIR parameter and the body Name resolution to that same HirParameterId, but its Lean output does not serialize those IDs/typed rows. r1 adapter Cargo invocation failed to compile after adaptation; final source fixes were not rebuilt because the two Cargo-call allowance was exhausted. This trace is a provisional transcription, not freshly emitted executable evidence."

def actualWorkingDirectory : String := "/home/momota1029/rust/yulang"
def absoluteOutputTarget : String := "/home/momota1029/rust/yulang/notes/theory/lean/YulangClosure/OriginalProviderOwnerBridgeTrace.lean"

end YulangClosure.OriginalProviderOwnerBridgeTrace
