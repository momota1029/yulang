import Std

namespace YulangClosure.OriginalProviderPublicationCoverageTrace

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

def actualWorkingDirectory : String := "/home/momota1029/rust/yulang"
def absoluteOutputTarget : String := "/home/momota1029/rust/yulang/notes/theory/lean/YulangClosure/OriginalProviderPublicationCoverageTrace.lean"

end YulangClosure.OriginalProviderPublicationCoverageTrace
