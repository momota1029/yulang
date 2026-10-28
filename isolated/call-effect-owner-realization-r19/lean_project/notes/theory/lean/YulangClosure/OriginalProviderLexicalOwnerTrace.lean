import Std

namespace YulangClosure.OriginalProviderLexicalOwnerTrace

inductive OwnerNode where
  | declaration | lambda | formal | bodyName
  deriving DecidableEq, Repr

structure LexicalParentEdge where
  child : OwnerNode
  parent : OwnerNode
  deriving DecidableEq, Repr

structure ProviderDeclarationRow where
  moduleName : String
  sourceFile : String
  name : String
  byteStart : Nat
  byteEnd : Nat
  isPublic : Bool
  parsedSourceKeyOwned : Bool
  definitionRootOwned : Bool
  deriving DecidableEq, Repr

structure ProviderFormalRow where
  spelling : String
  byteStart : Nat
  byteEnd : Nat
  hirParameterOrdinal : Nat
  localSourceLambdaOrdinal : Nat
  lexicalParent : OwnerNode
  deriving DecidableEq, Repr

structure ProviderBodyNameRow where
  spelling : String
  byteStart : Nat
  byteEnd : Nat
  resolvedHirParameterOrdinal : Nat
  localSourceIndexOrdinal : Nat
  hirOccurrenceOrdinal : Nat
  lexicalParent : OwnerNode
  deriving DecidableEq, Repr

structure ProviderOwnerRows where
  declaration : ProviderDeclarationRow
  formal : ProviderFormalRow
  bodyName : ProviderBodyNameRow
  lexicalParents : List LexicalParentEdge
  deriving DecidableEq, Repr

structure ConsumerExposure where
  exposedName : String
  providerModule : String
  providerName : String
  providerDeclarationRange : Nat × Nat
  matchesSameProviderIdentity : Bool
  deriving DecidableEq, Repr

/-- These constructor-shaped rows are serialized only after Rust has compared the branded DefinitionRootId, HirParameterId, SourceNodeKey, HirOccurrenceId, and complete SourceExportId values. HIR ordinals remain separate provenance fields; the consumer derives logical coordinates from constructors. -/
def providerOwnerRows : ProviderOwnerRows := {
  declaration := { moduleName := "std::core", sourceFile := "lib/std/core.yu", name := "id", byteStart := 0, byteEnd := 12, isPublic := true, parsedSourceKeyOwned := true, definitionRootOwned := true },
  formal := { spelling := "x", byteStart := 7, byteEnd := 8, hirParameterOrdinal := 0, localSourceLambdaOrdinal := 0, lexicalParent := .lambda },
  bodyName := { spelling := "x", byteStart := 11, byteEnd := 12, resolvedHirParameterOrdinal := 0, localSourceIndexOrdinal := 1, hirOccurrenceOrdinal := 3, lexicalParent := .formal },
  lexicalParents := [{ child := .lambda, parent := .declaration }, { child := .formal, parent := .lambda }, { child := .bodyName, parent := .formal }]
}

def consumerExposures : List ConsumerExposure := [
  { exposedName := "identity", providerModule := "std::core", providerName := "id", providerDeclarationRange := (0, 12), matchesSameProviderIdentity := true },
  { exposedName := "id", providerModule := "std::core", providerName := "id", providerDeclarationRange := (0, 12), matchesSameProviderIdentity := true },]

def exactProviderPublicationIdentityChecked : Bool := true
def explicitIdentityResolvesToProvider : Bool := true
def implicitPreludeIdResolvesToProvider : Bool := true
def providerUtf8Sha256 : String := "9b830a0650483a3387ced1724463b5fb18434366fb5a082f8cf7597ca8e7519e"
/-- The owner rows establish provider provenance and lexical identity only. They do not provide initializer execution or original logical event payloads. -/
def traceBoundary : String := "HIR/CST owner rows only; initializer execution and Return/Shared payloads absent"
def originalSourceAttempt : String := "OPEN: no actual Rust owner constructs OriginalSource.Source and the incoming Context from this HIR/CST evidence"
def firstMissingOwner : String := "provider Source/Context introduction: declaration/formal/body owners exist, but Source Site/Name/Declaration allocation, Context, and independent local source admission are absent"
def initializerEventStatus : String := "OPEN: no semantic initializer execution, Return-rebind frame, Shared frame, or captures supplied"
def fixedPublicationMapStatus : String := "OPEN: no actual PublicationRecord or independently justified Environment.publications equation supplied"
def actualWorkingDirectory : String := "/home/momota1029/rust/yulang"
def absoluteOutputTarget : String := "/home/momota1029/rust/yulang/notes/theory/lean/YulangClosure/OriginalProviderLexicalOwnerTrace.lean"

end YulangClosure.OriginalProviderLexicalOwnerTrace
