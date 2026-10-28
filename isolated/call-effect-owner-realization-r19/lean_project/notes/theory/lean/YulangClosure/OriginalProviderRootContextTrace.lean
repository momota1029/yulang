import YulangClosure.OriginalSourceSyntax

namespace YulangClosure.OriginalProviderRootContextTrace

open OriginalSource

structure ProviderDeclarationEvidence where
  moduleName : String
  sourceFile : String
  declaration : String
  declarationRange : Nat × Nat
  public : Bool
  definitionRootOwned : Bool
  deriving DecidableEq, Repr

structure ProviderLexicalEvidence where
  formalName : String
  formalRange : Nat × Nat
  bodyName : String
  bodyRange : Nat × Nat
  sameHirParameter : Bool
  localSourceIndex : Nat
  occurrenceOrdinal : Nat
  deriving DecidableEq, Repr

def providerUtf8Sha256 : String := "9b830a0650483a3387ced1724463b5fb18434366fb5a082f8cf7597ca8e7519e"
def providerDeclaration : ProviderDeclarationEvidence := {
  moduleName := "std::core", sourceFile := "lib/std/core.yu", declaration := "pub id x = x", declarationRange := (0, 12), public := true, definitionRootOwned := true
}
def providerLexical : ProviderLexicalEvidence := {
  formalName := "x", formalRange := (7, 8), bodyName := "x", bodyRange := (11, 12), sameHirParameter := true, localSourceIndex := 1, occurrenceOrdinal := 3
}
def providerExportIdentityJoinsDefinition : Bool := true

def semanticImportsEmptyHasNoImportEnvironment : Bool := true
def semanticImportsWithSourceImportsRetainsEnvironment : Bool := true
def callerEvidenceAbsentOnSourceImports : Bool := true
def rootContextConstructionOwner : String := "NO_SAFE_CODE_SLICE: inspected HIR module declaration/LocalSource owners and SemanticImports constructors; none constructs or supplies OriginalSource.Context"
def missingAuthority : String := "no approved constructor maps provider declaration, initializer, imported exports and lexical/source owners to Binding fields (name, Site owner, BindingKind, component, annotation, Entry, singleUse) and ordered Context"
def missingConsumer : String := "OriginalSourceGeneration.sourceRules consumes Context as an explicit argument; provider entry/admission has no Rust-to-OriginalSource Context bridge"
def prohibitedInferences : String := "export identity, visibility, spelling and opaque caller payload do not classify Binding fields or establish Context ordering"
def scopeOfNegativeClaim : String := "the inspected provider fixture and inspected SemanticImports/HirModule/LocalSource construction path only"
def actualWorkingDirectory : String := "/home/momota1029/rust/yulang"
def absoluteOutputTarget : String := "/home/momota1029/rust/yulang/notes/theory/lean/YulangClosure/OriginalProviderRootContextTrace.lean"

end YulangClosure.OriginalProviderRootContextTrace
