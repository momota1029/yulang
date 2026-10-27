import YulangClosure.OriginalSourceOwnerReification

/-! Data schema for one executed caller/resolver trace. These are owner-local
provenance locators, not allocations of OriginalSource names, sites, Context
bindings, semantic guards or runtime frames. The consumer and every provider
retain their separate parse/module identity; Rust checks authenticate those
owners before this serialization. A complete root inventory is distinct from
an adopted import-to-source translation and a complete original RuleTree. -/
namespace YulangClosure.OriginalSourceCallerSchema

open OriginalSourceOwnerReification

structure ModuleRow where
  ordinal : Nat
  moduleName : String
  sourceFile : String
  inputUtf8 : String
  parseRoot : SyntaxLocator
  deriving DecidableEq, Repr

structure RootRow where
  sourceOrder : Nat
  node : SyntaxLocator
  syntaxKind : String
  hirKind : String
  declarationName : Option String
  definitionOrdinal : Option Nat
  deriving DecidableEq, Repr

structure ImportLeafRow where
  ownerModule : Nat
  declarationLocator : SyntaxLocator
  leafLocator : SyntaxLocator
  path : List String
  selectedName : Option String
  alias : Option String
  isGlob : Bool
  isPublic : Bool
  recovered : Bool
  deriving DecidableEq, Repr

structure ExportRow where
  ordinal : Nat
  providerModule : Nat
  moduleName : String
  name : String
  declaration : SyntaxLocator
  kind : String
  isPublic : Bool
  recovered : Bool
  deriving DecidableEq, Repr

structure LookupRow where
  exposedName : String
  exportOrdinal : Nat
  publicRoute : List ImportLeafRow
  deriving DecidableEq, Repr

structure ImportedUseRow where
  rootSourceOrder : Nat
  sourceLocator : SyntaxLocator
  localSourceIndex : Nat
  occurrenceOrdinal : Nat
  exposedName : String
  exportOrdinal : Nat
  deriving DecidableEq, Repr

structure CallerTable where
  consumer : ModuleRow
  providers : List ModuleRow
  imports : List ImportLeafRow
  exports : List ExportRow
  lookups : List LookupRow
  importedUses : List ImportedUseRow
  roots : List RootRow
  selectedRootOrder : Nat
  selected : OriginTable
  unresolved : List String

def lookupExport (table : CallerTable) (exposedName : String) : Option ExportRow := do
  let lookup ← table.lookups.find? (fun row => row.exposedName = exposedName)
  table.exports.find? (fun row => row.ordinal = lookup.exportOrdinal)

/-- Finite table consistency. This does not construct an OriginalSource.Binding. -/
def ImportedUseAgrees (table : CallerTable) (use : ImportedUseRow) : Prop :=
  ∃ lookup ∈ table.lookups,
    lookup.exposedName = use.exposedName ∧ lookup.exportOrdinal = use.exportOrdinal

end YulangClosure.OriginalSourceCallerSchema
