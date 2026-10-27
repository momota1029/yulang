import YulangClosure.OriginalProviderLexicalOwnerTrace
import YulangClosure.OriginalProviderPublicationCoverage

/-!
Constructor-directed reification of the executed `pub id x = x` owner rows.
The trace is external provenance, not a semantic admission or Context witness.
Coordinates are indices in the retained constructor inventory; Rust ordinals
and byte positions are never used as logical coordinates. Administrative Wild
and binding sites have their own tags. This bounded fixture does not replace
the original whole-language source domain.
-/
namespace YulangClosure.OriginalProviderLexicalOwner

open OriginalSource OriginalProviderSourceSolution OriginalProviderLexicalOwnerTrace

inductive SiteKey where
  | owner (node : OwnerNode)
  | formalPattern
  | declarationBinding
  deriving DecidableEq, BEq, Repr

inductive NameKey where
  | provider | formal
  deriving DecidableEq, BEq, Repr

/-- Retain the observed lexical order, then introduce the two administrative
source constructors. The root declaration remains distinct from its binding. -/
def siteKeys (rows : ProviderOwnerRows) : List SiteKey :=
  [.owner .declaration] ++ rows.lexicalParents.map (fun edge => .owner edge.child) ++
    [.formalPattern, .declarationBinding]

def nameKeys : List NameKey := [.provider, .formal]

def siteCoordinate (rows : ProviderOwnerRows) (key : SiteKey) : Site :=
  (siteKeys rows).idxOf key

def nameCoordinate (key : NameKey) : Name := nameKeys.idxOf key

def occurrences (rows : ProviderOwnerRows) : Occurrences := {
  binding := siteCoordinate rows .declarationBinding
  closure := siteCoordinate rows (.owner .lambda)
  formal := siteCoordinate rows (.owner .formal)
  pattern := siteCoordinate rows .formalPattern
  body := siteCoordinate rows (.owner .bodyName)
  providerName := nameCoordinate .provider
  formalName := nameCoordinate .formal }

/-- A partial decoder for this exact unannotated provider fixture. Parent
incidence and the serialized parameter join are checked before constructing
the Name with the formal's logical identity. Branded equality is source-side
evidence; ordinal equality below does not authenticate a Rust identity. -/
def rowsValid (rows : ProviderOwnerRows) : Bool :=
  rows.declaration.moduleName == "std::core" &&
  rows.declaration.sourceFile == "lib/std/core.yu" &&
  rows.declaration.name == "id" && rows.declaration.isPublic &&
  rows.declaration.parsedSourceKeyOwned && rows.declaration.definitionRootOwned &&
  rows.formal.spelling == "x" && rows.bodyName.spelling == "x" &&
  rows.formal.lexicalParent == .lambda && rows.bodyName.lexicalParent == .formal &&
  rows.formal.hirParameterOrdinal == rows.bodyName.resolvedHirParameterOrdinal &&
  rows.lexicalParents == [⟨.lambda, .declaration⟩, ⟨.formal, .lambda⟩, ⟨.bodyName, .formal⟩]

def translate (rows : ProviderOwnerRows) : Option (Source .bindings) :=
  if rowsValid rows then
    some (.binding (siteCoordinate rows .declarationBinding) (nameCoordinate .provider) none
      (.lambda ⟨siteCoordinate rows (.owner .lambda), none⟩
        ⟨siteCoordinate rows (.owner .formal), nameCoordinate .formal, none, false⟩
        (.wild (siteCoordinate rows .formalPattern))
        (.name ⟨siteCoordinate rows (.owner .bodyName), none⟩ (nameCoordinate .formal)))
      .bindingsNil)
  else none

theorem emitted_rows_valid : rowsValid providerOwnerRows = true := by decide

theorem site_coordinate_rows (key : SiteKey) :
    (siteKeys providerOwnerRows)[siteCoordinate providerOwnerRows key]? = some key := by
  cases key with
  | owner node => cases node <;> decide
  | formalPattern => decide
  | declarationBinding => decide

theorem site_coordinates_injective : Function.Injective (siteCoordinate providerOwnerRows) := by
  intro first second same
  exact Option.some.inj ((site_coordinate_rows first).symm.trans
    ((congrArg (fun index => (siteKeys providerOwnerRows)[index]?) same).trans
      (site_coordinate_rows second)))

theorem name_coordinate_rows (key : NameKey) :
    nameKeys[nameCoordinate key]? = some key := by
  cases key <;> decide

theorem name_coordinates_injective : Function.Injective nameCoordinate := by
  intro first second same
  exact Option.some.inj ((name_coordinate_rows first).symm.trans
    ((congrArg (fun index => nameKeys[index]?) same).trans (name_coordinate_rows second)))

/-- The concrete decoder output is the original provider constructor tree,
not an assumed Source supplied as a theorem premise. -/
theorem translated_source :
    translate providerOwnerRows = some (occurrences providerOwnerRows).source := by rfl

def providerFormal : Formal :=
  ⟨(occurrences providerOwnerRows).formal, (occurrences providerOwnerRows).formalName, none, false⟩

def providerBody : Source .expression :=
  .name ⟨(occurrences providerOwnerRows).body, none⟩ (occurrences providerOwnerRows).formalName

/-- Exactly the formal Context expression in `sourceRules`' Lambda case.
The genuine incoming root Context remains universally quantified. -/
def formalContext (incoming : Context) : Context :=
  {name := providerFormal.name, owner := providerFormal.site, kind := .formal,
    annotation := providerFormal.annotation, entry := some providerFormal.entry,
    singleUse := providerBody.nameCount providerFormal.name == 1} :: incoming

theorem formal_context_extension (incoming : Context) :
    formalContext incoming = (occurrences providerOwnerRows).bodyContext incoming := by rfl

theorem body_name_lookup (incoming : Context) :
    lookupBinding (formalContext incoming) (occurrences providerOwnerRows).formalName =
      some ⟨(occurrences providerOwnerRows).formalName,
        (occurrences providerOwnerRows).formal, .formal, none, none, some .value, true⟩ := by
  rw [formal_context_extension]
  exact body_resolves_original_formal (occurrences providerOwnerRows) incoming

end YulangClosure.OriginalProviderLexicalOwner
