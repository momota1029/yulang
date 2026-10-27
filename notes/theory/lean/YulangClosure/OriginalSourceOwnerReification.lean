import YulangClosure.OriginalIdentityEntryOrigin
import YulangClosure.OriginalAuthenticInlineExtractionTraceR2

/-! Frozen owner-table schema. Raw ordinals below are authenticatable provenance
locators, never allocations into OriginalSource's Nat coordinates. No Context,
ambient scope, successful correspondence, semantic law or runtime value occurs
in OriginTable. OriginalCoordinates is an explicitly uninstantiated owner
interface; finite row-index construction and its required laws are separate.
CallerContextOrigin records preparation provenance without an equation to Context.
The schema ends at OWNER_SCHEMA_END; subsequent proofs may only be appended. -/
namespace YulangClosure.OriginalSourceOwnerReification

open OriginalSource OriginalSourceEvents OriginalIdentityRealization

inductive PhysicalKey where
  | definition | outerLambda | outerBody | application | rawCallee
  | argument | innerLambda | innerBody | sibling
  deriving DecidableEq, Repr
inductive FormalKey where
  | outer | inner
  deriving DecidableEq, Repr
inductive AdminWildKey where
  | outer | inner
  deriving DecidableEq, Repr
inductive AdminStatementKey where
  | application
  deriving DecidableEq, Repr
inductive NameKey where
  | declaration | outer | inner
  deriving DecidableEq, Repr
inductive DeclarationKey where
  | value
  deriving DecidableEq, Repr

structure SyntaxLocator where
  positionOrdinal : Nat
  byteRange : Nat × Nat
  deriving DecidableEq, Repr
structure PhysicalRow where
  key : PhysicalKey
  sourceLocator : SyntaxLocator
  localSourceIndex : Option Nat
  occurrenceOrdinal : Option Nat
  deriving DecidableEq, Repr
structure FormalRow where
  key : FormalKey
  lambda : PhysicalKey
  parameterOrdinal : Nat
  binderToken : SyntaxLocator
  spelling : String
  deriving DecidableEq, Repr
structure AdminWildRow where
  key : AdminWildKey
  formal : FormalKey
  deriving DecidableEq, Repr
inductive NameOwner where
  | declaration (key : DeclarationKey)
  | parameter (key : FormalKey)
  deriving DecidableEq, Repr
structure NameRow where
  key : NameKey
  owner : NameOwner
  spelling : String
  deriving DecidableEq, Repr
structure DeclarationRow where
  key : DeclarationKey
  sourceNode : PhysicalKey
  definitionRootOrdinal : Nat
  deriving DecidableEq, Repr
structure ResolutionRow where
  occurrence : PhysicalKey
  name : NameKey
  parameterOrdinal : Nat
  deriving DecidableEq, Repr
structure GroupRow where
  group : PhysicalKey
  projected : PhysicalKey
  deriving DecidableEq, Repr
/-- Administrative statement reification from the exact containing block and
ordered expression incidence. This is not a fabricated physical CST statement. -/
structure AdminStatementRow where
  key : AdminStatementKey
  block : PhysicalKey
  sourceOrder : Nat
  expression : PhysicalKey
  deriving DecidableEq, Repr
inductive BodyEntryKind where
  | statementExpression | finalExpression
  deriving DecidableEq, Repr
structure BodyRow where
  sourceOrder : Nat
  occurrence : PhysicalKey
  kind : BodyEntryKind
  deriving DecidableEq, Repr

/-- Serialized owner coordinates for a real caller preparation. These records
are provenance, not an OriginalSource.Context or evidence of semantic admission. -/
structure ModuleIdentityOrigin where
  moduleName : String
  sourceFile : String
  deriving DecidableEq, Repr
structure ProviderHirRootOrigin where
  moduleIdentity : ModuleIdentityOrigin
  parseRoot : SyntaxLocator
  definitionSource : SyntaxLocator
  definitionOrdinal : Nat
  deriving DecidableEq, Repr
structure ImportIndexOrigin where
  importingModule : ModuleIdentityOrigin
  importSource : SyntaxLocator
  selectedProvider : ProviderHirRootOrigin
  deriving DecidableEq, Repr
structure CallerContextOrigin where
  moduleIdentity : ModuleIdentityOrigin
  parseRoot : SyntaxLocator
  selectedDeclaration : DeclarationKey
  sourceImportEnvironment : List ImportIndexOrigin
  importIndexes : List ImportIndexOrigin
  roleIndexes : List ImportIndexOrigin
  selectedProviderHirRoots : List ProviderHirRootOrigin
  deriving DecidableEq, Repr

/-- An emitted finite table, with no claim that Lean can authenticate a Rust
pointer. The executed Rust owner checks and immutable input hashes are separate
source evidence. All joins remain typed and preserve raw Group incidence. -/
structure OriginTable where
  inputUtf8 : String
  sourceModule : String
  sourceFile : String
  physical : List PhysicalRow
  formals : List FormalRow
  wilds : List AdminWildRow
  names : List NameRow
  declarations : List DeclarationRow
  statements : List AdminStatementRow
  resolutions : List ResolutionRow
  groups : List GroupRow
  body : List BodyRow
  /-- none means unobserved caller preparation, never an empty Context. -/
  callerContext : Option CallerContextOrigin

/-- Disjoint typed source-owner keys. Finite reification uses their position
in the authenticated row lists; no arithmetic pairing convention is introduced. -/
inductive SiteKey where
  | physical (key : PhysicalKey)
  | formal (key : FormalKey)
  | wild (key : AdminWildKey)
  | statement (key : AdminStatementKey)
  | binding (key : DeclarationKey)
  deriving DecidableEq, Repr

/-- These are independent coordinate families, not an arithmetic coding. No
inhabitant is asserted to be the original allocation for the observed table. -/
structure OriginalCoordinates where
  physical : PhysicalKey → Site
  formal : FormalKey → Site
  wild : AdminWildKey → Site
  statement : AdminStatementKey → Site
  binding : DeclarationKey → Site
  name : NameKey → Name
  declaration : DeclarationKey → Declaration

def OriginalCoordinates.site (coordinates : OriginalCoordinates) : SiteKey → Site
  | .physical key => coordinates.physical key
  | .formal key => coordinates.formal key
  | .wild key => coordinates.wild key
  | .statement key => coordinates.statement key
  | .binding key => coordinates.binding key

def OriginTable.siteKeys (table : OriginTable) : List SiteKey :=
  table.physical.map (fun row => .physical row.key) ++
  table.formals.map (fun row => .formal row.key) ++
  table.wilds.map (fun row => .wild row.key) ++
  table.statements.map (fun row => .statement row.key) ++
  table.declarations.map (fun row => .binding row.key)

/-- Required exact laws of the finite owner-key representation. Declaring
these obligations supplies no concrete inhabitant and no caller Context. -/
structure CoordinateLaws (table : OriginTable) (coordinates : OriginalCoordinates) : Prop where
  sites : ∀ key, table.siteKeys[coordinates.site key]? = some key
  names : ∀ key, (table.names.map NameRow.key)[coordinates.name key]? = some key
  declarations : ∀ key, (table.declarations.map DeclarationRow.key)[coordinates.declaration key]? = some key
  sitesInjective : Function.Injective coordinates.site
  namesInjective : Function.Injective coordinates.name
  declarationsInjective : Function.Injective coordinates.declaration

/-- A provenance-level syntax tree. Group is retained until the checked table
projection; source erasure has no Group constructor. The statement coordinate
is distinct from the expression occurrence it contains. -/
inductive LocatedExpression where
  | name (site : PhysicalKey) (name : NameKey)
  | lambda (site : PhysicalKey) (formal : FormalKey) (wild : AdminWildKey)
      (name : NameKey) (body : LocatedExpression)
  | app (site : PhysicalKey) (callee argument : LocatedExpression)
  | group (site projected : PhysicalKey) (body : LocatedExpression)
  | block (site : PhysicalKey) (statement : AdminStatementKey)
      (first last : LocatedExpression)
  deriving Repr

def LocatedExpression.root : LocatedExpression → PhysicalKey
  | .name site _ | .lambda site _ _ _ _ | .app site _ _
  | .group site _ _ | .block site _ _ _ => site

def LocatedExpression.erase (coordinates : OriginalCoordinates) :
    LocatedExpression → Source .expression
  | .name site bindingName => .name ⟨coordinates.physical site, none⟩ (coordinates.name bindingName)
  | .lambda site formal wild bindingName body =>
      .lambda ⟨coordinates.physical site, none⟩
        ⟨coordinates.formal formal, coordinates.name bindingName, none, false⟩
        (.wild (coordinates.wild wild)) (body.erase coordinates)
  | .app site callee argument => .app ⟨coordinates.physical site, none⟩
      (callee.erase coordinates) (argument.erase coordinates)
  | .group _ _ body => body.erase coordinates
  | .block site statement first last => .block ⟨coordinates.physical site, none⟩
      (.statementsCons (.expressionS (coordinates.statement statement) (first.erase coordinates))
        .statementsNil) (last.erase coordinates)

/-- Constructor-by-constructor table-to-source relation. Group erasure requires
its actual typed edge and exact projected root; no successful correspondence
proposition or chosen Source is a constructor argument. Name/parameter joins
are explicit table membership, rather than same spelling. -/
inductive TableToSource (table : OriginTable) (coordinates : OriginalCoordinates) :
    LocatedExpression → Source .expression → Prop where
  | name (site name) (row : ResolutionRow) (physicalRow : PhysicalRow)
      (formalRow : FormalRow) (nameRow : NameRow)
      (hasPhysical : physicalRow ∈ table.physical) (physicalKey : physicalRow.key = site)
      (present : row ∈ table.resolutions) (atSite : row.occurrence = site)
      (resolved : row.name = name)
      (hasFormal : formalRow ∈ table.formals)
      (sameParameter : row.parameterOrdinal = formalRow.parameterOrdinal)
      (hasName : nameRow ∈ table.names) (nameKey : nameRow.key = name)
      (nameFormal : nameRow.owner = .parameter formalRow.key) :
      TableToSource table coordinates (.name site name)
        (.name ⟨coordinates.physical site, none⟩ (coordinates.name name))
  | lambda (site formal wild name body source) (formalRow : FormalRow)
      (wildRow : AdminWildRow) (nameRow : NameRow) (physicalRow : PhysicalRow)
      (hasPhysical : physicalRow ∈ table.physical) (physicalKey : physicalRow.key = site)
      (hasFormal : formalRow ∈ table.formals) (formalKey : formalRow.key = formal)
      (lambdaKey : formalRow.lambda = site)
      (hasWild : wildRow ∈ table.wilds) (wildKey : wildRow.key = wild)
      (wildFormal : wildRow.formal = formal)
      (hasName : nameRow ∈ table.names) (nameKey : nameRow.key = name)
      (nameFormal : nameRow.owner = .parameter formal)
      (child : TableToSource table coordinates body source) :
      TableToSource table coordinates (.lambda site formal wild name body)
        (.lambda ⟨coordinates.physical site, none⟩
          ⟨coordinates.formal formal, coordinates.name name, none, false⟩
          (.wild (coordinates.wild wild)) source)
  | app (site callee argument calleeSource argumentSource) (physicalRow : PhysicalRow)
      (hasPhysical : physicalRow ∈ table.physical) (physicalKey : physicalRow.key = site)
      (left : TableToSource table coordinates callee calleeSource)
      (right : TableToSource table coordinates argument argumentSource) :
      TableToSource table coordinates (.app site callee argument)
        (.app ⟨coordinates.physical site, none⟩ calleeSource argumentSource)
  | group (site projected body source) (edge : GroupRow) (physicalRow : PhysicalRow)
      (hasPhysical : physicalRow ∈ table.physical) (physicalKey : physicalRow.key = site)
      (present : edge ∈ table.groups) (raw : edge.group = site)
      (inner : edge.projected = projected) (root : body.root = projected)
      (child : TableToSource table coordinates body source) :
      TableToSource table coordinates (.group site projected body) source
  | block (site statement first last firstSource lastSource) (physicalRow : PhysicalRow)
      (statementRow : AdminStatementRow)
      (hasPhysical : physicalRow ∈ table.physical) (physicalKey : physicalRow.key = site)
      (hasStatement : statementRow ∈ table.statements)
      (statementKey : statementRow.key = statement) (statementBlock : statementRow.block = site)
      (statementOrder : statementRow.sourceOrder = 0)
      (statementExpression : statementRow.expression = first.root)
      (bodyOrder : table.body =
        [⟨0, first.root, .statementExpression⟩, ⟨1, last.root, .finalExpression⟩])
      (head : TableToSource table coordinates first firstSource)
      (tail : TableToSource table coordinates last lastSource) :
      TableToSource table coordinates (.block site statement first last)
        (.block ⟨coordinates.physical site, none⟩
          (.statementsCons (.expressionS (coordinates.statement statement) firstSource)
            .statementsNil) lastSource)

/-- The declaration edge retains its source-owned binding name and physical
Definition node. DeclarationRootOrdinal is provenance only; it does not become
OriginalSource.Declaration or a Context. -/
inductive TableToDeclaration (table : OriginTable) (coordinates : OriginalCoordinates) :
    DeclarationKey → LocatedExpression → Source .bindings → Prop where
  | binding (key name initializer source) (row : DeclarationRow)
      (physicalRow : PhysicalRow) (nameRow : NameRow)
      (hasDeclaration : row ∈ table.declarations) (declarationKey : row.key = key)
      (hasPhysical : physicalRow ∈ table.physical) (physicalKey : physicalRow.key = row.sourceNode)
      (hasName : nameRow ∈ table.names) (nameKey : nameRow.key = name)
      (nameOwner : nameRow.owner = .declaration key)
      (child : TableToSource table coordinates initializer source) :
      TableToDeclaration table coordinates key initializer
        (.binding (coordinates.binding key) (coordinates.name name) none source .bindingsNil)

-- OWNER_SCHEMA_END

/-- Partial, owner-table-derived representation. An absent row gives none;
there is no fresh-label convention or missing-row fallback. Each natural number
is a checked index into the serialized, authenticated typed owner row sequence. -/
def constructCoordinates (table : OriginTable) : Option OriginalCoordinates := do
  let definition ← table.siteKeys.findIdx? (fun key => decide (key = .physical .definition))
  let outerLambda ← table.siteKeys.findIdx? (fun key => decide (key = .physical .outerLambda))
  let outerBody ← table.siteKeys.findIdx? (fun key => decide (key = .physical .outerBody))
  let application ← table.siteKeys.findIdx? (fun key => decide (key = .physical .application))
  let rawCallee ← table.siteKeys.findIdx? (fun key => decide (key = .physical .rawCallee))
  let argument ← table.siteKeys.findIdx? (fun key => decide (key = .physical .argument))
  let innerLambda ← table.siteKeys.findIdx? (fun key => decide (key = .physical .innerLambda))
  let innerBody ← table.siteKeys.findIdx? (fun key => decide (key = .physical .innerBody))
  let sibling ← table.siteKeys.findIdx? (fun key => decide (key = .physical .sibling))
  let outerFormal ← table.siteKeys.findIdx? (fun key => decide (key = .formal .outer))
  let innerFormal ← table.siteKeys.findIdx? (fun key => decide (key = .formal .inner))
  let outerWild ← table.siteKeys.findIdx? (fun key => decide (key = .wild .outer))
  let innerWild ← table.siteKeys.findIdx? (fun key => decide (key = .wild .inner))
  let applicationStatement ← table.siteKeys.findIdx? (fun key => decide (key = .statement .application))
  let valueBinding ← table.siteKeys.findIdx? (fun key => decide (key = .binding .value))
  let declarationName ← (table.names.map NameRow.key).findIdx? (fun key => decide (key = .declaration))
  let outerName ← (table.names.map NameRow.key).findIdx? (fun key => decide (key = .outer))
  let innerName ← (table.names.map NameRow.key).findIdx? (fun key => decide (key = .inner))
  let valueDeclaration ← (table.declarations.map DeclarationRow.key).findIdx?
    (fun key => decide (key = .value))
  pure {
    physical := fun
      | .definition => definition
      | .outerLambda => outerLambda
      | .outerBody => outerBody
      | .application => application
      | .rawCallee => rawCallee
      | .argument => argument
      | .innerLambda => innerLambda
      | .innerBody => innerBody
      | .sibling => sibling
    formal := fun | .outer => outerFormal | .inner => innerFormal
    wild := fun | .outer => outerWild | .inner => innerWild
    statement := fun | .application => applicationStatement
    binding := fun | .value => valueBinding
    name := fun | .declaration => declarationName | .outer => outerName | .inner => innerName
    declaration := fun | .value => valueDeclaration }

/-- Lookup preservation itself proves functional/injective consistency; no
source freshness theorem or assertion of actual caller provenance is assumed. -/
theorem coordinate_laws_of_rows (table : OriginTable) (coordinates : OriginalCoordinates)
    (sites : ∀ key, table.siteKeys[coordinates.site key]? = some key)
    (names : ∀ key, (table.names.map NameRow.key)[coordinates.name key]? = some key)
    (declarations : ∀ key,
      (table.declarations.map DeclarationRow.key)[coordinates.declaration key]? = some key) :
    CoordinateLaws table coordinates := by
  refine ⟨sites, names, declarations, ?_, ?_, ?_⟩
  · intro first second same
    exact Option.some.inj ((sites first).symm.trans
      ((congrArg (fun index => table.siteKeys[index]?) same).trans (sites second)))
  · intro first second same
    exact Option.some.inj ((names first).symm.trans
      ((congrArg (fun index => (table.names.map NameRow.key)[index]?) same).trans (names second)))
  · intro first second same
    exact Option.some.inj ((declarations first).symm.trans
      ((congrArg (fun index => (table.declarations.map DeclarationRow.key)[index]?) same).trans
        (declarations second)))

/-- Checked source algebra, not authenticity of either table or coordinates. -/
theorem table_to_source_erasure {table : OriginTable} {coordinates : OriginalCoordinates}
    {expression : LocatedExpression} {source : Source .expression}
    (derived : TableToSource table coordinates expression source) :
    source = expression.erase coordinates := by
  induction derived <;> simp_all only [LocatedExpression.erase]

def innerTerm : LocatedExpression :=
  .lambda .innerLambda .inner .inner .inner (.name .innerBody .inner)
def argumentTerm : LocatedExpression := .name .argument .outer
def applicationTerm : LocatedExpression :=
  .app .application (.group .rawCallee .innerLambda innerTerm) argumentTerm
def bodyTerm : LocatedExpression :=
  .block .outerBody .application applicationTerm (.name .sibling .outer)
def fixtureTerm : LocatedExpression :=
  .lambda .outerLambda .outer .outer .outer bodyTerm

def bindingSource (coordinates : OriginalCoordinates) : Source .bindings :=
  .binding (coordinates.binding .value) (coordinates.name .declaration) none
    (fixtureTerm.erase coordinates) .bindingsNil

def outerFormal (coordinates : OriginalCoordinates) : Formal :=
  ⟨coordinates.formal .outer, coordinates.name .outer, none, false⟩

/-- Exactly the Context expression selected by the original outer Lambda
rule, universally over the genuine incoming Context. No empty root is chosen. -/
def innerContext (coordinates : OriginalCoordinates) (rootContext : Context) : Context :=
  OriginalSourceEvents.formalContext rootContext (outerFormal coordinates)
    (bodyTerm.erase coordinates)

/-- The sixth event owner is the inner invocation, reached through the complete
binding/outer Lambda/block/application tree. No numeric Site lookup is used. -/
def innerOwnerQuery (coordinates : OriginalCoordinates) (rootContext : Context)
    (rootRoute : Route) (rootAmbient : List ScopeEntry) : Option Owner :=
  ((owners rootRoute rootAmbient (sourceRules rootContext (bindingSource coordinates))).drop 5).head?

theorem inner_owner_available (coordinates : OriginalCoordinates) (rootContext : Context)
    (rootRoute : Route) (rootAmbient : List ScopeEntry) :
    (innerOwnerQuery coordinates rootContext rootRoute rootAmbient).isSome = true := by
  simp only [innerOwnerQuery, bindingSource, fixtureTerm, bodyTerm, applicationTerm,
    innerTerm, argumentTerm, LocatedExpression.erase, sourceRules, bindingsRulesK,
    expressionRulesK, statementsRulesK, statementRulesK]
  rfl

def innerOwner (coordinates : OriginalCoordinates) (rootContext : Context)
    (rootRoute : Route) (rootAmbient : List ScopeEntry) : Owner :=
  (innerOwnerQuery coordinates rootContext rootRoute rootAmbient).get
    (inner_owner_available coordinates rootContext rootRoute rootAmbient)

/-- The eight local inherited binders are computed by the real rule walk.
The two final pre-invocation binders belong to the inner Lambda itself. -/
def localAmbient (coordinates : OriginalCoordinates) (rootContext : Context)
    (rootRoute : Route) : List ScopeEntry :=
  (innerOwner coordinates rootContext rootRoute []).telescope.take 8

def innerIdentity (coordinates : OriginalCoordinates) (rootContext : Context)
    (rootRoute : Route) (rootAmbient : List ScopeEntry) : Identity :=
  ⟨coordinates.declaration .value,
    let scope := (innerOwner coordinates rootContext rootRoute rootAmbient).telescope
    scope.take (scope.length - 2),
    innerContext coordinates rootContext,
    coordinates.physical .innerLambda, coordinates.formal .inner,
    coordinates.wild .inner, coordinates.physical .innerBody, coordinates.name .inner⟩

theorem local_ambient_kinds (coordinates : OriginalCoordinates) (rootContext : Context)
    (rootRoute : Route) :
    (localAmbient coordinates rootContext rootRoute).map (fun entry => entry.binder.kind) =
      [.description, .viewLogic, .invocation, .receipt, .returnRebind, .shared,
       .eventProof, .viewLogic] := by
  simp only [localAmbient, innerOwner, innerOwnerQuery, bindingSource, fixtureTerm,
    bodyTerm, applicationTerm, innerTerm, argumentTerm, LocatedExpression.erase,
    sourceRules, bindingsRulesK, expressionRulesK, statementsRulesK, statementRulesK]
  rfl

theorem target_invocation_binder (coordinates : OriginalCoordinates) (rootContext : Context)
    (rootRoute : Route) (rootAmbient : List ScopeEntry) :
    (innerOwner coordinates rootContext rootRoute rootAmbient).binder =
      ⟨coordinates.physical .innerLambda, .invocation, 0⟩ := by
  simp only [innerOwner, innerOwnerQuery, bindingSource, fixtureTerm,
    bodyTerm, applicationTerm, innerTerm, argumentTerm, LocatedExpression.erase,
    sourceRules, bindingsRulesK, expressionRulesK, statementsRulesK, statementRulesK]
  rfl

theorem identity_source (coordinates : OriginalCoordinates) (rootContext : Context)
    (rootRoute : Route) (rootAmbient : List ScopeEntry) :
    (innerIdentity coordinates rootContext rootRoute rootAmbient).parameter.source =
      innerTerm.erase coordinates :=
  OriginalIdentityEntryOrigin.identity_source (innerIdentity coordinates rootContext rootRoute rootAmbient)

theorem identity_registration (coordinates : OriginalCoordinates) (rootContext : Context)
    (rootRoute : Route) (rootAmbient : List ScopeEntry) :
    (sourceEntries (innerContext coordinates rootContext)
      (innerTerm.erase coordinates)).head? =
      some (innerIdentity coordinates rootContext rootRoute rootAmbient).parameter.registration :=
  OriginalIdentityEntryOrigin.identity_registration (innerIdentity coordinates rootContext rootRoute rootAmbient)

theorem identity_body_binding (coordinates : OriginalCoordinates) (rootContext : Context)
    (rootRoute : Route) (rootAmbient : List ScopeEntry) :
    lookupBinding (OriginalFormalShared.bodyContext
      (innerIdentity coordinates rootContext rootRoute rootAmbient).parameter)
      (coordinates.name .inner) =
      some ({name := coordinates.name .inner, owner := coordinates.formal .inner, kind := .formal, entry := some .value, singleUse := true} : Binding) :=
  OriginalIdentityEntryOrigin.identity_name_binding (innerIdentity coordinates rootContext rootRoute rootAmbient)

theorem application_source (coordinates : OriginalCoordinates) (rootContext : Context)
    (rootRoute : Route) (rootAmbient : List ScopeEntry) :
    applicationTerm.erase coordinates =
      .app ⟨coordinates.physical .application, none⟩
        (innerIdentity coordinates rootContext rootRoute rootAmbient).parameter.source
        (argumentTerm.erase coordinates) := rfl

theorem application_owners (coordinates : OriginalCoordinates) (rootContext : Context)
    (rootRoute : Route) (rootAmbient : List ScopeEntry) :
    OriginalSourceEnvironment.sourceCallOwners (innerContext coordinates rootContext)
      (applicationTerm.erase coordinates) =
      .application (coordinates.physical .application) (innerContext coordinates rootContext)
        (coordinates.physical .innerLambda) (coordinates.physical .argument) ::
      (OriginalSourceEnvironment.sourceCallOwners (innerContext coordinates rootContext)
        (innerIdentity coordinates rootContext rootRoute rootAmbient).parameter.source ++
       OriginalSourceEnvironment.sourceCallOwners (innerContext coordinates rootContext)
        (argumentTerm.erase coordinates)) :=
  OriginalIdentityEntryOrigin.identity_application_owners
    (innerIdentity coordinates rootContext rootRoute rootAmbient)
    (coordinates.physical .application) (argumentTerm.erase coordinates)

theorem identity_invocation_owner (coordinates : OriginalCoordinates) (rootContext : Context)
    (rootRoute : Route) (rootAmbient : List ScopeEntry) :
    (sourceOwners (innerContext coordinates rootContext) (innerTerm.erase coordinates)).head? =
      some (lambdaInvocationOwner (coordinates.physical .innerLambda)
        (innerIdentity coordinates rootContext rootRoute rootAmbient).parameter.formal) :=
  OriginalIdentityEntryOrigin.identity_invocation_owner (innerIdentity coordinates rootContext rootRoute rootAmbient)

/-- The inherited prefix is extracted from the actual full-root owner,
without an empty fallback. Its complement remains the inner local suffix. -/
theorem target_scope_from_root (coordinates : OriginalCoordinates) (rootContext : Context)
    (rootRoute : Route) (rootAmbient : List ScopeEntry) :
    (innerOwner coordinates rootContext rootRoute rootAmbient).telescope =
      (innerIdentity coordinates rootContext rootRoute rootAmbient).ambient ++
        (innerOwner coordinates rootContext rootRoute rootAmbient).telescope.drop
          ((innerOwner coordinates rootContext rootRoute rootAmbient).telescope.length - 2) := by
  exact (List.take_append_drop _ _).symm

def innerDescription (coordinates : OriginalCoordinates) (rootContext : Context)
    (rootRoute : Route) : ScopeEntry :=
  (((innerOwner coordinates rootContext rootRoute []).telescope.drop 8).head?).get (by
    simp only [innerOwner, innerOwnerQuery, bindingSource, fixtureTerm, bodyTerm,
      applicationTerm, innerTerm, argumentTerm, LocatedExpression.erase, sourceRules,
      bindingsRulesK, expressionRulesK, statementRulesK, statementsRulesK]
    rfl)

/-- Actual frame payloads and event metadata, indexed by the computed source
owner. These are a caller/runtime input; source syntax cannot manufacture them. -/
structure OwnedFrame (s : OriginalSourceInterpretation.Sorts) (View : Type)
    (entry : ScopeEntry) where
  frame : Frame (OriginalSourceEnvironment.Payload s View)
  binder : frame.binder = entry.binder
  kind : frame.value.data.atKind entry.binder.kind

def telescopeFromOwnerFrames {s : OriginalSourceInterpretation.Sorts} {View : Type}
    (scope : List ScopeEntry)
    (frames : ∀ entry, entry ∈ scope → OwnedFrame s View entry) :
    OriginalParameterSemantics.Telescope s View scope :=
  match scope with
  | [] => .nil
  | head :: tail =>
      let first := frames head (by simp only [List.mem_cons, true_or])
      .cons head tail first.frame first.binder first.kind
        (telescopeFromOwnerFrames tail (fun entry present =>
          frames entry (List.mem_cons_of_mem head present)))

def introduction {s : OriginalSourceInterpretation.Sorts} {View : Type}
    (coordinates : OriginalCoordinates) (rootContext : Context)
    (rootRoute : Route) (rootAmbient : List ScopeEntry)
    (frames : ∀ entry, entry ∈
      (innerIdentity coordinates rootContext rootRoute rootAmbient).ambient →
        OwnedFrame s View entry) : OriginalFormalAdmission.Introduction s View :=
  (innerIdentity coordinates rootContext rootRoute rootAmbient).introduction
    (innerDescription coordinates rootContext rootRoute).route
    (telescopeFromOwnerFrames _ frames)

theorem introduction_scope_binders {s : OriginalSourceInterpretation.Sorts} {View : Type}
    (coordinates : OriginalCoordinates) (rootContext : Context)
    (rootRoute : Route) (rootAmbient : List ScopeEntry)
    (frames : ∀ entry, entry ∈
      (innerIdentity coordinates rootContext rootRoute rootAmbient).ambient →
        OwnedFrame s View entry) :
    (introduction coordinates rootContext rootRoute rootAmbient frames).telescope.frames.map Frame.binder =
      (innerIdentity coordinates rootContext rootRoute rootAmbient).ambient.map ScopeEntry.binder :=
  OriginalParameterSemantics.telescope_keeps_binders _

end YulangClosure.OriginalSourceOwnerReification
