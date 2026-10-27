import YulangClosure.OriginalIdentityEntryOrigin

/-!
# Candidate inline identity constructor interpretation

This is a source-algebra construction, not an authenticated Rust frontend
extraction. CandidateOwner and Node are raw representations. No theorem here
asserts that an arbitrary inhabitant comes from ParsedFile, SourceNodeKey,
HirParameterId or LocalSourceIndex. The first open owner equation is extraction
from those actual immutable owners into CandidateInline, retaining the exact
Lambda/token, resolved Parameter(id), body occurrence and enclosing Apply.

Physical nodes, inline binder tokens and administrative wildcard coordinates
are different constructors. In particular no Wild CST node is postulated.
Original Nat sites are a concrete erasure; provenance stays in the indexed
CandidateInline/Expansion and cannot be recovered by comparing bare Nats.
No injectivity, global freshness, numeric site inequality or runtime table is
assumed. The numerical encoding below is a candidate convention, not an
adopted frontend allocation policy.

The source rules are the unchanged OriginalSource constructors and the
reviewed OriginalIdentityEntryOrigin equations. The arbitrary original
argument, declaration, ambient telescope and surrounding Context are retained.
No Build solution, selected runtime Closure, generated label, admission,
source/native simulation or whole-language theorem follows from this algebra.
-/
namespace YulangClosure.OriginalInlineIdentityInterpretation

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalSourceEvents OriginalParameterWorld OriginalFormalShared
open OriginalIdentityRealization

/-- Candidate identity tags only; authentic pointer/root ownership is OPEN. -/
structure CandidateOwner where
  artifact : Nat
  parseRoot : Nat
  sourceRoot : Nat
  deriving DecidableEq, Repr

/-- A physical syntax locator, never a published occurrence ordinal. -/
structure Node (owner : CandidateOwner) where
  path : List Nat
  deriving DecidableEq, Repr

structure InlineToken {owner : CandidateOwner} (lambda : Node owner) where
  start : Nat
  stop : Nat
  spelling : String
  deriving DecidableEq, Repr

/-- Root-indexed parameter identity; spelling is deliberately absent. -/
structure ParameterId (owner : CandidateOwner) where
  ordinal : Nat
  deriving DecidableEq, Repr

inductive Coordinate (owner : CandidateOwner) where
  | physical (node : Node owner)
  | formal (lambda : Node owner) (token : InlineToken lambda)
  | administrativeWild (lambda : Node owner) (token : InlineToken lambda)
  deriving DecidableEq, Repr

/-- One candidate constructor instance. Its body is the parameter Name and
its callee is the inline Lambda; actual frontend incidence is not an axiom. -/
structure CandidateInline (owner : CandidateOwner) where
  applyNode : Node owner
  lambdaNode : Node owner
  binder : InlineToken lambdaNode
  parameter : ParameterId owner
  nameNode : Node owner
  deriving Repr

/-- A concrete arithmetic coding, used only for erasure into original Nat. -/
def pairCode (first second : Nat) : Nat :=
  (first + second) * (first + second + 1) + 2 * second

def pathCode : List Nat → Nat
  | [] => 0
  | step :: tail => pairCode step (pathCode tail) + 1

def ownerCode (owner : CandidateOwner) : Nat :=
  pairCode owner.artifact (pairCode owner.parseRoot owner.sourceRoot)

def coordinateCode {owner : CandidateOwner} : Coordinate owner → Site
  | .physical node => pairCode (ownerCode owner) (pairCode 0 (pathCode node.path))
  | .formal lambda token => pairCode (ownerCode owner)
      (pairCode 1 (pairCode (pathCode lambda.path) (pairCode token.start token.stop)))
  | .administrativeWild lambda token => pairCode (ownerCode owner)
      (pairCode 2 (pairCode (pathCode lambda.path) (pairCode token.start token.stop)))

def parameterName {owner : CandidateOwner} (parameter : ParameterId owner) : Name :=
  pairCode (ownerCode owner) parameter.ordinal

def lambdaCoordinate {owner : CandidateOwner} (origin : CandidateInline owner) : Coordinate owner :=
  .physical origin.lambdaNode

def formalCoordinate {owner : CandidateOwner} (origin : CandidateInline owner) : Coordinate owner :=
  .formal origin.lambdaNode origin.binder

def patternCoordinate {owner : CandidateOwner} (origin : CandidateInline owner) : Coordinate owner :=
  .administrativeWild origin.lambdaNode origin.binder

def nameCoordinate {owner : CandidateOwner} (origin : CandidateInline owner) : Coordinate owner :=
  .physical origin.nameNode

def applyCoordinate {owner : CandidateOwner} (origin : CandidateInline owner) : Coordinate owner :=
  .physical origin.applyNode

/-- Ambient source data is not inferred from a spelling or a runtime table. -/
structure Expansion {owner : CandidateOwner} (origin : CandidateInline owner) where
  declaration : Declaration
  ambient : List ScopeEntry
  context : Context

def Expansion.identity {owner : CandidateOwner} {origin : CandidateInline owner}
    (expansion : Expansion origin) : Identity :=
  ⟨expansion.declaration, expansion.ambient, expansion.context,
    coordinateCode (lambdaCoordinate origin), coordinateCode (formalCoordinate origin),
    coordinateCode (patternCoordinate origin), coordinateCode (nameCoordinate origin),
    parameterName origin.parameter⟩

def Expansion.application {owner : CandidateOwner} {origin : CandidateInline owner}
    (expansion : Expansion origin) (argument : Source .expression) : Source .expression :=
  .app ⟨coordinateCode (applyCoordinate origin), none⟩ expansion.identity.parameter.source argument

abbrev Lexical (owner : CandidateOwner) := List (String × ParameterId owner)

def resolve {owner : CandidateOwner} (lexical : Lexical owner) (spelling : String) :
    Option (ParameterId owner) :=
  (lexical.find? (fun entry => entry.1 == spelling)).map Prod.snd

theorem pushed_body_resolution {owner : CandidateOwner} (origin : CandidateInline owner)
    (prior : Lexical owner) :
    resolve ((origin.binder.spelling, origin.parameter) :: prior) origin.binder.spelling =
      some origin.parameter := by
  simp [resolve]

theorem nested_same_spelling {owner : CandidateOwner} (outer inner : CandidateInline owner)
    (prior : Lexical owner) :
    resolve ((outer.binder.spelling, inner.parameter) ::
      (outer.binder.spelling, outer.parameter) :: prior) outer.binder.spelling =
      some inner.parameter := by
  simp [resolve]

/-- Restoring the prior stack preserves every previous resolution. This is
candidate list algebra; Rust Work::Restore refinement remains OPEN. -/
theorem restored_resolution {owner : CandidateOwner} (prior : Lexical owner)
    (spelling : String) (parameter : ParameterId owner) (query : String) :
    resolve (((spelling, parameter) :: prior).drop 1) query = resolve prior query := rfl

theorem pattern_is_administrative {owner : CandidateOwner} (origin : CandidateInline owner)
    (node : Node owner) : patternCoordinate origin ≠ Coordinate.physical node := by
  intro equality
  cases equality

theorem formal_is_not_pattern {owner : CandidateOwner} (origin : CandidateInline owner) :
    formalCoordinate origin ≠ patternCoordinate origin := by
  intro equality
  cases equality

theorem formal_constructor {owner : CandidateOwner} {origin : CandidateInline owner}
    (expansion : Expansion origin) :
    expansion.identity.parameter.formal =
      ⟨coordinateCode (formalCoordinate origin), parameterName origin.parameter, none, false⟩ := rfl

theorem pattern_constructor {owner : CandidateOwner} {origin : CandidateInline owner}
    (expansion : Expansion origin) :
    expansion.identity.parameter.pattern = .wild (coordinateCode (patternCoordinate origin)) := rfl

theorem body_constructor {owner : CandidateOwner} {origin : CandidateInline owner}
    (expansion : Expansion origin) :
    expansion.identity.parameter.body =
      .name ⟨coordinateCode (nameCoordinate origin), none⟩ (parameterName origin.parameter) := rfl

theorem source_constructor {owner : CandidateOwner} {origin : CandidateInline owner}
    (expansion : Expansion origin) :
    expansion.identity.parameter.source =
      .lambda ⟨coordinateCode (lambdaCoordinate origin), none⟩
        ⟨coordinateCode (formalCoordinate origin), parameterName origin.parameter, none, false⟩
        (.wild (coordinateCode (patternCoordinate origin)))
        (.name ⟨coordinateCode (nameCoordinate origin), none⟩ (parameterName origin.parameter)) :=
  OriginalIdentityEntryOrigin.identity_source expansion.identity

theorem application_constructor {owner : CandidateOwner} {origin : CandidateInline owner}
    (expansion : Expansion origin) (argument : Source .expression) :
    expansion.application argument =
      .app ⟨coordinateCode (applyCoordinate origin), none⟩
        expansion.identity.parameter.source argument := rfl

theorem pattern_binds_nothing {owner : CandidateOwner} {origin : CandidateInline owner}
    (expansion : Expansion origin) :
    expansion.identity.parameter.pattern.bindingRecords = [] ∧
      expansion.identity.parameter.pattern.binders = [] := ⟨rfl, rfl⟩

theorem body_context {owner : CandidateOwner} {origin : CandidateInline owner}
    (expansion : Expansion origin) :
    bodyContext expansion.identity.parameter =
      {name := parameterName origin.parameter, owner := coordinateCode (formalCoordinate origin),
       kind := .formal, entry := some .value, singleUse := true} :: expansion.context := by
  simp [Expansion.identity, Identity.parameter, bodyContext, OriginalFormalShared.formalContext,
    Source.bindingRecords, Source.nameCount, Formal.entry]

/-- The generated source Name resolves to the same parameter selected by
candidate lexical push, including arbitrary shadowed ambient bindings. -/
theorem binding_preservation {owner : CandidateOwner} {origin : CandidateInline owner}
    (expansion : Expansion origin) (prior : Lexical owner) :
    (resolve ((origin.binder.spelling, origin.parameter) :: prior) origin.binder.spelling).map
        parameterName = some (parameterName origin.parameter) ∧
    lookupBinding (bodyContext expansion.identity.parameter) (parameterName origin.parameter) =
      some {name := parameterName origin.parameter, owner := coordinateCode (formalCoordinate origin),
            kind := .formal, entry := some .value, singleUse := true} := by
  constructor
  · rw [pushed_body_resolution]
    rfl
  · exact OriginalIdentityEntryOrigin.identity_name_binding expansion.identity

theorem registration {owner : CandidateOwner} {origin : CandidateInline owner}
    (expansion : Expansion origin) :
    (sourceEntries expansion.context expansion.identity.parameter.source).head? =
      some expansion.identity.parameter.registration :=
  OriginalIdentityEntryOrigin.identity_registration expansion.identity

theorem closure_owner {owner : CandidateOwner} {origin : CandidateInline owner}
    (expansion : Expansion origin) :
    (sourceCallOwners expansion.context expansion.identity.parameter.source).head? =
      some (.closure (coordinateCode (lambdaCoordinate origin)) expansion.context
        (coordinateCode (formalCoordinate origin)) (coordinateCode (patternCoordinate origin))
        (coordinateCode (nameCoordinate origin))) :=
  OriginalIdentityEntryOrigin.identity_closure_owner expansion.identity

theorem application_owners {owner : CandidateOwner} {origin : CandidateInline owner}
    (expansion : Expansion origin) (argument : Source .expression) :
    sourceCallOwners expansion.context (expansion.application argument) =
      .application (coordinateCode (applyCoordinate origin)) expansion.context
        (coordinateCode (lambdaCoordinate origin)) argument.site ::
        (sourceCallOwners expansion.context expansion.identity.parameter.source ++
          sourceCallOwners expansion.context argument) :=
  OriginalIdentityEntryOrigin.identity_application_owners expansion.identity
    (coordinateCode (applyCoordinate origin)) argument

theorem generated_lambda {owner : CandidateOwner} {origin : CandidateInline owner}
    (expansion : Expansion origin) :
    sourceRules expansion.context expansion.identity.parameter.source =
      lambdaTree expansion.identity.parameter :=
  actual_lambda_tree expansion.identity.parameter

theorem value_entry {owner : CandidateOwner} {origin : CandidateInline owner}
    (expansion : Expansion origin) : expansion.identity.parameter.formal.entry = .value :=
  identity_value_entry expansion.identity


theorem registration_operands {owner : CandidateOwner} {origin : CandidateInline owner}
    (expansion : Expansion origin) :
    expansion.identity.parameter.registration.site = coordinateCode (formalCoordinate origin) ∧
    expansion.identity.parameter.registration.entry = .value ∧
    expansion.identity.parameter.registration.role.annotation = none ∧
    expansion.identity.parameter.registration.role.entry = some .value ∧
    expansion.identity.parameter.registration.receipt.operands =
      [coordinateCode (lambdaCoordinate origin), coordinateCode (patternCoordinate origin),
       coordinateCode (nameCoordinate origin)] :=
  OriginalIdentityEntryOrigin.identity_registration_operands expansion.identity

theorem name_rule {owner : CandidateOwner} {origin : CandidateInline owner}
    (expansion : Expansion origin) :
    sourceRules (bodyContext expansion.identity.parameter) expansion.identity.parameter.body =
      .rule .name (coordinateCode (nameCoordinate origin)) (bodyContext expansion.identity.parameter)
        [.atom {(atom .resolvedSameBinding (coordinateCode (nameCoordinate origin))
          (bodyContext expansion.identity.parameter)) with
          names := [parameterName origin.parameter], binding :=
            lookupBinding (bodyContext expansion.identity.parameter) (parameterName origin.parameter)},
         .atom {(atom .computedFetchOnce (coordinateCode (nameCoordinate origin))
          (bodyContext expansion.identity.parameter)) with
          names := [parameterName origin.parameter], binding :=
            lookupBinding (bodyContext expansion.identity.parameter) (parameterName origin.parameter)}]
        .nil :=
  OriginalIdentityEntryOrigin.identity_name_rule expansion.identity

theorem application_ports {owner : CandidateOwner} {origin : CandidateInline owner}
    (expansion : Expansion origin) (argument : Source .expression) :
    ∃ atoms, sourceRules expansion.context (expansion.application argument) =
      .existsE ⟨coordinateCode (applyCoordinate origin), .viewLogic, 0⟩
        (.rule .app (coordinateCode (applyCoordinate origin)) expansion.context
          (atoms ++
            [.checking ⟨.value, coordinateCode (applyCoordinate origin), expansion.context,
              ⟨coordinateCode (lambdaCoordinate origin), .returnedValue⟩,
              ⟨coordinateCode (applyCoordinate origin), .descriptor⟩⟩,
             .checking ⟨.computation, coordinateCode (applyCoordinate origin), expansion.context,
              ⟨coordinateCode (applyCoordinate origin), .callableImage⟩,
              ⟨coordinateCode (applyCoordinate origin), .synthesis⟩⟩])
          (.two (sourceRules expansion.context expansion.identity.parameter.source)
            (sourceRules expansion.context argument))) :=
  OriginalIdentityEntryOrigin.identity_application_ports expansion.identity
    (coordinateCode (applyCoordinate origin)) argument

theorem value_entry_sequence {owner : CandidateOwner} {origin : CandidateInline owner}
    (expansion : Expansion origin) :
    enteredBody expansion.identity.parameter =
      .executionE ⟨coordinateCode (formalCoordinate origin), .returnRebind, 0⟩
        (.sharedE ⟨coordinateCode (formalCoordinate origin), .shared, 0⟩
          (checkedBody expansion.identity.parameter)) :=
  OriginalIdentityEntryOrigin.identity_value_entry_sequence expansion.identity

end YulangClosure.OriginalInlineIdentityInterpretation
