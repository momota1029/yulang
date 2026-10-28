import Std

/-!
Resolved source syntax for the adopted SG source-rule construction.

Authority: `2026-10-08-source-generalize-definition.md` §2, selecting
`2026-10-08-source-generalize-definition-and-proof.md` §§3–5. The 13 expression,
11 pattern and 3 statement forms are the inventory in
`docs/yulang-source-type-safety-ja.tex`, `sec:source` and `sec:all-source`.

This is raw, finite source data. It contains no typing derivation, successful
constraint, complete local rule package, executable-safety predicate or choice
of semantic witness. IDs refer to the original resolved syntax/declaration
tables. An annotation ID retains the actual written syntax; it is never parsed
from an inferred type. Full original local meanings are deliberately not
replaced by the paper's smaller, effect-erased execution type judgment.
-/
namespace YulangClosure.OriginalSource

abbrev Site := Nat
abbrev Name := Nat
abbrev Declaration := Nat
abbrev Annotation := Nat
abbrev Label := Nat

inductive Entry where
  | value | computation
  deriving DecidableEq, Repr

/-- The role is selected by the *outer source annotation*, before body typing. -/
structure Formal where
  site : Site
  name : Name
  annotation : Option Annotation
  outerComputation : Bool
  deriving DecidableEq, Repr

def Formal.entry (formal : Formal) : Entry :=
  if formal.outerComputation then .computation else .value

inductive Literal where
  | unit
  | bool (value : Bool)
  | int (value : Int)
  | floatBits (bits : Nat)
  | string (value : String)
  | bytes (value : List Nat)
  | path (value : String)
  | character (value : String)
  deriving DecidableEq, Repr

inductive Category where
  | expression | pattern | statement
  | expressions | patterns | recordItems | patternFields
  | arms | operationArms | statements | bindings | optionalExpression
  deriving DecidableEq, Repr

/-- An annotation is attached to its original occurrence. The generator will
emit a real boundary after synthesizing that occurrence, rather than replace
its synthesized root or silently introduce a source annotation. -/
structure Mark where
  site : Site
  annotation : Option Annotation := none
  deriving DecidableEq, Repr

/-- Resolved OR branches can use distinct lexical identities for the same
source spelling. Keep the original merge map; numeric identity equality is
not a substitute for the resolver's lexical-name correspondence. This is
source data, whose original legitimacy remains a local rule premise. -/
structure PatternMerge where
  left : Name
  right : Name
  result : Name
  deriving DecidableEq, Repr

/-- All source constructors, including ordered list containers. Custom finite
containers keep recursive source-to-rule construction structurally recursive.
`reference` is the original Ref pattern, not allocation of mutable state. -/
inductive Source : Category → Type where
  | literal (mark : Mark) (value : Literal) : Source .expression
  | primitive (mark : Mark) (declaration : Declaration) : Source .expression
  | name (mark : Mark) (binding : Name) : Source .expression
  | app (mark : Mark) (callee argument : Source .expression) : Source .expression
  | refSet (mark : Mark) (reference value : Source .expression) : Source .expression
  | lambda (mark : Mark) (formal : Formal) (pattern : Source .pattern)
      (body : Source .expression) : Source .expression
  | tuple (mark : Mark) (elements : Source .expressions) : Source .expression
  | record (mark : Mark) (items : Source .recordItems) : Source .expression
  | polyVariant (mark : Mark) (tag : Label) (payloads : Source .expressions) :
      Source .expression
  | select (mark : Mark) (receiver : Source .expression) (member : Name) :
      Source .expression
  | caseE (mark : Mark) (scrutinee : Source .expression) (arms : Source .arms) :
      Source .expression
  | catchE (mark : Mark) (scrutinee : Source .expression)
      (valueArms : Source .arms) (operationArms : Source .operationArms)
      (originalArmOrder : List Site) : Source .expression
  | block (mark : Mark) (statements : Source .statements)
      (last : Source .expression) : Source .expression

  | wild (site : Site) : Source .pattern
  | litPattern (site : Site) (value : Literal) : Source .pattern
  | varPattern (site : Site) (name : Name) : Source .pattern
  | tuplePattern (site : Site) (children : Source .patterns) : Source .pattern
  | listPattern (site : Site) (prefixPatterns : Source .patterns)
      (rest : Option Name) (suffix : Source .patterns) : Source .pattern
  | recordPattern (site : Site) (fields : Source .patternFields)
      (spread : Option Name) : Source .pattern
  | variantPattern (site : Site) (tag : Label) (payloads : Source .patterns) : Source .pattern
  | conPattern (site : Site) (constructor : Declaration)
      (typeArguments : List Annotation) (payloads : Source .patterns) : Source .pattern
  | refPattern (site : Site) (definition : Name) : Source .pattern
  | asPattern (site : Site) (child : Source .pattern) (name : Name) : Source .pattern
  | orPattern (site : Site) (left right : Source .pattern)
      (merges : List PatternMerge) : Source .pattern

  | letS (site : Site) (recursive : Bool) (bindings : Source .bindings) : Source .statement
  | expressionS (site : Site) (expression : Source .expression) : Source .statement
  | moduleS (site : Site) (declaration : Declaration) (body : Source .statements) : Source .statement

  | expressionsNil : Source .expressions
  | expressionsCons (head : Source .expression) (tail : Source .expressions) : Source .expressions
  | patternsNil : Source .patterns
  | patternsCons (head : Source .pattern) (tail : Source .patterns) : Source .patterns
  | recordNil : Source .recordItems
  | recordField (site : Site) (label : Label) (value : Source .expression)
      (tail : Source .recordItems) : Source .recordItems
  | recordSpread (site : Site) (value : Source .expression)
      (tail : Source .recordItems) : Source .recordItems
  | patternFieldsNil : Source .patternFields
  | patternField (site : Site) (label : Label) (child : Source .pattern)
      (default : Source .optionalExpression) (tail : Source .patternFields) : Source .patternFields
  | armsNil : Source .arms
  | arm (site : Site) (pattern : Source .pattern) (guard : Source .optionalExpression)
      (body : Source .expression) (tail : Source .arms) : Source .arms
  | operationArmsNil : Source .operationArms
  | operationArm (site : Site) (operation : Declaration) (rigidTypeBinders : Nat)
      (payload continuation : Source .pattern)
      (guard : Source .optionalExpression) (body : Source .expression)
      (tail : Source .operationArms) : Source .operationArms
  | statementsNil : Source .statements
  | statementsCons (head : Source .statement) (tail : Source .statements) : Source .statements
  | bindingsNil : Source .bindings
  | binding (site : Site) (name : Name) (annotation : Option Annotation)
      (initializer : Source .expression) (tail : Source .bindings) : Source .bindings
  | noExpression : Source .optionalExpression
  | someExpression (expression : Source .expression) : Source .optionalExpression

def Source.site : {category : Category} → Source category → Site
  | _, .literal mark _ | _, .primitive mark _ | _, .name mark _
  | _, .app mark _ _ | _, .refSet mark _ _ | _, .lambda mark _ _ _
  | _, .tuple mark _ | _, .record mark _ | _, .polyVariant mark _ _
  | _, .select mark _ _ | _, .caseE mark _ _ | _, .catchE mark _ _ _ _
  | _, .block mark _ _ => mark.site
  | _, .wild site | _, .litPattern site _ | _, .varPattern site _
  | _, .tuplePattern site _ | _, .listPattern site _ _ _
  | _, .recordPattern site _ _ | _, .variantPattern site _ _
  | _, .conPattern site _ _ _ | _, .refPattern site _
  | _, .asPattern site _ _ | _, .orPattern site _ _ _
  | _, .letS site _ _ | _, .expressionS site _ | _, .moduleS site _ _
  | _, .recordField site _ _ _ | _, .recordSpread site _ _
  | _, .patternField site _ _ _ _ | _, .arm site _ _ _ _
  | _, .operationArm site _ _ _ _ _ _ _ | _, .binding site _ _ _ _ => site
  | _, .someExpression expression => expression.site
  | _, _ => 0

/-- Source binder inventory. OR publishes only the common resolved names.
This function is data construction, with no successful match or type premise. -/
def Source.binders : {category : Category} → Source category → List Name
  | _, .varPattern _ bindingName => [bindingName]
  | _, .tuplePattern _ children => children.binders
  | _, .listPattern _ first rest last => first.binders ++ rest.toList ++ last.binders
  | _, .recordPattern _ fields spread => fields.binders ++ spread.toList
  | _, .variantPattern _ _ children | _, .conPattern _ _ _ children => children.binders
  | _, .asPattern _ child bindingName => child.binders ++ [bindingName]
  | _, .orPattern _ _ _ merges => merges.map PatternMerge.result
  | _, .patternsCons head tail => head.binders ++ tail.binders
  | _, .patternField _ _ child _ tail => child.binders ++ tail.binders
  | _, .binding _ bindingName _ _ tail => bindingName :: tail.binders
  | _, .letS _ _ bindings => bindings.binders
  | _, .statementsCons head tail => head.binders ++ tail.binders
  | _, _ => []

inductive BindingKind where
  | external | formal | pattern | internal | local | continuation | published | family
  deriving DecidableEq, Repr

structure Binding where
  name : Name
  owner : Site
  kind : BindingKind
  component : Option Site := none
  annotation : Option Annotation := none
  entry : Option Entry := none
  singleUse : Bool := false
  deriving DecidableEq, Repr

abbrev Context := List Binding

def bindNames (context : Context) (owner : Site) (kind : BindingKind)
    (names : List Name) : Context :=
  names.map (fun name => {name := name, owner := owner, kind := kind}) ++ context

def lookupBinding (context : Context) (name : Name) : Option Binding :=
  context.find? (fun binding => binding.name = name)

/-- Retain each lexical introduction's own occurrence. Grouping or tuple
construction must not change the owner of its nested declarations. -/
def Source.bindingRecords : {category : Category} → Source category → List Binding
  | _, .varPattern site bindingName => [{name := bindingName, owner := site, kind := .pattern}]
  | _, .tuplePattern _ children => children.bindingRecords
  | _, .listPattern site first rest last =>
      first.bindingRecords ++ rest.toList.map (fun bindingName =>
        {name := bindingName, owner := site, kind := .pattern}) ++ last.bindingRecords
  | _, .recordPattern site fields spread =>
      fields.bindingRecords ++ spread.toList.map (fun bindingName =>
        {name := bindingName, owner := site, kind := .pattern})
  | _, .variantPattern _ _ children | _, .conPattern _ _ _ children => children.bindingRecords
  | _, .asPattern site child bindingName =>
      child.bindingRecords ++ [{name := bindingName, owner := site, kind := .pattern}]
  | _, .orPattern site _ _ merges => merges.map (fun merge =>
      {name := merge.result, owner := site, kind := .pattern})
  | _, .patternsCons head tail => head.bindingRecords ++ tail.bindingRecords
  | _, .patternField _ _ child _ tail => child.bindingRecords ++ tail.bindingRecords
  | _, .binding site bindingName _ _ tail =>
      {name := bindingName, owner := site, kind := .published} :: tail.bindingRecords
  | _, .letS _ _ bindings => bindings.bindingRecords
  | _, .statementsCons head tail => head.bindingRecords ++ tail.bindingRecords
  | _, _ => []

/-- Ordered immediate source references used by formation constraints. The
aggregate rule receives the real operands, not merely a container's dummy
site or a list of independently solved child types. -/
def Source.roots : {category : Category} → Source category → List Site
  | _, .expressionsNil | _, .patternsNil | _, .recordNil | _, .patternFieldsNil
  | _, .armsNil | _, .operationArmsNil | _, .statementsNil | _, .bindingsNil
  | _, .noExpression => []
  | _, .expressionsCons head tail => head.site :: tail.roots
  | _, .patternsCons head tail => head.site :: tail.roots
  | _, .recordField site _ _ tail | _, .recordSpread site _ tail => site :: tail.roots
  | _, .patternField site _ _ _ tail => site :: tail.roots
  | _, .arm _ _ _ body tail => body.site :: tail.roots
  | _, .operationArm _ _ _ _ _ _ body tail => body.site :: tail.roots
  | _, .statementsCons head tail => head.site :: tail.roots
  | _, .binding site _ _ _ tail => site :: tail.roots
  | _, .someExpression expression => [expression.site]
  | _, source => [source.site]

/-- Count original resolved uses, including defaults and latent bodies. This
is source syntax analysis, not a promise that the future Call succeeds. -/
def Source.nameCount (bindingName : Name) : {category : Category} → Source category → Nat
  | _, .name _ used | _, .refPattern _ used => if bindingName = used then 1 else 0
  | _, .app _ first last | _, .refSet _ first last =>
      first.nameCount bindingName + last.nameCount bindingName
  | _, .lambda _ _ pattern body => pattern.nameCount bindingName + body.nameCount bindingName
  | _, .tuple _ children | _, .record _ children | _, .polyVariant _ _ children
  | _, .tuplePattern _ children | _, .recordPattern _ children _
  | _, .variantPattern _ _ children | _, .conPattern _ _ _ children
  | _, .letS _ _ children | _, .moduleS _ _ children => children.nameCount bindingName
  | _, .select _ receiver _ | _, .asPattern _ receiver _
  | _, .expressionS _ receiver | _, .someExpression receiver => receiver.nameCount bindingName
  | _, .caseE _ first last | _, .block _ first last
  | _, .expressionsCons first last | _, .patternsCons first last
  | _, .recordField _ _ first last | _, .recordSpread _ first last
  | _, .statementsCons first last | _, .binding _ _ _ first last
  | _, .listPattern _ first _ last | _, .orPattern _ first last _ =>
      first.nameCount bindingName + last.nameCount bindingName
  | _, .catchE _ first middle last _ | _, .patternField _ _ first middle last =>
      first.nameCount bindingName + middle.nameCount bindingName + last.nameCount bindingName
  | _, .arm _ first second third fourth =>
      first.nameCount bindingName + second.nameCount bindingName +
        third.nameCount bindingName + fourth.nameCount bindingName
  | _, .operationArm _ _ _ first continuation second third fourth =>
      first.nameCount bindingName + continuation.nameCount bindingName +
        second.nameCount bindingName + third.nameCount bindingName + fourth.nameCount bindingName
  | _, _ => 0

inductive Rule where
  | lit | primitive | name | app | refSet | lambda | tuple | record | polyVariant
  | select | caseE | catchE | block
  | wild | litPattern | varPattern | tuplePattern | listPattern | recordPattern
  | variantPattern | conPattern | refPattern | asPattern | orPattern
  | letS | expressionS | moduleS
  | recordField | recordSpread | patternField | arm | operationArm | binding
  | annotation | parameterEntry | registerGroup | sequence | empty
  | newUse | alias | view | run | join | sequentialBind | clientConstraint
  deriving DecidableEq, Repr

inductive BinderKind where
  | description | shared | viewLogic | invocation | receipt | returnRebind
  | rigidOperation | response | eventProof | publishedInstance | oneShot
  deriving DecidableEq, Repr

structure Binder where
  site : Site
  kind : BinderKind
  /-- Original declaration/packet arity where relevant; not fresh runtime IDs. -/
  arity : Nat := 0
  deriving DecidableEq, Repr

/-- Original local relation names. No constructor denotes source typing,
Generalize success, complete source adequacy, or arbitrary semantic inclusion.
An interpretation must use the independent original meanings of these names. -/
inductive AtomKind where
  | literalDeclaration | primitiveDeclarationInstance
  | resolvedSameBinding | exactWholeInstance | computedFetchOnce
  | descriptorFormation | wholeArgumentCompatibility | completeCallCertificate
  | sourceCallIncidence | roleAndInitialCallOrigin | callableImage
  | invariantReferenceProtocol | referenceResult
  | sourceFormalRole | captureWholeEnvironment | completeBodyConsumer
  | closureFormation | receiptFormation | entryForceReturnRebind | retainedEntry
  | tupleFormation | orderedRecordFormation | variantTagArity
  | retainedSelection | selectionQualifiedChildren | selectionWholeInstance
  | caseOrderedAttempts | branchJoin | shallowPacketInstance
  | shallowResidualCoverage | shallowLatentPreservation
  | blockFinalRoot | literalComparison | patternBinding | tupleArity
  | listLengthAndRest | visibleRecordPresence | variantPayload | nominalInvariant
  | referencePatternComparison | sameInputAlias | orCommonEnvironment | orderedOrAttempt
  | sourceLetRegistration | recursiveJointMemberWorld | oneShotInitializer
  | publicationFinalRoot | sourceModuleLinking
  | expressionDiscard | visibleFieldUpdate | visibleSpreadUpdate
  | defaultBeforeBinding | defaultAndInputJoin | patternAttempt | boolGuard
  | operationRigidInstance | rawContinuationContract | originalOutsideArmContext
  | actualReturnOrPendingSuffix | finalAnnotationFormation
  | originalNewInstance | sameMonomorphicAlias | actualRunInterface | clientPredicate
  | originalCheckingPrimitive | originalConversionPrimitive | checkConstructorShape
  deriving DecidableEq, Repr

/-- A local atom's operands are source-owned references, not a supplied proof
or subtree. All its fields are interpreted on one environment/whole tuple. -/
structure Atom where
  kind : AtomKind
  site : Site
  context : Context
  operands : List Site := []
  order : List Site := []
  names : List Name := []
  declaration : Option Declaration := none
  annotation : Option Annotation := none
  annotations : List Annotation := []
  labels : List Label := []
  flag : Option Bool := none
  arity : Nat := 0
  merges : List PatternMerge := []
  literal : Option Literal := none
  entry : Option Entry := none
  binding : Option Binding := none
  deriving DecidableEq, Repr

def atom (kind : AtomKind) (site : Site) (context : Context)
    (operands : List Site := []) : Atom := {kind, site, context, operands}

inductive CheckMode where
  | value | computation | domain | observation | equality
  deriving DecidableEq, Repr

/-- Distinct ports at one occurrence remain distinct even when their solved
types coincide. In particular the written target is not the synthesis port. -/
inductive Port where
  | synthesis | finalRoot | writtenTarget | descriptor | callableImage | returnedValue
  | formalCarrier | bodyConsumer | invocationReturn | branchJoin | patternInput
  | referenceContent
  deriving DecidableEq, Repr

structure Endpoint where
  site : Site
  port : Port
  deriving DecidableEq, Repr

/-- A complete same-tuple logical checking goal. Concrete adapters use the
separate Boundary judgment below, which has no transitivity constructor. -/
structure CheckGoal where
  mode : CheckMode
  site : Site
  context : Context
  lower : Endpoint
  upper : Endpoint
  deriving DecidableEq, Repr

inductive Premise where
  | atom (value : Atom)
  | checking (goal : CheckGoal)
  | boundary (site : Site) (context : Context) (lower upper : Endpoint)
  deriving DecidableEq, Repr

mutual
/-- These frames record source rule structure. They contain only local
premise syntax, never a proof, and are constructed below from Source. -/
inductive RuleTree where
  | rule (rule : Rule) (site : Site) (context : Context)
      (premises : List Premise) (children : RuleForest)
  | existsE (binder : Binder) (body : RuleTree)
  | forallE (binder : Binder) (body : RuleTree)
  /-- Record the source initializer's actual entry before its internal events. -/
  | initializerE (site : Site) (body : RuleTree)
  /-- The actual RHS event is open during source checking and fixed when
  replaying the description of an already published initialization. -/
  | executionE (binder : Binder) (body : RuleTree)
  /-- Reference one original shared strategy; never allocate it per view. -/
  | sharedE (binder : Binder) (body : RuleTree)
  /-- Record authentic constructor outputs at the original publication. -/
  | publishGroup (bindings : List (Name × Site)) (body : RuleTree)
  /-- Restore the original captured source/event anchor for a description. -/
  | atPublication (binding : Name) (body : RuleTree)
  | aliasPublication (original aliasName : Name) (body : RuleTree)
  | choice (site : Site) (left right : RuleTree)

inductive RuleForest where
  | nil
  | cons (head : RuleTree) (tail : RuleForest)
end

namespace RuleForest
def one (tree : RuleTree) : RuleForest := .cons tree .nil
def two (first second : RuleTree) : RuleForest := .cons first (.cons second .nil)
def three (first second third : RuleTree) : RuleForest :=
  .cons first (.cons second (.cons third .nil))
end RuleForest

/-- A referenced source definition retains its original raw code and
environment. It contains no already-proved source judgment. The binding
anchor is fixed across independent description instances. -/
structure Definition where
  declaration : Declaration
  anchor : Name
  context : Context
  source : Source .expression

/-- The finite client grammar of SG §3.4/§7. `newUse` names raw source data;
`alias` and `view` refer to an existing complete instance, and `run` retains
its original actual event operands. None supplies a successful query. -/
inductive Client where
  | done (site : Site)
  | newUse (site : Site) (definition : Definition) (instanceName : Name) (rest : Client)
  | alias (site : Site) (original aliasName : Name) (rest : Client)
  | view (site : Site) (original : Name) (target : Annotation) (rest : Client)
  | run (site : Site) (original : Name) (eventOperands : List Site) (rest : Client)
  | join (site : Site) (left right : Client)
  | bind (site : Site) (bindingName : Name) (first rest : Client)
  /-- A reference to an independently typed client predicate W at its
  original scope. This is not a seventh operational client instruction. -/
  | constrain (site : Site) (declaration : Declaration) (operands : List Site) (rest : Client)

end YulangClosure.OriginalSource
