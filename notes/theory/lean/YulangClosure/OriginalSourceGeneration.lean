import YulangClosure.OriginalSourceSyntax

/-!
Constructor-directed implementation of the adopted SG §§3–6 construction.

`sourceRules` accepts the raw 13/11/3 syntax. It does not accept a caller's
rule tree, source derivation, solver success or chosen semantic witness.
`Judgment` is the independent finite local-rule proof grammar. `Formula`,
`Build` and `Satisfies` are separate generated syntax and its interpretation.
The reconstruction below actually inducts over every rule and binder.

The semantic parameter is the original LOCAL kernel, including original
admission and actual conversion relations. No field has the whole source
judgment, arbitrary Function inclusion, Generalize success or native solver
acceptance as its result. A concrete original interpretation and native
success-to-satisfaction are additional obligations, not definitions here.
-/
namespace YulangClosure.OriginalSource

private def premises (kinds : List AtomKind) (site : Site) (context : Context)
    (operands : List Site := []) : List Premise :=
  kinds.map (fun kind => .atom (atom kind site context operands))

private def node (rule : Rule) (site : Site) (context : Context)
    (kinds : List AtomKind) (operands : List Site := [])
    (children : RuleForest := .nil) : RuleTree :=
  .rule rule site context (premises kinds site context operands) children

private def endpoint (site : Site) (port : Port := .finalRoot) : Endpoint :=
  ⟨site, port⟩

private def check (mode : CheckMode) (site : Site) (context : Context)
    (lower upper : Endpoint) : Premise := .checking ⟨mode, site, context, lower, upper⟩

private def annotated (mark : Mark) (context : Context) (body : RuleTree) : RuleTree :=
  match mark.annotation with
  | none => body
  | some target =>
      .rule .annotation mark.site context
        [.atom { (atom .finalAnnotationFormation mark.site context) with
          annotation := some target },
         .boundary mark.site context (endpoint mark.site .synthesis)
           (endpoint mark.site .writtenTarget)] (.one body)

/-- The original ordered suffix receives its predecessor's *actual*
Return/rebind or request/response telescope. Its admissible inputs are fixed
by the independent original kernel, not by whether the suffix is typable. -/
private def suffix (owner : Site) (body : RuleTree) : RuleTree :=
  .executionE ⟨owner, .returnRebind, 0⟩ body

private def patternContext {category : Category} (context : Context)
    (source : Source category) : Context :=
  source.bindingRecords.filter (fun binding =>
    !(context.any (fun prior => prior.name == binding.name))) ++ context

private def statementContext (context : Context)
    (source : Source .statement) : Context :=
  source.bindingRecords ++ context

/-- The selected Role_0 theorem is for an actual one-use, unannotated formal
applied to an ordinary rebound formal Name. It is not a policy for every
application. These flags are constructed at Lambda registration below. -/
def singletonFormalCall (context : Context)
    (callee argument : Source .expression) : Bool :=
  match callee, argument with
  | .name calleeMark calleeName, .name argumentMark argumentName =>
      match lookupBinding context calleeName, lookupBinding context argumentName with
      | some f, some a =>
          calleeMark.annotation.isNone && argumentMark.annotation.isNone &&
          f.kind == .formal && f.annotation.isNone && f.entry == some .value && f.singleUse &&
          a.kind == .formal && a.entry == some .value
      | _, _ => false
  | _, _ => false

mutual
/-- Finite source registration. The equations below are the rule inventory;
there is no fallback accepting an unregistered local rule package.

Argument derivation under App denotes the original *inert whole code
interface*. `wholeArgumentCompatibility` and `callableImage` retain that
interface, not its printed Comp summary. The call's original complete tuple
and all its coupled effect obligations occur in the same scoped rule.
-/
def sourceRules (context : Context) : {category : Category} → Source category → RuleTree
  | _, .literal mark value =>
      annotated mark context <|
        .rule .lit mark.site context
          [.atom { (atom .literalDeclaration mark.site context) with literal := some value }]
          .nil
  | _, .primitive mark declaration =>
      annotated mark context <|
        .rule .primitive mark.site context
          [.atom { (atom .primitiveDeclarationInstance mark.site context) with
            declaration := some declaration }] .nil
  | _, .name mark bindingName =>
      let binding := lookupBinding context bindingName
      let localRule := .rule .name mark.site context
          [.atom { (atom .resolvedSameBinding mark.site context) with
            names := [bindingName], binding := binding },
           .atom { (atom .computedFetchOnce mark.site context) with
            names := [bindingName], binding := binding }]
          .nil
      annotated mark context <|
        match binding.map Binding.kind with
        | some .published | some .family =>
            .existsE ⟨mark.site, .publishedInstance, 0⟩ <|
              .rule .name mark.site context
                [.atom { (atom .exactWholeInstance mark.site context) with
                  names := [bindingName], binding := binding }] (.one localRule)
        | _ => localRule
  | _, .app mark callee argument =>
      let callKinds := [.descriptorFormation, .wholeArgumentCompatibility,
        .completeCallCertificate, .sourceCallIncidence, .callableImage] ++
        if singletonFormalCall context callee argument then [.roleAndInitialCallOrigin] else []
      annotated mark context <|
        .existsE ⟨mark.site, .viewLogic, 0⟩ <|
          .rule .app mark.site context
            (premises callKinds mark.site context [callee.site, argument.site] ++
             [check .value mark.site context (endpoint callee.site .returnedValue)
                (endpoint mark.site .descriptor),
              check .computation mark.site context (endpoint mark.site .callableImage)
                (endpoint mark.site .synthesis)])
            (.two (sourceRules context callee) (sourceRules context argument))
  | _, .refSet mark reference value =>
      annotated mark context <|
        .rule .refSet mark.site context
          (premises [.invariantReferenceProtocol, .referenceResult]
            mark.site context [reference.site, value.site] ++
           [.boundary mark.site context (endpoint value.site)
             (endpoint reference.site .referenceContent)])
          (.two (sourceRules context reference) (suffix reference.site (sourceRules context value)))
  | _, .lambda mark formal pattern body =>
      let formalContext :=
        {name := formal.name, owner := formal.site, kind := BindingKind.formal,
          annotation := formal.annotation, entry := some formal.entry,
          singleUse := body.nameCount formal.name == 1} :: context
      let bodyContext := patternContext formalContext pattern
      let entryPremises :=
        [.atom { (atom .sourceFormalRole formal.site formalContext) with
          annotation := formal.annotation, entry := some formal.entry }] ++
        premises (match formal.entry with
          | .value => [.receiptFormation, .entryForceReturnRebind]
          | .computation => [.receiptFormation, .retainedEntry]) formal.site formalContext
          [mark.site, pattern.site, body.site]
      let checkedBody := .rule .sequence formal.site formalContext []
        (.two (sourceRules formalContext pattern)
          (.existsE ⟨body.site, .eventProof, 0⟩ <|
            .rule .sequence body.site bodyContext
              (premises [.completeBodyConsumer, .actualReturnOrPendingSuffix]
                body.site bodyContext [mark.site, formal.site] ++
               [check .computation body.site bodyContext (endpoint body.site)
                  (endpoint mark.site .bodyConsumer)])
              (.one (sourceRules bodyContext body))))
      let enteredBody := match formal.entry with
        | .value => suffix formal.site checkedBody
        | .computation => checkedBody
      annotated mark context <|
        .existsE ⟨formal.site, .description, 0⟩ <|
          .existsE ⟨mark.site, .viewLogic, 0⟩ <|
            node .lambda mark.site context [.captureWholeEnvironment, .closureFormation]
              [formal.site, pattern.site, body.site]
              (.one <| .forallE ⟨mark.site, .invocation, 0⟩ <|
                .existsE ⟨formal.site, .receipt, 0⟩ <|
                  .rule .parameterEntry formal.site formalContext entryPremises
                    (.one enteredBody))
  | _, .tuple mark elements =>
      annotated mark context <| node .tuple mark.site context [.tupleFormation] elements.roots
        (.one (sourceRules context elements))
  | _, .record mark items =>
      annotated mark context <| node .record mark.site context [.orderedRecordFormation] items.roots
        (.one (sourceRules context items))
  | _, .polyVariant mark tag payloads =>
      annotated mark context <|
        .rule .polyVariant mark.site context
          [.atom { (atom .variantTagArity mark.site context payloads.roots) with
            labels := [tag], arity := payloads.roots.length }]
          (.one (sourceRules context payloads))
  | _, .select mark receiver memberName =>
      annotated mark context <|
        .existsE ⟨mark.site, .viewLogic, 0⟩ <|
          .rule .select mark.site context
            ((premises [.retainedSelection, .selectionQualifiedChildren, .selectionWholeInstance]
              mark.site context [receiver.site]).map (fun premise => match premise with
                | .atom a => .atom { a with names := [memberName] }
                | other => other))
            (.one (sourceRules context receiver))
  | _, .caseE mark scrutinee arms =>
      annotated mark context <|
        node .caseE mark.site context [.caseOrderedAttempts, .branchJoin]
          (scrutinee.site :: arms.roots)
          (.two (sourceRules context scrutinee) (suffix scrutinee.site (sourceRules context arms)))
  | _, .catchE mark scrutinee valueArms operationArms originalArmOrder =>
      annotated mark context <|
        .rule .catchE mark.site context
          ((premises [.shallowPacketInstance, .shallowResidualCoverage, .shallowLatentPreservation,
            .branchJoin] mark.site context
            (scrutinee.site :: (valueArms.roots ++ operationArms.roots))).map
            (fun premise => match premise with
              | .atom a => .atom {a with order := originalArmOrder}
              | other => other))
          (.three (sourceRules context scrutinee)
            (suffix scrutinee.site (sourceRules context valueArms))
            (sourceRules context operationArms))
  | _, .block mark statements last =>
      let finalContext := statements.bindingRecords ++ context
      statementsRulesK context statements <|
        annotated mark context <|
          node .block mark.site context [.blockFinalRoot] [last.site]
            (.one (sourceRules finalContext last))
  | _, .wild site => node .wild site context []
  | _, .litPattern site value =>
      .rule .litPattern site context
        [.atom { (atom .literalComparison site context) with literal := some value }] .nil
  | _, .varPattern site bindingName =>
      .rule .varPattern site context
        [.atom { (atom .patternBinding site context) with names := [bindingName] }] .nil
  | _, .tuplePattern site children =>
      node .tuplePattern site context [.tupleArity] children.roots (.one (sourceRules context children))
  | _, .listPattern site first rest last =>
      .rule .listPattern site context
        [.atom { (atom .listLengthAndRest site context (first.roots ++ last.roots)) with
          names := rest.toList, arity := first.roots.length }]
        (.two (sourceRules context first)
          (sourceRules (patternContext context first) last))
  | _, .recordPattern site fields spread =>
      .rule .recordPattern site context
        [.atom { (atom .visibleRecordPresence site context fields.roots) with names := spread.toList }]
        (.one (sourceRules context fields))
  | _, .variantPattern site tag payloads =>
      .rule .variantPattern site context
        [.atom { (atom .variantPayload site context payloads.roots) with
          labels := [tag], arity := payloads.roots.length }]
        (.one (sourceRules context payloads))
  | _, .conPattern site constructor typeArguments payloads =>
      .rule .conPattern site context
        [.atom { (atom .nominalInvariant site context payloads.roots) with
          declaration := some constructor, annotations := typeArguments }]
        (.one (sourceRules context payloads))
  | _, .refPattern site definition =>
      .rule .refPattern site context
        [.atom { (atom .referencePatternComparison site context) with
          names := [definition], binding := lookupBinding context definition }] .nil
  | _, .asPattern site child bindingName =>
      .rule .asPattern site context
        [.atom { (atom .sameInputAlias site context [child.site]) with names := [bindingName] }]
        (.one (sourceRules context child))
  | _, .orPattern site left right merges =>
      .rule .orPattern site context
        [.atom { (atom .orCommonEnvironment site context [left.site, right.site]) with
          names := merges.map PatternMerge.result, merges := merges },
         .atom (atom .orderedOrAttempt site context [left.site, right.site])]
        (.two (sourceRules context left) (sourceRules context right))
  | _, .letS site recursive bindings =>
      statementRulesK context (.letS site recursive bindings) (node .empty site context [])
  | _, .expressionS site expression =>
      statementRulesK context (.expressionS site expression) (node .empty site context [])
  | _, .moduleS site declaration body =>
      statementRulesK context (.moduleS site declaration body) (node .empty site context [])
  | _, .expressionsNil | _, .patternsNil | _, .recordNil | _, .patternFieldsNil
  | _, .armsNil | _, .operationArmsNil | _, .statementsNil | _, .bindingsNil
  | _, .noExpression => node .empty 0 context []
  | _, .expressionsCons head tail =>
      node .sequence head.site context [.actualReturnOrPendingSuffix] [head.site]
        (.two (sourceRules context head) (suffix head.site (sourceRules context tail)))
  | _, .patternsCons head tail =>
      node .sequence head.site context [] []
        (.two (sourceRules context head) (sourceRules (patternContext context head) tail))
  | _, .recordField site label value tail =>
      .rule .recordField site context
        [.atom { (atom .visibleFieldUpdate site context [value.site]) with labels := [label] }]
        (.two (sourceRules context value) (suffix value.site (sourceRules context tail)))
  | _, .recordSpread site value tail =>
      node .recordSpread site context [.visibleSpreadUpdate] [value.site]
        (.two (sourceRules context value) (suffix value.site (sourceRules context tail)))
  | _, .patternField site label child default tail =>
      .rule .patternField site context
        [.atom { (atom .defaultBeforeBinding site context (child.site :: default.roots)) with
          labels := [label], flag := some (!default.roots.isEmpty) },
         .atom { (atom .defaultAndInputJoin site context (child.site :: default.roots)) with
          labels := [label], flag := some (!default.roots.isEmpty) }]
        (.three (sourceRules context default) (sourceRules context child)
          (sourceRules (patternContext context child) tail))
  | _, .arm site pattern guard body tail =>
      let inner := patternContext context pattern
      .rule .arm site context
        (premises [.patternAttempt, .boolGuard, .originalOutsideArmContext]
          site context (pattern.site :: body.site :: guard.roots) ++
         [.boundary site inner (endpoint body.site) (endpoint body.site .branchJoin)])
        (.cons (sourceRules context pattern)
          (.cons (sourceRules inner guard)
            (.cons (sourceRules inner body) (.one (sourceRules context tail)))))
  | _, .operationArm site operation rigidTypeBinders payload continuation guard body tail =>
      let inner := continuation.bindingRecords.map (fun binding =>
        {binding with kind := .continuation}) ++ patternContext context payload
      let packetPremises :=
        [.atom { (atom .operationRigidInstance site context [payload.site]) with
          declaration := some operation, arity := rigidTypeBinders },
         .atom { (atom .rawContinuationContract site context
           [payload.site, continuation.site, body.site]) with names := continuation.binders }]
      .rule .operationArm site context []
        (.two
          (.forallE ⟨site, .rigidOperation, rigidTypeBinders⟩ <|
            .rule .arm site context
              (packetPremises ++
               premises [.boolGuard, .originalOutsideArmContext] site context (body.site :: guard.roots) ++
               [.boundary site inner (endpoint body.site) (endpoint body.site .branchJoin)])
              (.cons (sourceRules context payload)
                (.cons (sourceRules (patternContext context payload) continuation)
                  (.cons (sourceRules inner guard) (.one (sourceRules inner body))))))
          (sourceRules context tail))
  | _, .statementsCons head tail =>
      statementsRulesK context (.statementsCons head tail) (node .empty head.site context [])
  | _, .binding site bindingName annotation initializer tail =>
      bindingsRulesK context (.binding site bindingName annotation initializer tail) true
        (node .empty site context [])
  | _, .someExpression expression => sourceRules context expression

termination_by category source => (sizeOf source) * 3 + 1
decreasing_by all_goals simp_wf <;> omega

/-- A statement continuation is constructed from source and remains inside
all original initializer and return/response scopes introduced by it. -/
def statementRulesK (context : Context) (statement : Source .statement)
    (continuation : RuleTree) : RuleTree :=
  match statement with
  | .letS site recursive bindings =>
      let inner := if recursive then
        bindings.bindingRecords.map (fun binding =>
          {binding with kind := .internal, component := some site}) ++ context else context
      let after := if recursive then
        .publishGroup (bindings.bindingRecords.map (fun binding => (binding.name, binding.owner))) continuation
        else continuation
      .rule .letS site context
        ([.atom { (atom .sourceLetRegistration site context) with
          names := bindings.binders, flag := some recursive }] ++
         if recursive then premises [.recursiveJointMemberWorld] site inner else [])
        (.one (bindingsRulesK inner bindings (!recursive) after))
  | .expressionS site expression =>
      node .expressionS site context [.expressionDiscard] [expression.site]
        (.two (sourceRules context expression) (suffix expression.site continuation))
  | .moduleS site declaration body =>
      .rule .moduleS site context
        [.atom { (atom .sourceModuleLinking site context) with declaration := some declaration }]
        (.one (statementsRulesK context body continuation))
termination_by (sizeOf statement) * 3
decreasing_by all_goals simp_wf <;> omega

def statementsRulesK (context : Context) (statements : Source .statements)
    (continuation : RuleTree) : RuleTree :=
  match statements with
  | .statementsNil => continuation
  | .statementsCons head tail =>
      statementRulesK context head
        (statementsRulesK (statementContext context head) tail continuation)
termination_by (sizeOf statements) * 3
decreasing_by all_goals simp_wf <;> omega

/-- Preserve an initializer Block's internal execution scopes through its
actual outer Return and publication; no captured local anchor is discarded. -/
def expressionRulesK (context : Context) (expression : Source .expression)
    (continuation : RuleTree) : RuleTree :=
  match expression with
  | .block mark statements last =>
      let inner := statements.bindingRecords ++ context
      statementsRulesK context statements <|
        expressionRulesK inner last <|
          annotated mark context <|
            node .block mark.site context [.blockFinalRoot] [last.site] (.one continuation)
  | other => node .sequence other.site context [] []
      (.two (sourceRules context other) continuation)
termination_by (sizeOf expression) * 3 + 2
decreasing_by all_goals simp_wf <;> omega

def bindingsRulesK (context : Context) (bindings : Source .bindings)
    (publishEach : Bool) (continuation : RuleTree) : RuleTree :=
  match bindings with
  | .bindingsNil => continuation
  | .binding site bindingName annotation initializer tail =>
      let tailContext := match lookupBinding context bindingName with
        | some binding => if binding.kind = .internal then context
            else bindNames context site .published [bindingName]
        | none => bindNames context site .published [bindingName]
      let rest := bindingsRulesK tailContext tail publishEach continuation
      let published := if publishEach then .publishGroup [(bindingName, site)] rest else rest
      let installed := suffix site <| .sharedE ⟨site, .shared, 0⟩ <|
        .rule .binding site context
          [.atom { (atom .oneShotInitializer site context [initializer.site]) with
            names := [bindingName], annotation := annotation },
           .atom { (atom .publicationFinalRoot site context [initializer.site]) with
            names := [bindingName], annotation := annotation }]
          (.one published)
      let formedContinuation : RuleTree := match annotation with
        | none => installed
        | some target =>
            .rule .annotation site context
              [.atom { (atom .finalAnnotationFormation site context [initializer.site]) with
                annotation := some target },
               .boundary site context (endpoint initializer.site .finalRoot)
                 (endpoint site .writtenTarget)] (.one installed)
      .initializerE site (expressionRulesK context initializer formedContinuation)

termination_by (sizeOf bindings) * 3
decreasing_by all_goals simp_wf <;> omega
end

/-- Source-directed SRC-J construction. A new instance's complete description
frame encloses BOTH its independent source derivation and the whole client
suffix. Alias allocates no instance. Join supplies exactly one environment
to both branches. Original Shared/Established/OneShot anchors are fields of
the fixed root environment; `newUse` only creates a description frame.

The local `originalNewInstance` relation must retain those original anchors
and source binder strategies. It is the original instance-map clause, not a
claim that Build, source typing or Generalize succeeds. Its independent
source derivation is the first child, generated here from raw source.
-/
def clientRules (context : Context) : Client → RuleTree
  | .done site => node .empty site context []
  | .newUse site definition instanceName rest =>
      let inner := bindNames context site .local [instanceName]
      .existsE ⟨site, .publishedInstance, 0⟩ <|
        .rule .newUse site inner
          [.atom { (atom .originalNewInstance site inner [definition.source.site]) with
            names := [definition.anchor, instanceName], declaration := some definition.declaration }]
          (.two (.atPublication definition.anchor (sourceRules definition.context definition.source))
            (.aliasPublication definition.anchor instanceName (clientRules inner rest)))
  | .alias site original aliasName rest =>
      let inherited := lookupBinding context original
      let inner := match inherited with
        | some binding => {binding with name := aliasName} :: context
        | none => context
      .rule .alias site context
        [.atom { (atom .sameMonomorphicAlias site context) with
          names := [original, aliasName], binding := inherited }]
        (.one (.aliasPublication original aliasName (clientRules inner rest)))
  | .view site original target rest =>
      let binding := lookupBinding context original
      .existsE ⟨site, .viewLogic, 0⟩ <|
        .rule .view site context
          [.atom { (atom .resolvedSameBinding site context) with names := [original], binding := binding },
           .atom { (atom .finalAnnotationFormation site context) with
             names := [original], binding := binding, annotation := some target },
           check .value site context (endpoint ((binding.map Binding.owner).getD site))
             (endpoint site .writtenTarget)]
          (.one (clientRules context rest))
  | .run site original eventOperands rest =>
      .forallE ⟨site, .invocation, 0⟩ <|
        .existsE ⟨site, .eventProof, 0⟩ <|
          .rule .run site context
            [.atom { (atom .actualRunInterface site context eventOperands) with
              names := [original], binding := lookupBinding context original }]
            (.one (suffix site (clientRules context rest)))
  | .join site left right =>
      node .join site context [] [] (.two (clientRules context left) (clientRules context right))
  | .bind site bindingName first rest =>
      node .sequentialBind site context [.actualReturnOrPendingSuffix] []
        (.two (clientRules context first)
          (suffix site (clientRules (bindNames context site .local [bindingName]) rest)))
  | .constrain site declaration operands rest =>
      .rule .clientConstraint site context
        [.atom { (atom .clientPredicate site context operands) with declaration := some declaration }]
        (.one (clientRules context rest))

/-- Actual event identity has its original owner/port, complete actual
parent path and occurrence. Description frames are not event identities. -/
structure EventStep (Value : Type) where
  source : Site
  kind : BinderKind
  occurrence : Nat
  data : Value
  deriving DecidableEq, Repr

structure ActualEvent (Value : Type) where
  parents : List (EventStep Value)
  occurrence : Nat
  deriving DecidableEq, Repr

structure ScopedValue (Value : Type) where
  data : Value
  event : ActualEvent Value

def Binder.isEvent (binder : Binder) : Bool :=
  match binder.kind with
  | .invocation | .receipt | .returnRebind | .rigidOperation | .response | .oneShot => true
  | _ => false

def Binder.isFixed (binder : Binder) : Bool := binder.isEvent || binder.kind == .shared

def ActualEvent.path {Value : Type} (event : ActualEvent Value) (binder : Binder)
    (data : Value) : List (EventStep Value) :=
  event.parents ++ [⟨binder.site, binder.kind, event.occurrence, data⟩]

structure AnchorKey (Value : Type) where
  origin : Declaration
  path : List (EventStep Value)
  binder : Binder
  deriving DecidableEq, Repr

structure PublicationId (Value : Type) where
  origin : Declaration
  site : Site
  path : List (EventStep Value)
  deriving DecidableEq, Repr

structure Frame (Value : Type) where
  binder : Binder
  value : ScopedValue Value
  entryPath : List (EventStep Value)

def Frame.exitPath {Value : Type} (frame : Frame Value) : List (EventStep Value) :=
  ActualEvent.path ⟨frame.entryPath, frame.value.event.occurrence⟩ frame.binder frame.value.data

/-- The actual entry snapshot is captured before an initializer's internal
bindings and events. It is distinct from its completed returned captures. -/
structure InitializerEntry (Value : Type) where
  site : Site
  path : List (EventStep Value)
  names : List (Name × PublicationId Value)
  frames : List (Frame Value)

structure PublicationRecord (Value : Type) where
  identity : PublicationId Value
  entryPath : List (EventStep Value)
  entryNames : List (Name × PublicationId Value)
  entryFrames : List (Frame Value)
  captures : List (Name × PublicationId Value)
  fixedFrames : List (Frame Value)
  initializers : List (InitializerEntry Value)

/-- The one original strategy and publication graph are fixed solution data.
They contain values/identities, never source derivations or solver-success
proofs. New description frames cannot replace either map. -/
structure Environment (Value : Type) where
  root : Value
  anchors : AnchorKey Value → ScopedValue Value
  publications : PublicationId Value → Option (PublicationRecord Value)
  origin : Declaration
  eventPath : List (EventStep Value) := []
  names : List (Name × PublicationId Value) := []
  frames : List (Frame Value) := []
  replay : Option (List (Frame Value)) := none
  initializers : List (InitializerEntry Value) := []

def Environment.enterInitializer {Value : Type} (environment : Environment Value)
    (site : Site) : Environment Value :=
  {environment with initializers :=
    ⟨site, environment.eventPath, environment.names,
      environment.frames.filter (fun frame => frame.binder.isFixed)⟩ :: environment.initializers}

def Environment.anchorKey {Value : Type} (environment : Environment Value)
    (binder : Binder) : AnchorKey Value := ⟨environment.origin, environment.eventPath, binder⟩

/-- Admission and source checking retain every original candidate payload.
The independent payload is part of an actual-event key, never overwritten
by a selected strategy value. Description proof data lives in other frames. -/
def Environment.choose {Value : Type} (_environment : Environment Value)
    (_binder : Binder) (candidate : ScopedValue Value) : ScopedValue Value := candidate

def Environment.anchorValue {Value : Type} (environment : Environment Value)
    (binder : Binder) : ScopedValue Value :=
  environment.anchors (environment.anchorKey binder)

def Environment.extend {Value : Type} (environment : Environment Value)
    (binder : Binder) (candidate : ScopedValue Value) : Environment Value :=
  let value := candidate
  { environment with
    frames := environment.frames ++ [⟨binder, value, environment.eventPath⟩]
    eventPath := if binder.isEvent then
      ActualEvent.path ⟨environment.eventPath, value.event.occurrence⟩ binder value.data
      else environment.eventPath
    replay := if binder.kind == .invocation || binder.kind == .rigidOperation || binder.kind == .response
      then none else environment.replay }

def Environment.prefixAtShared {Value : Type} (environment : Environment Value)
    (site : Site) : List (Frame Value) :=
  (environment.frames.reverse.dropWhile (fun frame =>
    !(frame.binder.site == site && frame.binder.kind == .shared))).reverse

/-- Exact source construction of a publication record. The prefix ends at
this binding's own Shared introduction, below its actual Return/rebind.
Its replay entry was recorded before all internal initializer events. -/
noncomputable def Environment.publicationCandidate {Value : Type} (environment : Environment Value)
    (site : Site) : Option (PublicationId Value × PublicationRecord Value) := by
  classical
  exact do
    let entries := environment.initializers.dropWhile (fun entry => entry.site != site)
    let entry ← entries.head?
    let savedFrames := environment.prefixAtShared site
    let shared ← savedFrames.getLast?
    let returned ← savedFrames.reverse.find? (fun frame =>
      frame.binder.site == site && frame.binder.kind == .returnRebind)
    if ¬ shared.entryPath = returned.exitPath then none else do
      let identity : PublicationId Value :=
        ⟨environment.origin, site, returned.exitPath⟩
      return (identity, {
        identity := identity
        entryPath := entry.path
        entryNames := entry.names
        entryFrames := entry.frames
        captures := environment.names
        fixedFrames := savedFrames.filter (fun frame => frame.binder.isFixed)
        initializers := entries})

def Environment.publicationValid {Value : Type} (environment : Environment Value)
    (bindings : List (Name × Site)) : Prop :=
  ∀ binding ∈ bindings, ∃ identity record,
    environment.publicationCandidate binding.2 = some (identity, record) ∧
      environment.publications identity = some record

noncomputable def Environment.publish {Value : Type} (environment : Environment Value)
    (bindings : List (Name × Site)) : Option (Environment Value) := do
  let additions ← bindings.mapM (fun binding => do
    let candidate ← environment.publicationCandidate binding.2
    return (binding.1, candidate.1))
  return {environment with names := additions ++ environment.names}

def Environment.publicationName {Value : Type} (environment : Environment Value)
    (binding : Name) : Option (PublicationId Value) :=
  (environment.names.find? (fun pair => pair.1 == binding)).map Prod.snd

def Environment.restore {Value : Type} (environment : Environment Value)
    (record : PublicationRecord Value) : Environment Value :=
  { environment with
    origin := record.identity.origin
    eventPath := record.entryPath
    names := record.entryNames
    frames := record.entryFrames ++ environment.frames.filter (fun frame => !frame.binder.isFixed)
    replay := some record.fixedFrames
    initializers := record.initializers }

noncomputable def Environment.atPublication {Value : Type} (environment : Environment Value)
    (binding : Name) : Option (Environment Value) := by
  classical
  exact do
    let identity ← environment.publicationName binding
    let record ← environment.publications identity
    if ¬ (record.identity = identity ∧ record.fixedFrames.all (fun frame => frame.binder.isFixed) = true) then none else
      return environment.restore record

def Environment.aliasPublication {Value : Type} (environment : Environment Value)
    (original aliasName : Name) : Option (Environment Value) := do
  let identity ← environment.publicationName original
  return {environment with names := (aliasName, identity) :: environment.names}

/-- During a new description, an initializer event is an original fixed
record. Future invocation/response binders clear replay in `extend`. -/
noncomputable def Environment.executionValue {Value : Type} (environment : Environment Value)
    (binder : Binder) : Option (ScopedValue Value) := by
  classical
  exact do
    let saved ← environment.replay
    let frame ← saved.find? (fun frame => decide (frame.binder = binder ∧ frame.entryPath = environment.eventPath))
    return frame.value

inductive StructuralCheck where
  | recordWidthDepth | unionInjection | unionCases | intersection | top
  | sameValue | sameComputation | result | guaranteeWeakening
  | constructorCongruence | recursiveEquationPair
  deriving DecidableEq, Repr

/-- Independent LOCAL meanings only. `structuralShape` validates the exact
constructor/whole endpoint incidence of the listed children. `functionShape`
validates a same-callable checked-domain/source-observation pair; it does not
assert either inclusion. Those require recursive finite `Checking` proofs.
`primitiveCheck` is an actual independently typed primitive declaration.
`conversion` is a direct original source-boundary operation, not a path. -/
structure Kernel (Value : Type) where
  atom : Environment Value → Atom → Prop
  admitted : Environment Value → Binder → ScopedValue Value → Prop
  primitiveCheck : Environment Value → Declaration → CheckGoal → Prop
  structuralShape : Environment Value → StructuralCheck → CheckGoal → List CheckGoal → Prop
  functionShape : Environment Value → CheckGoal → CheckGoal → Binder → CheckGoal → Prop
  /-- The tag comes from the original source normalization/boundary rule,
  never from a solved endpoint's latent shape. -/
  boundaryTag : Environment Value → Site → Context → Endpoint → Endpoint → CheckMode → Prop
  conversion : Environment Value → Site → Context → Endpoint → Endpoint → Declaration → Prop

mutual
/-- Finite original checking derivations; no arbitrary inclusion-oracle
constructor and no direct-boundary transitivity constructor. -/
inductive Checking {Value : Type} (kernel : Kernel Value) :
    Environment Value → CheckGoal → Prop where
  | identity {environment : Environment Value} (goal : CheckGoal)
      (same : goal.lower = goal.upper) : Checking kernel environment goal
  | primitive {environment : Environment Value} (goal : CheckGoal) (declaration : Declaration)
      (valid : kernel.primitiveCheck environment declaration goal) : Checking kernel environment goal
  | compose {environment : Environment Value}
      (mode : CheckMode) (site : Site) (context : Context) (first middle last : Endpoint)
      (left : Checking kernel environment ⟨mode, site, context, first, middle⟩)
      (right : Checking kernel environment ⟨mode, site, context, middle, last⟩) :
      Checking kernel environment ⟨mode, site, context, first, last⟩
  | structural {environment : Environment Value}
      (rule : StructuralCheck) (goal : CheckGoal) (children : List CheckGoal)
      (shape : kernel.structuralShape environment rule goal children)
      (checked : Checkings kernel environment children) : Checking kernel environment goal
  | function {environment : Environment Value}
      (goal domain observation : CheckGoal) (challenge : Binder)
      (domainMode : domain.mode = .domain) (observationMode : observation.mode = .observation)
      (challengeKind : challenge.kind = .invocation)
      (shape : kernel.functionShape environment goal domain challenge observation)
      (domainProof : Checking kernel environment domain)
      (observationProof : ∀ value, kernel.admitted environment challenge value →
        Checking kernel (environment.extend challenge value) observation) :
      Checking kernel environment goal
inductive Checkings {Value : Type} (kernel : Kernel Value) :
    Environment Value → List CheckGoal → Prop where
  | nil {environment : Environment Value} : Checkings kernel environment []
  | cons {environment : Environment Value} {head : CheckGoal} {tail : List CheckGoal}
      (first : Checking kernel environment head) (rest : Checkings kernel environment tail) :
      Checkings kernel environment (head :: tail)
end

inductive Boundary {Value : Type} (kernel : Kernel Value) (environment : Environment Value) :
    Site → Context → Endpoint → Endpoint → Prop where
  | proofOnly (site : Site) (context : Context) (lower upper : Endpoint)
      (mode : CheckMode) (sourceTag : kernel.boundaryTag environment site context lower upper mode)
      (proof : Checking kernel environment ⟨mode, site, context, lower, upper⟩) :
      Boundary kernel environment site context lower upper
  | actual (site : Site) (context : Context) (lower upper : Endpoint) (declaration : Declaration)
      (valid : kernel.conversion environment site context lower upper declaration) :
      Boundary kernel environment site context lower upper

inductive Local {Value : Type} (kernel : Kernel Value) (environment : Environment Value) :
    Premise → Prop where
  | atom {value : Atom} (valid : kernel.atom environment value) : Local kernel environment (.atom value)
  | checking {goal : CheckGoal} (proof : Checking kernel environment goal) :
      Local kernel environment (.checking goal)
  | boundary {site : Site} {context : Context} {lower upper : Endpoint}
      (proof : Boundary kernel environment site context lower upper) :
      Local kernel environment (.boundary site context lower upper)

mutual
/-- Independent original finite rule derivation. The constructors here
mention neither Build, Formula, Satisfies, source export nor Q success. -/
inductive Judgment {Value : Type} (kernel : Kernel Value) :
    Environment Value → RuleTree → Prop where
  | rule {environment : Environment Value} {rule : Rule} {site : Site} {context : Context}
      {premises : List Premise} {children : RuleForest}
      (localProofs : ∀ premise ∈ premises, Local kernel environment premise)
      (childProofs : Judgments kernel environment children) :
      Judgment kernel environment (.rule rule site context premises children)
  | existsE {environment : Environment Value} {binder : Binder} {body : RuleTree}
      (value : ScopedValue Value) (admitted : kernel.admitted environment binder value)
      (proof : Judgment kernel (environment.extend binder value) body) :
      Judgment kernel environment (.existsE binder body)
  | forallE {environment : Environment Value} {binder : Binder} {body : RuleTree}
      (proof : ∀ value, kernel.admitted environment binder value →
        Judgment kernel (environment.extend binder value) body) :
      Judgment kernel environment (.forallE binder body)
  | initializerE {environment : Environment Value} {site : Site} {body : RuleTree}
      (proof : Judgment kernel (environment.enterInitializer site) body) :
      Judgment kernel environment (.initializerE site body)
  | executionOpen {environment : Environment Value} {binder : Binder} {body : RuleTree}
      (openHistory : environment.replay = none)
      (proof : ∀ value, kernel.admitted environment binder value →
        Judgment kernel (environment.extend binder value) body) :
      Judgment kernel environment (.executionE binder body)
  | executionFixed {environment : Environment Value} {binder : Binder} {body : RuleTree}
      (history : List (Frame Value)) (fixedHistory : environment.replay = some history)
      (value : ScopedValue Value) (lookup : environment.executionValue binder = some value)
      (admitted : kernel.admitted environment binder value)
      (proof : Judgment kernel (environment.extend binder value) body) :
      Judgment kernel environment (.executionE binder body)
  | sharedE {environment : Environment Value} {binder : Binder} {body : RuleTree}
      (admitted : kernel.admitted environment binder (environment.anchorValue binder))
      (proof : Judgment kernel (environment.extend binder (environment.anchorValue binder)) body) :
      Judgment kernel environment (.sharedE binder body)
  | publishGroup {environment : Environment Value} {bindings : List (Name × Site)} {body : RuleTree}
      (valid : environment.publicationValid bindings) (next : Environment Value)
      (constructed : environment.publish bindings = some next)
      (proof : Judgment kernel next body) : Judgment kernel environment (.publishGroup bindings body)
  | atPublication {environment : Environment Value} {bindingName : Name} {body : RuleTree}
      (restored : Environment Value) (lookup : environment.atPublication bindingName = some restored)
      (proof : Judgment kernel restored body) : Judgment kernel environment (.atPublication bindingName body)
  | aliasPublication {environment : Environment Value} {original aliasName : Name} {body : RuleTree}
      (aliased : Environment Value) (lookup : environment.aliasPublication original aliasName = some aliased)
      (proof : Judgment kernel aliased body) :
      Judgment kernel environment (.aliasPublication original aliasName body)
  | chooseLeft {environment : Environment Value} {site : Site} {left right : RuleTree}
      (proof : Judgment kernel environment left) : Judgment kernel environment (.choice site left right)
  | chooseRight {environment : Environment Value} {site : Site} {left right : RuleTree}
      (proof : Judgment kernel environment right) : Judgment kernel environment (.choice site left right)
inductive Judgments {Value : Type} (kernel : Kernel Value) :
    Environment Value → RuleForest → Prop where
  | nil {environment : Environment Value} : Judgments kernel environment .nil
  | cons {environment : Environment Value} {head : RuleTree} {tail : RuleForest}
      (first : Judgment kernel environment head) (rest : Judgments kernel environment tail) :
      Judgments kernel environment (.cons head tail)
end

/-- A source judgment is indexed by raw source and its resolved environment;
the finite rule inventory is calculated from that source, not supplied by the
caller. Its local semantics is independent of generated formula semantics. -/
def SourceJudgment {Value : Type} (kernel : Kernel Value) (environment : Environment Value)
    (context : Context) {category : Category} (source : Source category) : Prop :=
  Judgment kernel environment (sourceRules context source)

inductive Formula where
  | truth
  | local (premise : Premise)
  | and (left right : Formula)
  | or (left right : Formula)
  | existsE (binder : Binder) (body : Formula)
  | forallE (binder : Binder) (body : Formula)
  | initializerE (site : Site) (body : Formula)
  | executionE (binder : Binder) (body : Formula)
  | sharedE (binder : Binder) (body : Formula)
  | publishGroup (bindings : List (Name × Site)) (body : Formula)
  | atPublication (binding : Name) (body : Formula)
  | aliasPublication (original aliasName : Name) (body : Formula)

def compilePremises : List Premise → Formula
  | [] => .truth
  | head :: tail => .and (.local head) (compilePremises tail)

mutual
def compile : RuleTree → Formula
  | .rule _ _ _ localPremises children => .and (compilePremises localPremises) (compileForest children)
  | .existsE binder body => .existsE binder (compile body)
  | .forallE binder body => .forallE binder (compile body)
  | .initializerE site body => .initializerE site (compile body)
  | .executionE binder body => .executionE binder (compile body)
  | .sharedE binder body => .sharedE binder (compile body)
  | .publishGroup bindings body => .publishGroup bindings (compile body)
  | .atPublication bindingName body => .atPublication bindingName (compile body)
  | .aliasPublication original aliasName body => .aliasPublication original aliasName (compile body)
  | .choice _ left right => .or (compile left) (compile right)
def compileForest : RuleForest → Formula
  | .nil => .truth
  | .cons head tail => .and (compile head) (compileForest tail)
end

def Satisfies {Value : Type} (kernel : Kernel Value) (environment : Environment Value) : Formula → Prop
  | .truth => True
  | .local premise => Local kernel environment premise
  | .and left right => Satisfies kernel environment left ∧ Satisfies kernel environment right
  | .or left right => Satisfies kernel environment left ∨ Satisfies kernel environment right
  | .existsE binder body => ∃ value, kernel.admitted environment binder value ∧
      Satisfies kernel (environment.extend binder value) body
  | .forallE binder body => ∀ value, kernel.admitted environment binder value →
      Satisfies kernel (environment.extend binder value) body
  | .initializerE site body => Satisfies kernel (environment.enterInitializer site) body
  | .executionE binder body => match environment.replay with
      | none => ∀ value, kernel.admitted environment binder value →
          Satisfies kernel (environment.extend binder value) body
      | some _ => ∃ value, environment.executionValue binder = some value ∧
          kernel.admitted environment binder value ∧
          Satisfies kernel (environment.extend binder value) body
  | .sharedE binder body =>
      kernel.admitted environment binder (environment.anchorValue binder) ∧
        Satisfies kernel (environment.extend binder (environment.anchorValue binder)) body
  | .publishGroup bindings body => environment.publicationValid bindings ∧
      ∃ next, environment.publish bindings = some next ∧ Satisfies kernel next body
  | .atPublication bindingName body =>
      ∃ restored, environment.atPublication bindingName = some restored ∧ Satisfies kernel restored body
  | .aliasPublication original aliasName body =>
      ∃ aliased, environment.aliasPublication original aliasName = some aliased ∧ Satisfies kernel aliased body

/-- Total source-directed generation; no input derivation or successful
checking promise is used to produce the formula. -/
def Build (context : Context) {category : Category} (source : Source category) : Formula :=
  compile (sourceRules context source)

def JointJudgment {Value : Type} (kernel : Kernel Value) (environment : Environment Value)
    (context : Context) (client : Client) : Prop :=
  Judgment kernel environment (clientRules context client)

def BuildJoint (context : Context) (client : Client) : Formula :=
  compile (clientRules context client)

theorem premises_iff {Value : Type} (kernel : Kernel Value) (environment : Environment Value)
    (localPremises : List Premise) :
    Satisfies kernel environment (compilePremises localPremises) ↔
      ∀ premise ∈ localPremises, Local kernel environment premise := by
  induction localPremises with
  | nil => simp [compilePremises, Satisfies]
  | cons head tail ih => simp [compilePremises, Satisfies, ih]

mutual
theorem reconstruction {Value : Type} (kernel : Kernel Value) (environment : Environment Value)
    (tree : RuleTree) : Satisfies kernel environment (compile tree) ↔ Judgment kernel environment tree := by
  cases tree with
  | rule rule site context localPremises children =>
      constructor
      · intro success
        exact .rule ((premises_iff kernel environment localPremises).mp success.1)
          ((reconstruction_forest kernel environment children).mp success.2)
      · intro proof
        cases proof with
        | rule locals childrenProof =>
            exact ⟨(premises_iff kernel environment localPremises).mpr locals,
              (reconstruction_forest kernel environment children).mpr childrenProof⟩
  | existsE binder body =>
      constructor
      · rintro ⟨value, admitted, success⟩
        exact .existsE value admitted ((reconstruction kernel (environment.extend binder value) body).mp success)
      · intro proof
        cases proof with
        | existsE value admitted bodyProof =>
            exact ⟨value, admitted, (reconstruction kernel (environment.extend binder value) body).mpr bodyProof⟩
  | forallE binder body =>
      constructor
      · intro success
        exact .forallE (fun value admitted =>
          (reconstruction kernel (environment.extend binder value) body).mp (success value admitted))
      · intro proof
        cases proof with
        | forallE bodyProof =>
            exact fun value admitted =>
              (reconstruction kernel (environment.extend binder value) body).mpr (bodyProof value admitted)
  | sharedE binder body =>
      constructor
      · intro success
        exact .sharedE success.1 ((reconstruction kernel _ body).mp success.2)
      · intro proof
        cases proof with
        | sharedE admitted child => exact ⟨admitted, (reconstruction kernel _ body).mpr child⟩
  | initializerE site body =>
      constructor
      · intro success
        exact .initializerE ((reconstruction kernel _ body).mp success)
      · intro proof
        cases proof with
        | initializerE child => exact (reconstruction kernel _ body).mpr child
  | executionE binder body =>
      cases mode : environment.replay with
      | none =>
          constructor
          · intro success
            simp only [compile, Satisfies, mode] at success
            exact .executionOpen mode (fun value admitted =>
              (reconstruction kernel _ body).mp (success value admitted))
          · intro proof
            cases proof with
            | executionOpen _ child =>
                simp only [compile, Satisfies, mode]
                exact fun value admitted => (reconstruction kernel _ body).mpr (child value admitted)
            | executionFixed history impossible _ _ _ _ => simp [mode] at impossible
      | some history =>
          constructor
          · intro success
            simp only [compile, Satisfies, mode] at success
            rcases success with ⟨value, lookup, admitted, child⟩
            exact .executionFixed history mode value lookup admitted ((reconstruction kernel _ body).mp child)
          · intro proof
            cases proof with
            | executionOpen impossible _ => simp [mode] at impossible
            | executionFixed _ _ value lookup admitted child =>
                simp only [compile, Satisfies, mode]
                exact ⟨value, lookup, admitted, (reconstruction kernel _ body).mpr child⟩
  | publishGroup bindings body =>
      constructor
      · rintro ⟨valid, next, constructed, success⟩
        exact .publishGroup valid next constructed ((reconstruction kernel next body).mp success)
      · intro proof
        cases proof with
        | publishGroup valid next constructed child =>
            exact ⟨valid, next, constructed, (reconstruction kernel next body).mpr child⟩
  | atPublication bindingName body =>
      constructor
      · rintro ⟨restored, lookup, success⟩
        exact .atPublication restored lookup ((reconstruction kernel restored body).mp success)
      · intro proof
        cases proof with
        | atPublication restored lookup child =>
            exact ⟨restored, lookup, (reconstruction kernel restored body).mpr child⟩
  | aliasPublication original aliasName body =>
      constructor
      · rintro ⟨aliased, lookup, success⟩
        exact .aliasPublication aliased lookup ((reconstruction kernel aliased body).mp success)
      · intro proof
        cases proof with
        | aliasPublication aliased lookup child =>
            exact ⟨aliased, lookup, (reconstruction kernel aliased body).mpr child⟩
  | choice site left right =>
      constructor
      · intro success
        cases success with
        | inl proof => exact .chooseLeft ((reconstruction kernel environment left).mp proof)
        | inr proof => exact .chooseRight ((reconstruction kernel environment right).mp proof)
      · intro proof
        cases proof with
        | chooseLeft proof => exact Or.inl ((reconstruction kernel environment left).mpr proof)
        | chooseRight proof => exact Or.inr ((reconstruction kernel environment right).mpr proof)
termination_by sizeOf tree
theorem reconstruction_forest {Value : Type} (kernel : Kernel Value) (environment : Environment Value)
    (forest : RuleForest) :
    Satisfies kernel environment (compileForest forest) ↔ Judgments kernel environment forest := by
  cases forest with
  | nil =>
      constructor
      · intro _; exact .nil
      · intro _; trivial
  | cons head tail =>
      constructor
      · intro success
        exact .cons ((reconstruction kernel environment head).mp success.1)
          ((reconstruction_forest kernel environment tail).mp success.2)
      · intro proof
        cases proof with
        | cons first rest =>
            exact ⟨(reconstruction kernel environment head).mpr first,
              (reconstruction_forest kernel environment tail).mpr rest⟩
termination_by sizeOf forest
end

/-- SRC for every raw constructor. In particular this theorem takes Source,
not a pre-registered tree, local reconstruction law, or a source typing
derivation hidden in the generated solution record. -/
theorem source_reconstruction {Value : Type} (kernel : Kernel Value)
    (environment : Environment Value) (context : Context) {category : Category}
    (source : Source category) :
    Satisfies kernel environment (Build context source) ↔
      SourceJudgment kernel environment context source :=
  reconstruction kernel environment (sourceRules context source)

theorem generated_constraints_imply_source_judgment {Value : Type} (kernel : Kernel Value)
    (environment : Environment Value) (context : Context) {category : Category}
    (source : Source category)
    (solved : Satisfies kernel environment (Build context source)) :
    SourceJudgment kernel environment context source :=
  (source_reconstruction kernel environment context source).mp solved

/-- SRC-J keeps one fixed environment (including the original anchored
strategy) for the whole finite client. It does not separately existentially
close each alias/view and then conjoin those independent answers. -/
theorem joint_reconstruction {Value : Type} (kernel : Kernel Value)
    (environment : Environment Value) (context : Context) (client : Client) :
    Satisfies kernel environment (BuildJoint context client) ↔
      JointJudgment kernel environment context client :=
  reconstruction kernel environment (clientRules context client)

theorem generated_joint_constraints_imply_joint_judgment {Value : Type} (kernel : Kernel Value)
    (environment : Environment Value) (context : Context) (client : Client)
    (solved : Satisfies kernel environment (BuildJoint context client)) :
    JointJudgment kernel environment context client :=
  (joint_reconstruction kernel environment context client).mp solved

/-- A join retains the exact same root and preceding frame assignment in
both children, including any enclosing new-instance description frame. -/
theorem join_uses_one_environment {Value : Type} (kernel : Kernel Value)
    (environment : Environment Value) (context : Context) (site : Site) (left right : Client) :
    Satisfies kernel environment (BuildJoint context (.join site left right)) ↔
      Satisfies kernel environment (BuildJoint context left) ∧
      Satisfies kernel environment (BuildJoint context right) := by
  simp [BuildJoint, clientRules, node, premises, compile, compileForest,
    RuleForest.two, compilePremises, Satisfies]

/-- W is conjoined at its actual original scope. It can refer to the same
public, fixed, instance and event fields as the surrounding client; it does
not receive a separately solved copy of that scoped assignment. -/
theorem client_predicate_uses_one_environment {Value : Type} (kernel : Kernel Value)
    (environment : Environment Value) (context : Context) (site : Site)
    (declaration : Declaration) (operands : List Site) (rest : Client) :
    Satisfies kernel environment (BuildJoint context (.constrain site declaration operands rest)) ↔
      Local kernel environment (.atom { (atom .clientPredicate site context operands) with
        declaration := some declaration }) ∧
      Satisfies kernel environment (BuildJoint context rest) := by
  simp [BuildJoint, clientRules, compile, compileForest, RuleForest.one, compilePremises, Satisfies]

/-- New checks raw source inside the SAME instance frame subsequently used
by its client. This exposes the actual source-premise supplier; the caller
does not hand the theorem a local rule tree or a source typing derivation. -/
theorem new_use_checks_source_and_client_in_one_frame {Value : Type} (kernel : Kernel Value)
    (environment : Environment Value) (context : Context) (site : Site)
    (definition : Definition) (instanceName : Name) (rest : Client) :
    Satisfies kernel environment (BuildJoint context (.newUse site definition instanceName rest)) ↔
      ∃ value, kernel.admitted environment ⟨site, .publishedInstance, 0⟩ value ∧
        Local kernel (environment.extend ⟨site, .publishedInstance, 0⟩ value)
          (.atom { (atom .originalNewInstance site
            (bindNames context site .local [instanceName]) [definition.source.site]) with
            names := [definition.anchor, instanceName], declaration := some definition.declaration }) ∧
        (∃ restored, (environment.extend ⟨site, .publishedInstance, 0⟩ value).atPublication
            definition.anchor = some restored ∧
          SourceJudgment kernel restored definition.context definition.source) ∧
        (∃ aliased, (environment.extend ⟨site, .publishedInstance, 0⟩ value).aliasPublication
            definition.anchor instanceName = some aliased ∧
          JointJudgment kernel aliased (bindNames context site .local [instanceName]) rest) := by
  simp only [BuildJoint, clientRules, compile, compileForest, RuleForest.two,
    compilePremises, Satisfies, and_true]
  constructor
  · rintro ⟨value, admitted, localProof, ⟨restored, lookup, sourceProof⟩,
      ⟨aliased, aliasLookup, restProof⟩⟩
    exact ⟨value, admitted, localProof,
      ⟨restored, lookup, (reconstruction kernel _ _).mp sourceProof⟩,
      ⟨aliased, aliasLookup, (reconstruction kernel _ _).mp restProof⟩⟩
  · rintro ⟨value, admitted, localProof, ⟨restored, lookup, sourceProof⟩,
      ⟨aliased, aliasLookup, restProof⟩⟩
    exact ⟨value, admitted, localProof,
      ⟨restored, lookup, (reconstruction kernel _ _).mpr sourceProof⟩,
      ⟨aliased, aliasLookup, (reconstruction kernel _ _).mpr restProof⟩⟩

theorem description_extension_preserves_anchor {Value : Type} (environment : Environment Value)
    (binder target : Binder) (value : ScopedValue Value) (logical : binder.isEvent = false) :
    (environment.extend binder value).anchorKey target = environment.anchorKey target ∧
      (environment.extend binder value).anchors = environment.anchors ∧
      (environment.extend binder value).publications = environment.publications := by
  simp [Environment.extend, Environment.anchorKey, logical]

theorem admitted_candidate_payload_preserved {Value : Type} (environment : Environment Value)
    (binder : Binder) (candidate : ScopedValue Value) :
    environment.choose binder candidate = candidate := rfl

theorem future_invocation_reopens_history {Value : Type} (environment : Environment Value)
    (site arity : Nat) (candidate : ScopedValue Value) :
    (environment.extend ⟨site, .invocation, arity⟩ candidate).replay = none := rfl

theorem distinct_actual_occurrences {Value : Type} (binder : Binder)
    (parents : List (EventStep Value)) (data : Value)
    (first second : Nat) (different : first ≠ second) :
    ActualEvent.path ⟨parents, first⟩ binder data ≠ ActualEvent.path ⟨parents, second⟩ binder data := by
  intro same
  have tails := congrArg (fun path : List (EventStep Value) => path.drop parents.length) same
  simp [ActualEvent.path, EventStep.mk.injEq] at tails
  exact different tails

theorem distinct_challenge_payloads {Value : Type} (binder : Binder) (event : ActualEvent Value)
    (first second : Value) (different : first ≠ second) :
    event.path binder first ≠ event.path binder second := by
  intro same
  have tails := congrArg (fun path : List (EventStep Value) => path.drop event.parents.length) same
  simp [ActualEvent.path, EventStep.mk.injEq] at tails
  exact different tails

theorem restore_uses_captured_anchor {Value : Type} (environment : Environment Value)
    (record : PublicationRecord Value) (binder : Binder) :
    (environment.restore record).anchorKey binder =
      ⟨record.identity.origin, record.entryPath, binder⟩ ∧
    (environment.restore record).anchors = environment.anchors ∧
    (environment.restore record).publications = environment.publications := by
  exact ⟨rfl, rfl, rfl⟩

theorem alias_keeps_publication_identity {Value : Type} (environment : Environment Value)
    (original aliasName : Name) (identity : PublicationId Value)
    (lookup : environment.publicationName original = some identity) :
    (environment.aliasPublication original aliasName).map
        (fun aliased => aliased.publicationName aliasName) = some (some identity) := by
  simp only [Environment.aliasPublication, lookup]
  simp [Environment.publicationName]

theorem publication_candidate_retains_original_scope {Value : Type}
    (environment : Environment Value) (site : Site) (shared returned : Frame Value)
    (entry : InitializerEntry Value)
    (entryAt : (environment.initializers.dropWhile (fun entry => entry.site != site)).head? = some entry)
    (sharedAt : (environment.prefixAtShared site).getLast? = some shared)
    (returnedAt : (environment.prefixAtShared site).reverse.find? (fun frame =>
      frame.binder.site == site && frame.binder.kind == .returnRebind) = some returned)
    (sameEvent : shared.entryPath = returned.exitPath) :
    environment.publicationCandidate site = some
      (⟨environment.origin, site, returned.exitPath⟩,
       {identity := ⟨environment.origin, site, returned.exitPath⟩,
        entryPath := entry.path, entryNames := entry.names, entryFrames := entry.frames,
        captures := environment.names,
        fixedFrames := (environment.prefixAtShared site).filter (fun frame => frame.binder.isFixed),
        initializers := environment.initializers.dropWhile (fun entry => entry.site != site)}) := by
  simp [Environment.publicationCandidate, entryAt, sharedAt, returnedAt, sameEvent]

theorem initializer_entry_is_actual_scope {Value : Type} (environment : Environment Value)
    (site : Site) :
    (environment.enterInitializer site).initializers.head? =
      some ⟨site, environment.eventPath, environment.names,
        environment.frames.filter (fun frame => frame.binder.isFixed)⟩ ∧
      (environment.enterInitializer site).eventPath = environment.eventPath := by
  exact ⟨rfl, rfl⟩

theorem restore_uses_entry_snapshot {Value : Type} (environment : Environment Value)
    (record : PublicationRecord Value) :
    (environment.restore record).names = record.entryNames ∧
      (environment.restore record).frames = record.entryFrames ++
        environment.frames.filter (fun frame => !frame.binder.isFixed) ∧
      (environment.restore record).replay = some record.fixedFrames ∧
      (environment.restore record).initializers = record.initializers := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem event_extension_uses_actual_parent_and_payload {Value : Type}
    (environment : Environment Value) (binder : Binder) (candidate : ScopedValue Value)
    (actual : binder.isEvent = true) :
    (environment.extend binder candidate).eventPath =
      environment.eventPath ++ [⟨binder.site, binder.kind, candidate.event.occurrence, candidate.data⟩] := by
  simp [Environment.extend, ActualEvent.path, actual]

theorem scope_prefix_preserved {Value : Type} (environment : Environment Value)
    (binder : Binder) (value : ScopedValue Value) :
    (environment.extend binder value).root = environment.root ∧
      (environment.extend binder value).frames.take environment.frames.length = environment.frames := by
  simp [Environment.extend]

end YulangClosure.OriginalSource
