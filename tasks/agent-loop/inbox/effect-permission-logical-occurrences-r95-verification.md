# R95 primary execution authorization and verification receipt

Sprint: `EFFECT-PERMISSION-LOGICAL-OCCURRENCES/20261101-R95`.
This file is Luna's primary-owned exact execution authorization. It is effective
only after the commit containing these bytes is pushed to `origin/yulang3`.

## Pushed pre-execution authorization

Independent exact-input review: **PASS**, frozen at
`tasks/agent-loop/inbox/effect-permission-logical-occurrences-r95-input-review.md`,
SHA-256 `9b694c2c29ab4c3b88cfd456862ce101f5249d72cfa5cbee83d477ae1aa890a0`.
Reviewer measured 20 seconds of the 60-second grant. Its exact reconstructed
input is 106,897 bytes, SHA-256
`8bd62910afba8530f2140bd5b150db0d5fb5281c4651b87a88f78c51dc53d0d7`.
The R93 candidate remains SHA-256
`3c3ac12f0e652b361925ff0d80db78b4bae96f4bd2cc83f3f8346d6e5db54192`.

I authorize exactly one Lean invocation, only after this receipt is pushed:

```text
/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean --stdin -j1 -M1024
```

The reviewed stdin is assembled in memory from the three manifest-pinned source
files, no separator bytes, with only the two reviewed inter-module import lines
removed. No output file, scratch, cache, Lake build, test, project copy,
worktree, or environment is authorized. One Lean process only, capped at 120
seconds and 1,024 MiB. This receipt authorizes no repair or second call.

Primary authorization timestamp (UTC): 2026-10-31 16:55:31 UTC.
Authorization commit: the commit containing this receipt must be pushed before execution.
Lean execution status: **NOT RUN**.

## Execution result

Authorization commit: `64200c8997e55938670c9dccaac1351f0e4e558e`, pushed to
`origin/yulang3` before this call. State update commit
`abc8309c9bc01f6e1382d934b5116374c3f3ad95` was also pushed before execution.
The current local and remote HEADs matched at that commit before launch.

UTC start: 2026-10-31T16:56:35.571454+00:00.
UTC stop: 2026-10-31T16:56:48.146995+00:00.
Exact input: 106897 bytes, SHA-256 `8bd62910afba8530f2140bd5b150db0d5fb5281c4651b87a88f78c51dc53d0d7`.
Lean executable SHA-256: `bf8d54e4714cc4b03d3f6bb34c83b7202b87e49c8bfcbff6895c085bb90ceb38`.
Command: `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean --stdin -j1 -M1024`.
Lean process count: 1. Parallel jobs: 1. Memory cap: 1,024 MiB.
Wall time: 12.576 seconds; child peak RSS: 928752 KiB.
Timeout: NO.
Exit status: 1.

### Complete stdout

```text
<stdin>:1790:70: warning: This simp argument is unused:
  Prod.exists

Hint: Omit it from the simp argument list.
  [apply] simp [inventory, lookup, List.mem_map, eq_comm]

Note: This linter can be disabled with `set_option linter.unusedSimpArgs false`
<stdin>:1808:50: error: Tactic `apply` failed: could not unify the conclusion of `ih`
  lookup (encode ?scope ?cursor) route = observe ?scope ?cursor route
with the goal
  lookup (encodeForest scope children✝) route = observe scope (Cursor.forest children✝) route

Note: The full type of `ih` is
  ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route

case cons.tree.rule.false
route : List Bool
ih : ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route
scope : List ScopeFrame
rule✝ : Rule
site✝ : Site
context✝ : Context
premises✝ : List Premise
children✝ : RuleForest
⊢ lookup (encodeForest scope children✝) route = observe scope (Cursor.forest children✝) route
<stdin>:1808:50: error: Tactic `apply` failed: could not unify the conclusion of `ih`
  lookup (encode ?scope ?cursor) route = observe ?scope ?cursor route
with the goal
  lookup (encodeTree (scope ++ [ScopeFrame.existsE binder✝]) body✝) route =
    observe (scope ++ [ScopeFrame.existsE binder✝]) (Cursor.tree body✝) route

Note: The full type of `ih` is
  ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route

case cons.tree.existsE.false
route : List Bool
ih : ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route
scope : List ScopeFrame
binder✝ : Binder
body✝ : RuleTree
⊢ lookup (encodeTree (scope ++ [ScopeFrame.existsE binder✝]) body✝) route =
    observe (scope ++ [ScopeFrame.existsE binder✝]) (Cursor.tree body✝) route
<stdin>:1808:50: error: Tactic `apply` failed: could not unify the conclusion of `ih`
  lookup (encode ?scope ?cursor) route = observe ?scope ?cursor route
with the goal
  lookup (encodeTree (scope ++ [ScopeFrame.forallE binder✝]) body✝) route =
    observe (scope ++ [ScopeFrame.forallE binder✝]) (Cursor.tree body✝) route

Note: The full type of `ih` is
  ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route

case cons.tree.forallE.false
route : List Bool
ih : ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route
scope : List ScopeFrame
binder✝ : Binder
body✝ : RuleTree
⊢ lookup (encodeTree (scope ++ [ScopeFrame.forallE binder✝]) body✝) route =
    observe (scope ++ [ScopeFrame.forallE binder✝]) (Cursor.tree body✝) route
<stdin>:1808:50: error: Tactic `apply` failed: could not unify the conclusion of `ih`
  lookup (encode ?scope ?cursor) route = observe ?scope ?cursor route
with the goal
  lookup (encodeTree (scope ++ [ScopeFrame.initializerE site✝]) body✝) route =
    observe (scope ++ [ScopeFrame.initializerE site✝]) (Cursor.tree body✝) route

Note: The full type of `ih` is
  ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route

case cons.tree.initializerE.false
route : List Bool
ih : ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route
scope : List ScopeFrame
site✝ : Site
body✝ : RuleTree
⊢ lookup (encodeTree (scope ++ [ScopeFrame.initializerE site✝]) body✝) route =
    observe (scope ++ [ScopeFrame.initializerE site✝]) (Cursor.tree body✝) route
<stdin>:1808:50: error: Tactic `apply` failed: could not unify the conclusion of `ih`
  lookup (encode ?scope ?cursor) route = observe ?scope ?cursor route
with the goal
  lookup (encodeTree (scope ++ [ScopeFrame.executionE binder✝]) body✝) route =
    observe (scope ++ [ScopeFrame.executionE binder✝]) (Cursor.tree body✝) route

Note: The full type of `ih` is
  ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route

case cons.tree.executionE.false
route : List Bool
ih : ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route
scope : List ScopeFrame
binder✝ : Binder
body✝ : RuleTree
⊢ lookup (encodeTree (scope ++ [ScopeFrame.executionE binder✝]) body✝) route =
    observe (scope ++ [ScopeFrame.executionE binder✝]) (Cursor.tree body✝) route
<stdin>:1808:50: error: Tactic `apply` failed: could not unify the conclusion of `ih`
  lookup (encode ?scope ?cursor) route = observe ?scope ?cursor route
with the goal
  lookup (encodeTree (scope ++ [ScopeFrame.sharedE binder✝]) body✝) route =
    observe (scope ++ [ScopeFrame.sharedE binder✝]) (Cursor.tree body✝) route

Note: The full type of `ih` is
  ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route

case cons.tree.sharedE.false
route : List Bool
ih : ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route
scope : List ScopeFrame
binder✝ : Binder
body✝ : RuleTree
⊢ lookup (encodeTree (scope ++ [ScopeFrame.sharedE binder✝]) body✝) route =
    observe (scope ++ [ScopeFrame.sharedE binder✝]) (Cursor.tree body✝) route
<stdin>:1808:50: error: Tactic `apply` failed: could not unify the conclusion of `ih`
  lookup (encode ?scope ?cursor) route = observe ?scope ?cursor route
with the goal
  lookup (encodeTree (scope ++ [ScopeFrame.publishGroup bindings✝]) body✝) route =
    observe (scope ++ [ScopeFrame.publishGroup bindings✝]) (Cursor.tree body✝) route

Note: The full type of `ih` is
  ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route

case cons.tree.publishGroup.false
route : List Bool
ih : ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route
scope : List ScopeFrame
bindings✝ : List (Name × Site)
body✝ : RuleTree
⊢ lookup (encodeTree (scope ++ [ScopeFrame.publishGroup bindings✝]) body✝) route =
    observe (scope ++ [ScopeFrame.publishGroup bindings✝]) (Cursor.tree body✝) route
<stdin>:1808:50: error: Tactic `apply` failed: could not unify the conclusion of `ih`
  lookup (encode ?scope ?cursor) route = observe ?scope ?cursor route
with the goal
  lookup (encodeTree (scope ++ [ScopeFrame.atPublication binding✝]) body✝) route =
    observe (scope ++ [ScopeFrame.atPublication binding✝]) (Cursor.tree body✝) route

Note: The full type of `ih` is
  ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route

case cons.tree.atPublication.false
route : List Bool
ih : ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route
scope : List ScopeFrame
binding✝ : Name
body✝ : RuleTree
⊢ lookup (encodeTree (scope ++ [ScopeFrame.atPublication binding✝]) body✝) route =
    observe (scope ++ [ScopeFrame.atPublication binding✝]) (Cursor.tree body✝) route
<stdin>:1808:50: error: Tactic `apply` failed: could not unify the conclusion of `ih`
  lookup (encode ?scope ?cursor) route = observe ?scope ?cursor route
with the goal
  lookup (encodeTree (scope ++ [ScopeFrame.aliasPublication original✝ aliasName✝]) body✝) route =
    observe (scope ++ [ScopeFrame.aliasPublication original✝ aliasName✝]) (Cursor.tree body✝) route

Note: The full type of `ih` is
  ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route

case cons.tree.aliasPublication.false
route : List Bool
ih : ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route
scope : List ScopeFrame
original✝ aliasName✝ : Name
body✝ : RuleTree
⊢ lookup (encodeTree (scope ++ [ScopeFrame.aliasPublication original✝ aliasName✝]) body✝) route =
    observe (scope ++ [ScopeFrame.aliasPublication original✝ aliasName✝]) (Cursor.tree body✝) route
<stdin>:1808:50: error: Tactic `apply` failed: could not unify the conclusion of `ih`
  lookup (encode ?scope ?cursor) route = observe ?scope ?cursor route
with the goal
  lookup (encodeTree scope left✝) route = observe scope (Cursor.tree left✝) route

Note: The full type of `ih` is
  ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route

case cons.tree.choice.false
route : List Bool
ih : ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route
scope : List ScopeFrame
site✝ : Site
left✝ right✝ : RuleTree
⊢ lookup (encodeTree scope left✝) route = observe scope (Cursor.tree left✝) route
<stdin>:1808:50: error: Tactic `apply` failed: could not unify the conclusion of `ih`
  lookup (encode ?scope ?cursor) route = observe ?scope ?cursor route
with the goal
  lookup (encodeTree scope right✝) route = observe scope (Cursor.tree right✝) route

Note: The full type of `ih` is
  ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route

case cons.tree.choice.true
route : List Bool
ih : ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route
scope : List ScopeFrame
site✝ : Site
left✝ right✝ : RuleTree
⊢ lookup (encodeTree scope right✝) route = observe scope (Cursor.tree right✝) route
<stdin>:1812:50: error: Tactic `apply` failed: could not unify the conclusion of `ih`
  lookup (encode ?scope ?cursor) route = observe ?scope ?cursor route
with the goal
  lookup (encodeTree scope head✝) route = observe scope (Cursor.tree head✝) route

Note: The full type of `ih` is
  ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route

case cons.forest.cons.false
route : List Bool
ih : ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route
scope : List ScopeFrame
head✝ : RuleTree
tail✝ : RuleForest
⊢ lookup (encodeTree scope head✝) route = observe scope (Cursor.tree head✝) route
<stdin>:1812:50: error: Tactic `apply` failed: could not unify the conclusion of `ih`
  lookup (encode ?scope ?cursor) route = observe ?scope ?cursor route
with the goal
  lookup (encodeForest scope tail✝) route = observe scope (Cursor.forest tail✝) route

Note: The full type of `ih` is
  ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route

case cons.forest.cons.true
route : List Bool
ih : ∀ (scope : List ScopeFrame) (cursor : Cursor), lookup (encode scope cursor) route = observe scope cursor route
scope : List ScopeFrame
head✝ : RuleTree
tail✝ : RuleForest
⊢ lookup (encodeForest scope tail✝) route = observe scope (Cursor.forest tail✝) route
<stdin>:1883:35: error: Application type mismatch: The argument
  hfollow
has type
  follow scope (Cursor.tree (sourceRules context source)) route =
    some { enclosing := enclosing, cursor := Cursor.tree (RuleTree.existsE binder body) }
but is expected to have type
  some { enclosing := enclosing, cursor := Cursor.tree (RuleTree.existsE binder body) } =
    some
      { enclosing := { binder := binder, enclosing := enclosing, subtree := body }.enclosing,
        cursor := Cursor.tree (RuleTree.existsE binder body) }
in the application
  And.intro hfollow
<stdin>:1902:8: error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.descriptorFormation` could not be determined

Hint: Using `AtomKind.descriptorFormation would be unambiguous:
  [apply] `AtomKind.descriptorFormation`
<stdin>:1902:30: error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.wholeArgumentCompatibility` could not be determined

Hint: Using `AtomKind.wholeArgumentCompatibility would be unambiguous:
  [apply] `AtomKind.wholeArgumentCompatibility`
<stdin>:1903:8: error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.completeCallCertificate` could not be determined

Hint: Using `AtomKind.completeCallCertificate would be unambiguous:
  [apply] `AtomKind.completeCallCertificate`
<stdin>:1903:34: error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.sourceCallIncidence` could not be determined

Hint: Using `AtomKind.sourceCallIncidence would be unambiguous:
  [apply] `AtomKind.sourceCallIncidence`
<stdin>:1903:56: error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.callableImage` could not be determined

Hint: Using one of these would be unambiguous:
  [apply] `AtomKind.callableImage`
  [apply] `Port.callableImage`
<stdin>:1904:61: error(lean.invalidDottedIdent): Invalid dotted identifier notation: The expected type of `.roleAndInitialCallOrigin` could not be determined

Hint: Using `AtomKind.roleAndInitialCallOrigin would be unambiguous:
  [apply] `AtomKind.roleAndInitialCallOrigin`
<stdin>:1918:51: error: Tactic `rfl` failed: The left-hand side
  observe scope
    (Cursor.tree
      (annotated { site := site } context
        (RuleTree.existsE { site := site, kind := BinderKind.viewLogic }
          (RuleTree.rule Rule.app site context
            (premises
                ([AtomKind.descriptorFormation, AtomKind.wholeArgumentCompatibility, AtomKind.completeCallCertificate,
                    AtomKind.sourceCallIncidence, AtomKind.callableImage] ++
                  if singletonFormalCall context callee argument = true then [AtomKind.roleAndInitialCallOrigin]
                  else [])
                site context [callee.site, argument.site] ++
              [check CheckMode.value site context (endpoint callee.site Port.returnedValue)
                  (endpoint site Port.descriptor),
                check CheckMode.computation site context (endpoint site Port.callableImage)
                  (endpoint site Port.synthesis)])
            (RuleForest.two (sourceRules context callee) (sourceRules context argument))))))
    (annotationRoute { site := site })
is not definitionally equal to the right-hand side
  some
    { binder := { site := site, kind := BinderKind.viewLogic }, enclosing := scope,
      subtree := appRule context { site := site } callee argument }

case none
context : Context
callee argument : Source Category.expression
scope : List ScopeFrame
site : Site
⊢ observe scope
      (Cursor.tree
        (annotated { site := site } context
          (RuleTree.existsE { site := site, kind := BinderKind.viewLogic }
            (RuleTree.rule Rule.app site context
              (premises
                  ([AtomKind.descriptorFormation, AtomKind.wholeArgumentCompatibility, AtomKind.completeCallCertificate,
                      AtomKind.sourceCallIncidence, AtomKind.callableImage] ++
                    if singletonFormalCall context callee argument = true then [AtomKind.roleAndInitialCallOrigin]
                    else [])
                  site context [callee.site, argument.site] ++
                [check CheckMode.value site context (endpoint callee.site Port.returnedValue)
                    (endpoint site Port.descriptor),
                  check CheckMode.computation site context (endpoint site Port.callableImage)
                    (endpoint site Port.synthesis)])
              (RuleForest.two (sourceRules context callee) (sourceRules context argument))))))
      (annotationRoute { site := site }) =
    some
      { binder := { site := site, kind := BinderKind.viewLogic }, enclosing := scope,
        subtree := appRule context { site := site } callee argument }
<stdin>:1918:51: error: Tactic `rfl` failed: The left-hand side
  observe scope
    (Cursor.tree
      (annotated { site := site, annotation := some val✝ } context
        (RuleTree.existsE { site := site, kind := BinderKind.viewLogic }
          (RuleTree.rule Rule.app site context
            (premises
                ([AtomKind.descriptorFormation, AtomKind.wholeArgumentCompatibility, AtomKind.completeCallCertificate,
                    AtomKind.sourceCallIncidence, AtomKind.callableImage] ++
                  if singletonFormalCall context callee argument = true then [AtomKind.roleAndInitialCallOrigin]
                  else [])
                site context [callee.site, argument.site] ++
              [check CheckMode.value site context (endpoint callee.site Port.returnedValue)
                  (endpoint site Port.descriptor),
                check CheckMode.computation site context (endpoint site Port.callableImage)
                  (endpoint site Port.synthesis)])
            (RuleForest.two (sourceRules context callee) (sourceRules context argument))))))
    (annotationRoute { site := site, annotation := some val✝ })
is not definitionally equal to the right-hand side
  some
    { binder := { site := site, kind := BinderKind.viewLogic }, enclosing := scope,
      subtree := appRule context { site := site, annotation := some val✝ } callee argument }

case some
context : Context
callee argument : Source Category.expression
scope : List ScopeFrame
site : Site
val✝ : Annotation
⊢ observe scope
      (Cursor.tree
        (annotated { site := site, annotation := some val✝ } context
          (RuleTree.existsE { site := site, kind := BinderKind.viewLogic }
            (RuleTree.rule Rule.app site context
              (premises
                  ([AtomKind.descriptorFormation, AtomKind.wholeArgumentCompatibility, AtomKind.completeCallCertificate,
                      AtomKind.sourceCallIncidence, AtomKind.callableImage] ++
                    if singletonFormalCall context callee argument = true then [AtomKind.roleAndInitialCallOrigin]
                    else [])
                  site context [callee.site, argument.site] ++
                [check CheckMode.value site context (endpoint callee.site Port.returnedValue)
                    (endpoint site Port.descriptor),
                  check CheckMode.computation site context (endpoint site Port.callableImage)
                    (endpoint site Port.synthesis)])
              (RuleForest.two (sourceRules context callee) (sourceRules context argument))))))
      (annotationRoute { site := site, annotation := some val✝ }) =
    some
      { binder := { site := site, kind := BinderKind.viewLogic }, enclosing := scope,
        subtree := appRule context { site := site, annotation := some val✝ } callee argument }
<stdin>:1961:54: error: unsolved goals
case none.false
context : Context
pattern : Source Category.pattern
body : Source Category.expression
scope : List ScopeFrame
site formalSite : Site
formalName : Name
formalAnnotation : Option Annotation
⊢ ((match
          Cursor.tree
            (annotated { site := site } context
              (RuleTree.existsE { site := formalSite, kind := BinderKind.description }
                (RuleTree.existsE { site := site, kind := BinderKind.viewLogic }
                  (node Rule.lambda site context [AtomKind.captureWholeEnvironment, AtomKind.closureFormation]
                    [formalSite, pattern.site, body.site]
                    (RuleForest.cons
                      (RuleTree.forallE { site := site, kind := BinderKind.invocation }
                        (RuleTree.existsE { site := formalSite, kind := BinderKind.receipt }
                          (RuleTree.rule Rule.parameterEntry formalSite
                            ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                annotation := formalAnnotation, entry := some Entry.value,
                                singleUse := Source.nameCount formalName body == 1 } ::
                              context)
                            (Premise.atom
                                {
                                  kind :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).kind,
                                  site :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).site,
                                  context :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).context,
                                  operands :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).operands,
                                  order :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).order,
                                  names :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).names,
                                  declaration :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).declaration,
                                  annotation := formalAnnotation,
                                  annotations :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).annotations,
                                  labels :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).labels,
                                  flag :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).flag,
                                  arity :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).arity,
                                  merges :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).merges,
                                  literal :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).literal,
                                  entry := some Entry.value,
                                  binding :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).binding } ::
                              premises [AtomKind.receiptFormation, AtomKind.entryForceReturnRebind] formalSite
                                ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                    annotation := formalAnnotation, entry := some Entry.value,
                                    singleUse := Source.nameCount formalName body == 1 } ::
                                  context)
                                [site, pattern.site, body.site])
                            (RuleForest.cons
                              (suffix formalSite
                                (RuleTree.sharedE { site := formalSite, kind := BinderKind.shared }
                                  (RuleTree.rule Rule.sequence formalSite
                                    ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                        annotation := formalAnnotation, entry := some Entry.value,
                                        singleUse := Source.nameCount formalName body == 1 } ::
                                      context)
                                    []
                                    (RuleForest.cons
                                      (sourceRules
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)
                                        pattern)
                                      (RuleForest.cons
                                        (RuleTree.existsE { site := body.site, kind := BinderKind.eventProof }
                                          (RuleTree.rule Rule.sequence body.site
                                            (patternContext
                                              ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                                  annotation := formalAnnotation, entry := some Entry.value,
                                                  singleUse := Source.nameCount formalName body == 1 } ::
                                                context)
                                              pattern)
                                            (premises
                                                [AtomKind.completeBodyConsumer, AtomKind.actualReturnOrPendingSuffix]
                                                body.site
                                                (patternContext
                                                  ({ name := formalName, owner := formalSite,
                                                      kind := BindingKind.formal, annotation := formalAnnotation,
                                                      entry := some Entry.value,
                                                      singleUse := Source.nameCount formalName body == 1 } ::
                                                    context)
                                                  pattern)
                                                [site, formalSite] ++
                                              [check CheckMode.computation body.site
                                                  (patternContext
                                                    ({ name := formalName, owner := formalSite,
                                                        kind := BindingKind.formal, annotation := formalAnnotation,
                                                        entry := some Entry.value,
                                                        singleUse := Source.nameCount formalName body == 1 } ::
                                                      context)
                                                    pattern)
                                                  (endpoint body.site) (endpoint site Port.bodyConsumer)])
                                            (RuleForest.cons
                                              (sourceRules
                                                (patternContext
                                                  ({ name := formalName, owner := formalSite,
                                                      kind := BindingKind.formal, annotation := formalAnnotation,
                                                      entry := some Entry.value,
                                                      singleUse := Source.nameCount formalName body == 1 } ::
                                                    context)
                                                  pattern)
                                                body)
                                              RuleForest.nil)))
                                        RuleForest.nil)))))
                              RuleForest.nil))))
                      RuleForest.nil))))),
          false with
        | Cursor.tree (RuleTree.rule rule site context premises children), false =>
          some { enclosing := scope, cursor := Cursor.forest children }
        | Cursor.tree (RuleTree.existsE binder body), false =>
          some { enclosing := scope ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.forallE binder body), false =>
          some { enclosing := scope ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.initializerE site body), false =>
          some { enclosing := scope ++ [ScopeFrame.initializerE site], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.executionE binder body), false =>
          some { enclosing := scope ++ [ScopeFrame.executionE binder], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.sharedE binder body), false =>
          some { enclosing := scope ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.publishGroup bindings body), false =>
          some { enclosing := scope ++ [ScopeFrame.publishGroup bindings], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.atPublication binding body), false =>
          some { enclosing := scope ++ [ScopeFrame.atPublication binding], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
          some { enclosing := scope ++ [ScopeFrame.aliasPublication original aliasName], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.choice site left right), false =>
          some { enclosing := scope, cursor := Cursor.tree left }
        | Cursor.tree (RuleTree.choice site left right), true =>
          some { enclosing := scope, cursor := Cursor.tree right }
        | Cursor.forest (RuleForest.cons head tail), false => some { enclosing := scope, cursor := Cursor.tree head }
        | Cursor.forest (RuleForest.cons head tail), true => some { enclosing := scope, cursor := Cursor.forest tail }
        | x, x_1 => none).bind
      fun position =>
      (match position.cursor, false with
          | Cursor.tree (RuleTree.rule rule site context premises children), false =>
            some { enclosing := position.enclosing, cursor := Cursor.forest children }
          | Cursor.tree (RuleTree.existsE binder body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.forallE binder body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.initializerE site body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.initializerE site], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.executionE binder body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.executionE binder], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.sharedE binder body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.publishGroup bindings body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.atPublication binding body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
            some
              { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.choice site left right), false =>
            some { enclosing := position.enclosing, cursor := Cursor.tree left }
          | Cursor.tree (RuleTree.choice site left right), true =>
            some { enclosing := position.enclosing, cursor := Cursor.tree right }
          | Cursor.forest (RuleForest.cons head tail), false =>
            some { enclosing := position.enclosing, cursor := Cursor.tree head }
          | Cursor.forest (RuleForest.cons head tail), true =>
            some { enclosing := position.enclosing, cursor := Cursor.forest tail }
          | x, x_1 => none).bind
        fun position =>
        (match position.cursor, false with
            | Cursor.tree (RuleTree.rule rule site context premises children), false =>
              some { enclosing := position.enclosing, cursor := Cursor.forest children }
            | Cursor.tree (RuleTree.existsE binder body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.forallE binder body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.initializerE site body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.initializerE site], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.executionE binder body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.executionE binder], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.sharedE binder body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.publishGroup bindings body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.atPublication binding body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
              some
                { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                  cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.choice site left right), false =>
              some { enclosing := position.enclosing, cursor := Cursor.tree left }
            | Cursor.tree (RuleTree.choice site left right), true =>
              some { enclosing := position.enclosing, cursor := Cursor.tree right }
            | Cursor.forest (RuleForest.cons head tail), false =>
              some { enclosing := position.enclosing, cursor := Cursor.tree head }
            | Cursor.forest (RuleForest.cons head tail), true =>
              some { enclosing := position.enclosing, cursor := Cursor.forest tail }
            | x, x_1 => none).bind
          fun position =>
          (match position.cursor, false with
              | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                some { enclosing := position.enclosing, cursor := Cursor.forest children }
              | Cursor.tree (RuleTree.existsE binder body), false =>
                some { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.forallE binder body), false =>
                some { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.initializerE site body), false =>
                some { enclosing := position.enclosing ++ [ScopeFrame.initializerE site], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.executionE binder body), false =>
                some { enclosing := position.enclosing ++ [ScopeFrame.executionE binder], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.sharedE binder body), false =>
                some { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                some
                  { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.atPublication binding body), false =>
                some
                  { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                some
                  { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                    cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.choice site left right), false =>
                some { enclosing := position.enclosing, cursor := Cursor.tree left }
              | Cursor.tree (RuleTree.choice site left right), true =>
                some { enclosing := position.enclosing, cursor := Cursor.tree right }
              | Cursor.forest (RuleForest.cons head tail), false =>
                some { enclosing := position.enclosing, cursor := Cursor.tree head }
              | Cursor.forest (RuleForest.cons head tail), true =>
                some { enclosing := position.enclosing, cursor := Cursor.forest tail }
              | x, x_1 => none).bind
            fun position =>
            (match position.cursor, false with
                | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                  some { enclosing := position.enclosing, cursor := Cursor.forest children }
                | Cursor.tree (RuleTree.existsE binder body), false =>
                  some { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.forallE binder body), false =>
                  some { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.initializerE site body), false =>
                  some { enclosing := position.enclosing ++ [ScopeFrame.initializerE site], cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.executionE binder body), false =>
                  some { enclosing := position.enclosing ++ [ScopeFrame.executionE binder], cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.sharedE binder body), false =>
                  some { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                  some
                    { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                      cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.atPublication binding body), false =>
                  some
                    { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                      cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                  some
                    { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                      cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.choice site left right), false =>
                  some { enclosing := position.enclosing, cursor := Cursor.tree left }
                | Cursor.tree (RuleTree.choice site left right), true =>
                  some { enclosing := position.enclosing, cursor := Cursor.tree right }
                | Cursor.forest (RuleForest.cons head tail), false =>
                  some { enclosing := position.enclosing, cursor := Cursor.tree head }
                | Cursor.forest (RuleForest.cons head tail), true =>
                  some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                | x, x_1 => none).bind
              fun position =>
              (match position.cursor, false with
                  | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                    some { enclosing := position.enclosing, cursor := Cursor.forest children }
                  | Cursor.tree (RuleTree.existsE binder body), false =>
                    some { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.forallE binder body), false =>
                    some { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.initializerE site body), false =>
                    some
                      { enclosing := position.enclosing ++ [ScopeFrame.initializerE site], cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.executionE binder body), false =>
                    some
                      { enclosing := position.enclosing ++ [ScopeFrame.executionE binder], cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.sharedE binder body), false =>
                    some { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                    some
                      { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                        cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.atPublication binding body), false =>
                    some
                      { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                        cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                    some
                      { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                        cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.choice site left right), false =>
                    some { enclosing := position.enclosing, cursor := Cursor.tree left }
                  | Cursor.tree (RuleTree.choice site left right), true =>
                    some { enclosing := position.enclosing, cursor := Cursor.tree right }
                  | Cursor.forest (RuleForest.cons head tail), false =>
                    some { enclosing := position.enclosing, cursor := Cursor.tree head }
                  | Cursor.forest (RuleForest.cons head tail), true =>
                    some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                  | x, x_1 => none).bind
                fun position =>
                (match position.cursor, false with
                    | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                      some { enclosing := position.enclosing, cursor := Cursor.forest children }
                    | Cursor.tree (RuleTree.existsE binder body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.forallE binder body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.initializerE site body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                          cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.executionE binder body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                          cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.sharedE binder body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                          cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.atPublication binding body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                          cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                          cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.choice site left right), false =>
                      some { enclosing := position.enclosing, cursor := Cursor.tree left }
                    | Cursor.tree (RuleTree.choice site left right), true =>
                      some { enclosing := position.enclosing, cursor := Cursor.tree right }
                    | Cursor.forest (RuleForest.cons head tail), false =>
                      some { enclosing := position.enclosing, cursor := Cursor.tree head }
                    | Cursor.forest (RuleForest.cons head tail), true =>
                      some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                    | x, x_1 => none).bind
                  fun position =>
                  (match position.cursor, false with
                      | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                        some { enclosing := position.enclosing, cursor := Cursor.forest children }
                      | Cursor.tree (RuleTree.existsE binder body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.forallE binder body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.initializerE site body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                            cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.executionE binder body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                            cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.sharedE binder body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                            cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.atPublication binding body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                            cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                            cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.choice site left right), false =>
                        some { enclosing := position.enclosing, cursor := Cursor.tree left }
                      | Cursor.tree (RuleTree.choice site left right), true =>
                        some { enclosing := position.enclosing, cursor := Cursor.tree right }
                      | Cursor.forest (RuleForest.cons head tail), false =>
                        some { enclosing := position.enclosing, cursor := Cursor.tree head }
                      | Cursor.forest (RuleForest.cons head tail), true =>
                        some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                      | x, x_1 => none).bind
                    fun position =>
                    (match position.cursor, false with
                        | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                          some { enclosing := position.enclosing, cursor := Cursor.forest children }
                        | Cursor.tree (RuleTree.existsE binder body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.existsE binder],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.forallE binder body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.forallE binder],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.initializerE site body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.executionE binder body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.sharedE binder body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.atPublication binding body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.choice site left right), false =>
                          some { enclosing := position.enclosing, cursor := Cursor.tree left }
                        | Cursor.tree (RuleTree.choice site left right), true =>
                          some { enclosing := position.enclosing, cursor := Cursor.tree right }
                        | Cursor.forest (RuleForest.cons head tail), false =>
                          some { enclosing := position.enclosing, cursor := Cursor.tree head }
                        | Cursor.forest (RuleForest.cons head tail), true =>
                          some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                        | x, x_1 => none).bind
                      fun position =>
                      (match position.cursor, false with
                          | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                            some { enclosing := position.enclosing, cursor := Cursor.forest children }
                          | Cursor.tree (RuleTree.existsE binder body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.existsE binder],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.forallE binder body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.forallE binder],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.initializerE site body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.executionE binder body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.sharedE binder body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.atPublication binding body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.choice site left right), false =>
                            some { enclosing := position.enclosing, cursor := Cursor.tree left }
                          | Cursor.tree (RuleTree.choice site left right), true =>
                            some { enclosing := position.enclosing, cursor := Cursor.tree right }
                          | Cursor.forest (RuleForest.cons head tail), false =>
                            some { enclosing := position.enclosing, cursor := Cursor.tree head }
                          | Cursor.forest (RuleForest.cons head tail), true =>
                            some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                          | x, x_1 => none).bind
                        fun position =>
                        (match position.cursor, false with
                            | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                              some { enclosing := position.enclosing, cursor := Cursor.forest children }
                            | Cursor.tree (RuleTree.existsE binder body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.existsE binder],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.forallE binder body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.forallE binder],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.initializerE site body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.executionE binder body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.sharedE binder body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.atPublication binding body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.choice site left right), false =>
                              some { enclosing := position.enclosing, cursor := Cursor.tree left }
                            | Cursor.tree (RuleTree.choice site left right), true =>
                              some { enclosing := position.enclosing, cursor := Cursor.tree right }
                            | Cursor.forest (RuleForest.cons head tail), false =>
                              some { enclosing := position.enclosing, cursor := Cursor.tree head }
                            | Cursor.forest (RuleForest.cons head tail), true =>
                              some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                            | x, x_1 => none).bind
                          fun position =>
                          (match position.cursor, true with
                              | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                                some { enclosing := position.enclosing, cursor := Cursor.forest children }
                              | Cursor.tree (RuleTree.existsE binder body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.existsE binder],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.forallE binder body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.forallE binder],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.initializerE site body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.executionE binder body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.sharedE binder body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.atPublication binding body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.choice site left right), false =>
                                some { enclosing := position.enclosing, cursor := Cursor.tree left }
                              | Cursor.tree (RuleTree.choice site left right), true =>
                                some { enclosing := position.enclosing, cursor := Cursor.tree right }
                              | Cursor.forest (RuleForest.cons head tail), false =>
                                some { enclosing := position.enclosing, cursor := Cursor.tree head }
                              | Cursor.forest (RuleForest.cons head tail), true =>
                                some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                              | x, x_1 => none).bind
                            fun position =>
                            (match position.cursor, false with
                                | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                                  some { enclosing := position.enclosing, cursor := Cursor.forest children }
                                | Cursor.tree (RuleTree.existsE binder body), false =>
                                  some
                                    { enclosing := position.enclosing ++ [ScopeFrame.existsE binder],
                                      cursor := Cursor.tree body }
                                | Cursor.tree (RuleTree.forallE binder body), false =>
                                  some
                                    { enclosing := position.enclosing ++ [ScopeFrame.forallE binder],
                                      cursor := Cursor.tree body }
                                | Cursor.tree (RuleTree.initializerE site body), false =>
                                  some
                                    { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                                      cursor := Cursor.tree body }
                                | Cursor.tree (RuleTree.executionE binder body), false =>
                                  some
                                    { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                                      cursor := Cursor.tree body }
                                | Cursor.tree (RuleTree.sharedE binder body), false =>
                                  some
                                    { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder],
                                      cursor := Cursor.tree body }
                                | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                                  some
                                    { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                                      cursor := Cursor.tree body }
                                | Cursor.tree (RuleTree.atPublication binding body), false =>
                                  some
                                    { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                                      cursor := Cursor.tree body }
                                | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                                  some
                                    {
                                      enclosing :=
                                        position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                                      cursor := Cursor.tree body }
                                | Cursor.tree (RuleTree.choice site left right), false =>
                                  some { enclosing := position.enclosing, cursor := Cursor.tree left }
                                | Cursor.tree (RuleTree.choice site left right), true =>
                                  some { enclosing := position.enclosing, cursor := Cursor.tree right }
                                | Cursor.forest (RuleForest.cons head tail), false =>
                                  some { enclosing := position.enclosing, cursor := Cursor.tree head }
                                | Cursor.forest (RuleForest.cons head tail), true =>
                                  some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                                | x, x_1 => none).bind
                              fun position =>
                              match position.cursor with
                              | Cursor.tree (RuleTree.existsE binder body) =>
                                if
                                    (match binder.kind with
                                      | BinderKind.viewLogic => true
                                      | BinderKind.eventProof => true
                                      | BinderKind.publishedInstance => true
                                      | x => false) =
                                      true then
                                  some { binder := binder, enclosing := position.enclosing, subtree := body }
                                else none
                              | x => none) =
    some
      { binder := { site := body.site, kind := BinderKind.eventProof },
        enclosing :=
          scope ++
            ([ScopeFrame.existsE { site := formalSite, kind := BinderKind.description },
                ScopeFrame.existsE { site := site, kind := BinderKind.viewLogic },
                ScopeFrame.forallE { site := site, kind := BinderKind.invocation },
                ScopeFrame.existsE { site := formalSite, kind := BinderKind.receipt }] ++
              ([ScopeFrame.executionE { site := formalSite, kind := BinderKind.returnRebind }] ++
                [ScopeFrame.sharedE { site := formalSite, kind := BinderKind.shared }])),
        subtree :=
          RuleTree.rule Rule.sequence body.site
            (List.filter
                (fun binding =>
                  !(formalName == binding.name || List.any context fun prior => prior.name == binding.name))
                pattern.bindingRecords ++
              { name := formalName, owner := formalSite, kind := BindingKind.formal, annotation := formalAnnotation,
                  entry := some Entry.value, singleUse := Source.nameCount formalName body == 1 } ::
                context)
            (List.map
                (fun kind =>
                  Premise.atom
                    (atom kind body.site
                      (List.filter
                          (fun binding =>
                            !(formalName == binding.name || List.any context fun prior => prior.name == binding.name))
                          pattern.bindingRecords ++
                        { name := formalName, owner := formalSite, kind := BindingKind.formal,
                            annotation := formalAnnotation, entry := some Entry.value,
                            singleUse := Source.nameCount formalName body == 1 } ::
                          context)
                      [site, formalSite]))
                [AtomKind.completeBodyConsumer, AtomKind.actualReturnOrPendingSuffix] ++
              [Premise.checking
                  { mode := CheckMode.computation, site := body.site,
                    context :=
                      List.filter
                          (fun binding =>
                            !(formalName == binding.name || List.any context fun prior => prior.name == binding.name))
                          pattern.bindingRecords ++
                        { name := formalName, owner := formalSite, kind := BindingKind.formal,
                            annotation := formalAnnotation, entry := some Entry.value,
                            singleUse := Source.nameCount formalName body == 1 } ::
                          context,
                    lower := { site := body.site, port := Port.finalRoot },
                    upper := { site := site, port := Port.bodyConsumer } }])
            (RuleForest.cons
              (sourceRules
                (List.filter
                    (fun binding =>
                      !(formalName == binding.name || List.any context fun prior => prior.name == binding.name))
                    pattern.bindingRecords ++
                  { name := formalName, owner := formalSite, kind := BindingKind.formal, annotation := formalAnnotation,
                      entry := some Entry.value, singleUse := Source.nameCount formalName body == 1 } ::
                    context)
                body)
              RuleForest.nil) }

case none.true
context : Context
pattern : Source Category.pattern
body : Source Category.expression
scope : List ScopeFrame
site formalSite : Site
formalName : Name
formalAnnotation : Option Annotation
⊢ ((match
          Cursor.tree
            (annotated { site := site } context
              (RuleTree.existsE { site := formalSite, kind := BinderKind.description }
                (RuleTree.existsE { site := site, kind := BinderKind.viewLogic }
                  (node Rule.lambda site context [AtomKind.captureWholeEnvironment, AtomKind.closureFormation]
                    [formalSite, pattern.site, body.site]
                    (RuleForest.cons
                      (RuleTree.forallE { site := site, kind := BinderKind.invocation }
                        (RuleTree.existsE { site := formalSite, kind := BinderKind.receipt }
                          (RuleTree.rule Rule.parameterEntry formalSite
                            ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                annotation := formalAnnotation, entry := some Entry.computation,
                                singleUse := Source.nameCount formalName body == 1 } ::
                              context)
                            (Premise.atom
                                {
                                  kind :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).kind,
                                  site :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).site,
                                  context :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).context,
                                  operands :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).operands,
                                  order :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).order,
                                  names :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).names,
                                  declaration :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).declaration,
                                  annotation := formalAnnotation,
                                  annotations :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).annotations,
                                  labels :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).labels,
                                  flag :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).flag,
                                  arity :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).arity,
                                  merges :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).merges,
                                  literal :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).literal,
                                  entry := some Entry.computation,
                                  binding :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).binding } ::
                              premises [AtomKind.receiptFormation, AtomKind.retainedEntry] formalSite
                                ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                    annotation := formalAnnotation, entry := some Entry.computation,
                                    singleUse := Source.nameCount formalName body == 1 } ::
                                  context)
                                [site, pattern.site, body.site])
                            (RuleForest.cons
                              (RuleTree.sharedE { site := formalSite, kind := BinderKind.shared }
                                (RuleTree.rule Rule.sequence formalSite
                                  ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                      annotation := formalAnnotation, entry := some Entry.computation,
                                      singleUse := Source.nameCount formalName body == 1 } ::
                                    context)
                                  []
                                  (RuleForest.cons
                                    (sourceRules
                                      ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                          annotation := formalAnnotation, entry := some Entry.computation,
                                          singleUse := Source.nameCount formalName body == 1 } ::
                                        context)
                                      pattern)
                                    (RuleForest.cons
                                      (RuleTree.existsE { site := body.site, kind := BinderKind.eventProof }
                                        (RuleTree.rule Rule.sequence body.site
                                          (patternContext
                                            ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                                annotation := formalAnnotation, entry := some Entry.computation,
                                                singleUse := Source.nameCount formalName body == 1 } ::
                                              context)
                                            pattern)
                                          (premises
                                              [AtomKind.completeBodyConsumer, AtomKind.actualReturnOrPendingSuffix]
                                              body.site
                                              (patternContext
                                                ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                                    annotation := formalAnnotation, entry := some Entry.computation,
                                                    singleUse := Source.nameCount formalName body == 1 } ::
                                                  context)
                                                pattern)
                                              [site, formalSite] ++
                                            [check CheckMode.computation body.site
                                                (patternContext
                                                  ({ name := formalName, owner := formalSite,
                                                      kind := BindingKind.formal, annotation := formalAnnotation,
                                                      entry := some Entry.computation,
                                                      singleUse := Source.nameCount formalName body == 1 } ::
                                                    context)
                                                  pattern)
                                                (endpoint body.site) (endpoint site Port.bodyConsumer)])
                                          (RuleForest.cons
                                            (sourceRules
                                              (patternContext
                                                ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                                    annotation := formalAnnotation, entry := some Entry.computation,
                                                    singleUse := Source.nameCount formalName body == 1 } ::
                                                  context)
                                                pattern)
                                              body)
                                            RuleForest.nil)))
                                      RuleForest.nil))))
                              RuleForest.nil))))
                      RuleForest.nil))))),
          false with
        | Cursor.tree (RuleTree.rule rule site context premises children), false =>
          some { enclosing := scope, cursor := Cursor.forest children }
        | Cursor.tree (RuleTree.existsE binder body), false =>
          some { enclosing := scope ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.forallE binder body), false =>
          some { enclosing := scope ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.initializerE site body), false =>
          some { enclosing := scope ++ [ScopeFrame.initializerE site], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.executionE binder body), false =>
          some { enclosing := scope ++ [ScopeFrame.executionE binder], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.sharedE binder body), false =>
          some { enclosing := scope ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.publishGroup bindings body), false =>
          some { enclosing := scope ++ [ScopeFrame.publishGroup bindings], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.atPublication binding body), false =>
          some { enclosing := scope ++ [ScopeFrame.atPublication binding], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
          some { enclosing := scope ++ [ScopeFrame.aliasPublication original aliasName], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.choice site left right), false =>
          some { enclosing := scope, cursor := Cursor.tree left }
        | Cursor.tree (RuleTree.choice site left right), true =>
          some { enclosing := scope, cursor := Cursor.tree right }
        | Cursor.forest (RuleForest.cons head tail), false => some { enclosing := scope, cursor := Cursor.tree head }
        | Cursor.forest (RuleForest.cons head tail), true => some { enclosing := scope, cursor := Cursor.forest tail }
        | x, x_1 => none).bind
      fun position =>
      (match position.cursor, false with
          | Cursor.tree (RuleTree.rule rule site context premises children), false =>
            some { enclosing := position.enclosing, cursor := Cursor.forest children }
          | Cursor.tree (RuleTree.existsE binder body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.forallE binder body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.initializerE site body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.initializerE site], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.executionE binder body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.executionE binder], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.sharedE binder body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.publishGroup bindings body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.atPublication binding body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
            some
              { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.choice site left right), false =>
            some { enclosing := position.enclosing, cursor := Cursor.tree left }
          | Cursor.tree (RuleTree.choice site left right), true =>
            some { enclosing := position.enclosing, cursor := Cursor.tree right }
          | Cursor.forest (RuleForest.cons head tail), false =>
            some { enclosing := position.enclosing, cursor := Cursor.tree head }
          | Cursor.forest (RuleForest.cons head tail), true =>
            some { enclosing := position.enclosing, cursor := Cursor.forest tail }
          | x, x_1 => none).bind
        fun position =>
        (match position.cursor, false with
            | Cursor.tree (RuleTree.rule rule site context premises children), false =>
              some { enclosing := position.enclosing, cursor := Cursor.forest children }
            | Cursor.tree (RuleTree.existsE binder body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.forallE binder body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.initializerE site body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.initializerE site], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.executionE binder body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.executionE binder], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.sharedE binder body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.publishGroup bindings body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.atPublication binding body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
              some
                { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                  cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.choice site left right), false =>
              some { enclosing := position.enclosing, cursor := Cursor.tree left }
            | Cursor.tree (RuleTree.choice site left right), true =>
              some { enclosing := position.enclosing, cursor := Cursor.tree right }
            | Cursor.forest (RuleForest.cons head tail), false =>
              some { enclosing := position.enclosing, cursor := Cursor.tree head }
            | Cursor.forest (RuleForest.cons head tail), true =>
              some { enclosing := position.enclosing, cursor := Cursor.forest tail }
            | x, x_1 => none).bind
          fun position =>
          (match position.cursor, false with
              | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                some { enclosing := position.enclosing, cursor := Cursor.forest children }
              | Cursor.tree (RuleTree.existsE binder body), false =>
                some { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.forallE binder body), false =>
                some { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.initializerE site body), false =>
                some { enclosing := position.enclosing ++ [ScopeFrame.initializerE site], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.executionE binder body), false =>
                some { enclosing := position.enclosing ++ [ScopeFrame.executionE binder], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.sharedE binder body), false =>
                some { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                some
                  { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.atPublication binding body), false =>
                some
                  { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                some
                  { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                    cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.choice site left right), false =>
                some { enclosing := position.enclosing, cursor := Cursor.tree left }
              | Cursor.tree (RuleTree.choice site left right), true =>
                some { enclosing := position.enclosing, cursor := Cursor.tree right }
              | Cursor.forest (RuleForest.cons head tail), false =>
                some { enclosing := position.enclosing, cursor := Cursor.tree head }
              | Cursor.forest (RuleForest.cons head tail), true =>
                some { enclosing := position.enclosing, cursor := Cursor.forest tail }
              | x, x_1 => none).bind
            fun position =>
            (match position.cursor, false with
                | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                  some { enclosing := position.enclosing, cursor := Cursor.forest children }
                | Cursor.tree (RuleTree.existsE binder body), false =>
                  some { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.forallE binder body), false =>
                  some { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.initializerE site body), false =>
                  some { enclosing := position.enclosing ++ [ScopeFrame.initializerE site], cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.executionE binder body), false =>
                  some { enclosing := position.enclosing ++ [ScopeFrame.executionE binder], cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.sharedE binder body), false =>
                  some { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                  some
                    { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                      cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.atPublication binding body), false =>
                  some
                    { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                      cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                  some
                    { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                      cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.choice site left right), false =>
                  some { enclosing := position.enclosing, cursor := Cursor.tree left }
                | Cursor.tree (RuleTree.choice site left right), true =>
                  some { enclosing := position.enclosing, cursor := Cursor.tree right }
                | Cursor.forest (RuleForest.cons head tail), false =>
                  some { enclosing := position.enclosing, cursor := Cursor.tree head }
                | Cursor.forest (RuleForest.cons head tail), true =>
                  some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                | x, x_1 => none).bind
              fun position =>
              (match position.cursor, false with
                  | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                    some { enclosing := position.enclosing, cursor := Cursor.forest children }
                  | Cursor.tree (RuleTree.existsE binder body), false =>
                    some { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.forallE binder body), false =>
                    some { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.initializerE site body), false =>
                    some
                      { enclosing := position.enclosing ++ [ScopeFrame.initializerE site], cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.executionE binder body), false =>
                    some
                      { enclosing := position.enclosing ++ [ScopeFrame.executionE binder], cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.sharedE binder body), false =>
                    some { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                    some
                      { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                        cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.atPublication binding body), false =>
                    some
                      { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                        cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                    some
                      { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                        cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.choice site left right), false =>
                    some { enclosing := position.enclosing, cursor := Cursor.tree left }
                  | Cursor.tree (RuleTree.choice site left right), true =>
                    some { enclosing := position.enclosing, cursor := Cursor.tree right }
                  | Cursor.forest (RuleForest.cons head tail), false =>
                    some { enclosing := position.enclosing, cursor := Cursor.tree head }
                  | Cursor.forest (RuleForest.cons head tail), true =>
                    some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                  | x, x_1 => none).bind
                fun position =>
                (match position.cursor, false with
                    | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                      some { enclosing := position.enclosing, cursor := Cursor.forest children }
                    | Cursor.tree (RuleTree.existsE binder body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.forallE binder body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.initializerE site body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                          cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.executionE binder body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                          cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.sharedE binder body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                          cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.atPublication binding body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                          cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                          cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.choice site left right), false =>
                      some { enclosing := position.enclosing, cursor := Cursor.tree left }
                    | Cursor.tree (RuleTree.choice site left right), true =>
                      some { enclosing := position.enclosing, cursor := Cursor.tree right }
                    | Cursor.forest (RuleForest.cons head tail), false =>
                      some { enclosing := position.enclosing, cursor := Cursor.tree head }
                    | Cursor.forest (RuleForest.cons head tail), true =>
                      some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                    | x, x_1 => none).bind
                  fun position =>
                  (match position.cursor, false with
                      | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                        some { enclosing := position.enclosing, cursor := Cursor.forest children }
                      | Cursor.tree (RuleTree.existsE binder body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.forallE binder body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.initializerE site body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                            cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.executionE binder body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                            cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.sharedE binder body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                            cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.atPublication binding body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                            cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                            cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.choice site left right), false =>
                        some { enclosing := position.enclosing, cursor := Cursor.tree left }
                      | Cursor.tree (RuleTree.choice site left right), true =>
                        some { enclosing := position.enclosing, cursor := Cursor.tree right }
                      | Cursor.forest (RuleForest.cons head tail), false =>
                        some { enclosing := position.enclosing, cursor := Cursor.tree head }
                      | Cursor.forest (RuleForest.cons head tail), true =>
                        some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                      | x, x_1 => none).bind
                    fun position =>
                    (match position.cursor, false with
                        | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                          some { enclosing := position.enclosing, cursor := Cursor.forest children }
                        | Cursor.tree (RuleTree.existsE binder body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.existsE binder],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.forallE binder body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.forallE binder],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.initializerE site body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.executionE binder body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.sharedE binder body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.atPublication binding body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.choice site left right), false =>
                          some { enclosing := position.enclosing, cursor := Cursor.tree left }
                        | Cursor.tree (RuleTree.choice site left right), true =>
                          some { enclosing := position.enclosing, cursor := Cursor.tree right }
                        | Cursor.forest (RuleForest.cons head tail), false =>
                          some { enclosing := position.enclosing, cursor := Cursor.tree head }
                        | Cursor.forest (RuleForest.cons head tail), true =>
                          some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                        | x, x_1 => none).bind
                      fun position =>
                      (match position.cursor, false with
                          | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                            some { enclosing := position.enclosing, cursor := Cursor.forest children }
                          | Cursor.tree (RuleTree.existsE binder body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.existsE binder],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.forallE binder body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.forallE binder],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.initializerE site body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.executionE binder body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.sharedE binder body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.atPublication binding body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.choice site left right), false =>
                            some { enclosing := position.enclosing, cursor := Cursor.tree left }
                          | Cursor.tree (RuleTree.choice site left right), true =>
                            some { enclosing := position.enclosing, cursor := Cursor.tree right }
                          | Cursor.forest (RuleForest.cons head tail), false =>
                            some { enclosing := position.enclosing, cursor := Cursor.tree head }
                          | Cursor.forest (RuleForest.cons head tail), true =>
                            some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                          | x, x_1 => none).bind
                        fun position =>
                        (match position.cursor, true with
                            | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                              some { enclosing := position.enclosing, cursor := Cursor.forest children }
                            | Cursor.tree (RuleTree.existsE binder body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.existsE binder],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.forallE binder body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.forallE binder],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.initializerE site body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.executionE binder body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.sharedE binder body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.atPublication binding body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.choice site left right), false =>
                              some { enclosing := position.enclosing, cursor := Cursor.tree left }
                            | Cursor.tree (RuleTree.choice site left right), true =>
                              some { enclosing := position.enclosing, cursor := Cursor.tree right }
                            | Cursor.forest (RuleForest.cons head tail), false =>
                              some { enclosing := position.enclosing, cursor := Cursor.tree head }
                            | Cursor.forest (RuleForest.cons head tail), true =>
                              some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                            | x, x_1 => none).bind
                          fun position =>
                          (match position.cursor, false with
                              | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                                some { enclosing := position.enclosing, cursor := Cursor.forest children }
                              | Cursor.tree (RuleTree.existsE binder body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.existsE binder],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.forallE binder body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.forallE binder],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.initializerE site body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.executionE binder body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.sharedE binder body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.atPublication binding body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.choice site left right), false =>
                                some { enclosing := position.enclosing, cursor := Cursor.tree left }
                              | Cursor.tree (RuleTree.choice site left right), true =>
                                some { enclosing := position.enclosing, cursor := Cursor.tree right }
                              | Cursor.forest (RuleForest.cons head tail), false =>
                                some { enclosing := position.enclosing, cursor := Cursor.tree head }
                              | Cursor.forest (RuleForest.cons head tail), true =>
                                some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                              | x, x_1 => none).bind
                            fun position =>
                            match position.cursor with
                            | Cursor.tree (RuleTree.existsE binder body) =>
                              if
                                  (match binder.kind with
                                    | BinderKind.viewLogic => true
                                    | BinderKind.eventProof => true
                                    | BinderKind.publishedInstance => true
                                    | x => false) =
                                    true then
                                some { binder := binder, enclosing := position.enclosing, subtree := body }
                              else none
                            | x => none) =
    some
      { binder := { site := body.site, kind := BinderKind.eventProof },
        enclosing :=
          scope ++
            ([ScopeFrame.existsE { site := formalSite, kind := BinderKind.description },
                ScopeFrame.existsE { site := site, kind := BinderKind.viewLogic },
                ScopeFrame.forallE { site := site, kind := BinderKind.invocation },
                ScopeFrame.existsE { site := formalSite, kind := BinderKind.receipt }] ++
              ([] ++ [ScopeFrame.sharedE { site := formalSite, kind := BinderKind.shared }])),
        subtree :=
          RuleTree.rule Rule.sequence body.site
            (List.filter
                (fun binding =>
                  !(formalName == binding.name || List.any context fun prior => prior.name == binding.name))
                pattern.bindingRecords ++
              { name := formalName, owner := formalSite, kind := BindingKind.formal, annotation := formalAnnotation,
                  entry := some Entry.computation, singleUse := Source.nameCount formalName body == 1 } ::
                context)
            (List.map
                (fun kind =>
                  Premise.atom
                    (atom kind body.site
                      (List.filter
                          (fun binding =>
                            !(formalName == binding.name || List.any context fun prior => prior.name == binding.name))
                          pattern.bindingRecords ++
                        { name := formalName, owner := formalSite, kind := BindingKind.formal,
                            annotation := formalAnnotation, entry := some Entry.computation,
                            singleUse := Source.nameCount formalName body == 1 } ::
                          context)
                      [site, formalSite]))
                [AtomKind.completeBodyConsumer, AtomKind.actualReturnOrPendingSuffix] ++
              [Premise.checking
                  { mode := CheckMode.computation, site := body.site,
                    context :=
                      List.filter
                          (fun binding =>
                            !(formalName == binding.name || List.any context fun prior => prior.name == binding.name))
                          pattern.bindingRecords ++
                        { name := formalName, owner := formalSite, kind := BindingKind.formal,
                            annotation := formalAnnotation, entry := some Entry.computation,
                            singleUse := Source.nameCount formalName body == 1 } ::
                          context,
                    lower := { site := body.site, port := Port.finalRoot },
                    upper := { site := site, port := Port.bodyConsumer } }])
            (RuleForest.cons
              (sourceRules
                (List.filter
                    (fun binding =>
                      !(formalName == binding.name || List.any context fun prior => prior.name == binding.name))
                    pattern.bindingRecords ++
                  { name := formalName, owner := formalSite, kind := BindingKind.formal, annotation := formalAnnotation,
                      entry := some Entry.computation, singleUse := Source.nameCount formalName body == 1 } ::
                    context)
                body)
              RuleForest.nil) }

case some.false
context : Context
pattern : Source Category.pattern
body : Source Category.expression
scope : List ScopeFrame
site formalSite : Site
formalName : Name
formalAnnotation : Option Annotation
val✝ : Annotation
⊢ ((match
          Cursor.tree
            (annotated { site := site, annotation := some val✝ } context
              (RuleTree.existsE { site := formalSite, kind := BinderKind.description }
                (RuleTree.existsE { site := site, kind := BinderKind.viewLogic }
                  (node Rule.lambda site context [AtomKind.captureWholeEnvironment, AtomKind.closureFormation]
                    [formalSite, pattern.site, body.site]
                    (RuleForest.cons
                      (RuleTree.forallE { site := site, kind := BinderKind.invocation }
                        (RuleTree.existsE { site := formalSite, kind := BinderKind.receipt }
                          (RuleTree.rule Rule.parameterEntry formalSite
                            ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                annotation := formalAnnotation, entry := some Entry.value,
                                singleUse := Source.nameCount formalName body == 1 } ::
                              context)
                            (Premise.atom
                                {
                                  kind :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).kind,
                                  site :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).site,
                                  context :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).context,
                                  operands :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).operands,
                                  order :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).order,
                                  names :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).names,
                                  declaration :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).declaration,
                                  annotation := formalAnnotation,
                                  annotations :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).annotations,
                                  labels :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).labels,
                                  flag :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).flag,
                                  arity :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).arity,
                                  merges :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).merges,
                                  literal :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).literal,
                                  entry := some Entry.value,
                                  binding :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).binding } ::
                              premises [AtomKind.receiptFormation, AtomKind.entryForceReturnRebind] formalSite
                                ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                    annotation := formalAnnotation, entry := some Entry.value,
                                    singleUse := Source.nameCount formalName body == 1 } ::
                                  context)
                                [site, pattern.site, body.site])
                            (RuleForest.cons
                              (suffix formalSite
                                (RuleTree.sharedE { site := formalSite, kind := BinderKind.shared }
                                  (RuleTree.rule Rule.sequence formalSite
                                    ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                        annotation := formalAnnotation, entry := some Entry.value,
                                        singleUse := Source.nameCount formalName body == 1 } ::
                                      context)
                                    []
                                    (RuleForest.cons
                                      (sourceRules
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.value,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)
                                        pattern)
                                      (RuleForest.cons
                                        (RuleTree.existsE { site := body.site, kind := BinderKind.eventProof }
                                          (RuleTree.rule Rule.sequence body.site
                                            (patternContext
                                              ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                                  annotation := formalAnnotation, entry := some Entry.value,
                                                  singleUse := Source.nameCount formalName body == 1 } ::
                                                context)
                                              pattern)
                                            (premises
                                                [AtomKind.completeBodyConsumer, AtomKind.actualReturnOrPendingSuffix]
                                                body.site
                                                (patternContext
                                                  ({ name := formalName, owner := formalSite,
                                                      kind := BindingKind.formal, annotation := formalAnnotation,
                                                      entry := some Entry.value,
                                                      singleUse := Source.nameCount formalName body == 1 } ::
                                                    context)
                                                  pattern)
                                                [site, formalSite] ++
                                              [check CheckMode.computation body.site
                                                  (patternContext
                                                    ({ name := formalName, owner := formalSite,
                                                        kind := BindingKind.formal, annotation := formalAnnotation,
                                                        entry := some Entry.value,
                                                        singleUse := Source.nameCount formalName body == 1 } ::
                                                      context)
                                                    pattern)
                                                  (endpoint body.site) (endpoint site Port.bodyConsumer)])
                                            (RuleForest.cons
                                              (sourceRules
                                                (patternContext
                                                  ({ name := formalName, owner := formalSite,
                                                      kind := BindingKind.formal, annotation := formalAnnotation,
                                                      entry := some Entry.value,
                                                      singleUse := Source.nameCount formalName body == 1 } ::
                                                    context)
                                                  pattern)
                                                body)
                                              RuleForest.nil)))
                                        RuleForest.nil)))))
                              RuleForest.nil))))
                      RuleForest.nil))))),
          false with
        | Cursor.tree (RuleTree.rule rule site context premises children), false =>
          some { enclosing := scope, cursor := Cursor.forest children }
        | Cursor.tree (RuleTree.existsE binder body), false =>
          some { enclosing := scope ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.forallE binder body), false =>
          some { enclosing := scope ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.initializerE site body), false =>
          some { enclosing := scope ++ [ScopeFrame.initializerE site], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.executionE binder body), false =>
          some { enclosing := scope ++ [ScopeFrame.executionE binder], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.sharedE binder body), false =>
          some { enclosing := scope ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.publishGroup bindings body), false =>
          some { enclosing := scope ++ [ScopeFrame.publishGroup bindings], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.atPublication binding body), false =>
          some { enclosing := scope ++ [ScopeFrame.atPublication binding], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
          some { enclosing := scope ++ [ScopeFrame.aliasPublication original aliasName], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.choice site left right), false =>
          some { enclosing := scope, cursor := Cursor.tree left }
        | Cursor.tree (RuleTree.choice site left right), true =>
          some { enclosing := scope, cursor := Cursor.tree right }
        | Cursor.forest (RuleForest.cons head tail), false => some { enclosing := scope, cursor := Cursor.tree head }
        | Cursor.forest (RuleForest.cons head tail), true => some { enclosing := scope, cursor := Cursor.forest tail }
        | x, x_1 => none).bind
      fun position =>
      (match position.cursor, false with
          | Cursor.tree (RuleTree.rule rule site context premises children), false =>
            some { enclosing := position.enclosing, cursor := Cursor.forest children }
          | Cursor.tree (RuleTree.existsE binder body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.forallE binder body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.initializerE site body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.initializerE site], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.executionE binder body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.executionE binder], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.sharedE binder body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.publishGroup bindings body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.atPublication binding body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
            some
              { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.choice site left right), false =>
            some { enclosing := position.enclosing, cursor := Cursor.tree left }
          | Cursor.tree (RuleTree.choice site left right), true =>
            some { enclosing := position.enclosing, cursor := Cursor.tree right }
          | Cursor.forest (RuleForest.cons head tail), false =>
            some { enclosing := position.enclosing, cursor := Cursor.tree head }
          | Cursor.forest (RuleForest.cons head tail), true =>
            some { enclosing := position.enclosing, cursor := Cursor.forest tail }
          | x, x_1 => none).bind
        fun position =>
        (match position.cursor, false with
            | Cursor.tree (RuleTree.rule rule site context premises children), false =>
              some { enclosing := position.enclosing, cursor := Cursor.forest children }
            | Cursor.tree (RuleTree.existsE binder body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.forallE binder body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.initializerE site body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.initializerE site], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.executionE binder body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.executionE binder], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.sharedE binder body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.publishGroup bindings body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.atPublication binding body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
              some
                { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                  cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.choice site left right), false =>
              some { enclosing := position.enclosing, cursor := Cursor.tree left }
            | Cursor.tree (RuleTree.choice site left right), true =>
              some { enclosing := position.enclosing, cursor := Cursor.tree right }
            | Cursor.forest (RuleForest.cons head tail), false =>
              some { enclosing := position.enclosing, cursor := Cursor.tree head }
            | Cursor.forest (RuleForest.cons head tail), true =>
              some { enclosing := position.enclosing, cursor := Cursor.forest tail }
            | x, x_1 => none).bind
          fun position =>
          (match position.cursor, false with
              | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                some { enclosing := position.enclosing, cursor := Cursor.forest children }
              | Cursor.tree (RuleTree.existsE binder body), false =>
                some { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.forallE binder body), false =>
                some { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.initializerE site body), false =>
                some { enclosing := position.enclosing ++ [ScopeFrame.initializerE site], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.executionE binder body), false =>
                some { enclosing := position.enclosing ++ [ScopeFrame.executionE binder], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.sharedE binder body), false =>
                some { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                some
                  { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.atPublication binding body), false =>
                some
                  { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                some
                  { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                    cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.choice site left right), false =>
                some { enclosing := position.enclosing, cursor := Cursor.tree left }
              | Cursor.tree (RuleTree.choice site left right), true =>
                some { enclosing := position.enclosing, cursor := Cursor.tree right }
              | Cursor.forest (RuleForest.cons head tail), false =>
                some { enclosing := position.enclosing, cursor := Cursor.tree head }
              | Cursor.forest (RuleForest.cons head tail), true =>
                some { enclosing := position.enclosing, cursor := Cursor.forest tail }
              | x, x_1 => none).bind
            fun position =>
            (match position.cursor, false with
                | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                  some { enclosing := position.enclosing, cursor := Cursor.forest children }
                | Cursor.tree (RuleTree.existsE binder body), false =>
                  some { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.forallE binder body), false =>
                  some { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.initializerE site body), false =>
                  some { enclosing := position.enclosing ++ [ScopeFrame.initializerE site], cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.executionE binder body), false =>
                  some { enclosing := position.enclosing ++ [ScopeFrame.executionE binder], cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.sharedE binder body), false =>
                  some { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                  some
                    { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                      cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.atPublication binding body), false =>
                  some
                    { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                      cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                  some
                    { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                      cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.choice site left right), false =>
                  some { enclosing := position.enclosing, cursor := Cursor.tree left }
                | Cursor.tree (RuleTree.choice site left right), true =>
                  some { enclosing := position.enclosing, cursor := Cursor.tree right }
                | Cursor.forest (RuleForest.cons head tail), false =>
                  some { enclosing := position.enclosing, cursor := Cursor.tree head }
                | Cursor.forest (RuleForest.cons head tail), true =>
                  some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                | x, x_1 => none).bind
              fun position =>
              (match position.cursor, false with
                  | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                    some { enclosing := position.enclosing, cursor := Cursor.forest children }
                  | Cursor.tree (RuleTree.existsE binder body), false =>
                    some { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.forallE binder body), false =>
                    some { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.initializerE site body), false =>
                    some
                      { enclosing := position.enclosing ++ [ScopeFrame.initializerE site], cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.executionE binder body), false =>
                    some
                      { enclosing := position.enclosing ++ [ScopeFrame.executionE binder], cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.sharedE binder body), false =>
                    some { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                    some
                      { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                        cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.atPublication binding body), false =>
                    some
                      { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                        cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                    some
                      { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                        cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.choice site left right), false =>
                    some { enclosing := position.enclosing, cursor := Cursor.tree left }
                  | Cursor.tree (RuleTree.choice site left right), true =>
                    some { enclosing := position.enclosing, cursor := Cursor.tree right }
                  | Cursor.forest (RuleForest.cons head tail), false =>
                    some { enclosing := position.enclosing, cursor := Cursor.tree head }
                  | Cursor.forest (RuleForest.cons head tail), true =>
                    some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                  | x, x_1 => none).bind
                fun position =>
                (match position.cursor, false with
                    | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                      some { enclosing := position.enclosing, cursor := Cursor.forest children }
                    | Cursor.tree (RuleTree.existsE binder body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.forallE binder body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.initializerE site body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                          cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.executionE binder body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                          cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.sharedE binder body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                          cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.atPublication binding body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                          cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                          cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.choice site left right), false =>
                      some { enclosing := position.enclosing, cursor := Cursor.tree left }
                    | Cursor.tree (RuleTree.choice site left right), true =>
                      some { enclosing := position.enclosing, cursor := Cursor.tree right }
                    | Cursor.forest (RuleForest.cons head tail), false =>
                      some { enclosing := position.enclosing, cursor := Cursor.tree head }
                    | Cursor.forest (RuleForest.cons head tail), true =>
                      some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                    | x, x_1 => none).bind
                  fun position =>
                  (match position.cursor, false with
                      | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                        some { enclosing := position.enclosing, cursor := Cursor.forest children }
                      | Cursor.tree (RuleTree.existsE binder body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.forallE binder body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.initializerE site body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                            cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.executionE binder body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                            cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.sharedE binder body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                            cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.atPublication binding body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                            cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                            cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.choice site left right), false =>
                        some { enclosing := position.enclosing, cursor := Cursor.tree left }
                      | Cursor.tree (RuleTree.choice site left right), true =>
                        some { enclosing := position.enclosing, cursor := Cursor.tree right }
                      | Cursor.forest (RuleForest.cons head tail), false =>
                        some { enclosing := position.enclosing, cursor := Cursor.tree head }
                      | Cursor.forest (RuleForest.cons head tail), true =>
                        some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                      | x, x_1 => none).bind
                    fun position =>
                    (match position.cursor, false with
                        | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                          some { enclosing := position.enclosing, cursor := Cursor.forest children }
                        | Cursor.tree (RuleTree.existsE binder body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.existsE binder],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.forallE binder body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.forallE binder],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.initializerE site body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.executionE binder body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.sharedE binder body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.atPublication binding body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.choice site left right), false =>
                          some { enclosing := position.enclosing, cursor := Cursor.tree left }
                        | Cursor.tree (RuleTree.choice site left right), true =>
                          some { enclosing := position.enclosing, cursor := Cursor.tree right }
                        | Cursor.forest (RuleForest.cons head tail), false =>
                          some { enclosing := position.enclosing, cursor := Cursor.tree head }
                        | Cursor.forest (RuleForest.cons head tail), true =>
                          some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                        | x, x_1 => none).bind
                      fun position =>
                      (match position.cursor, false with
                          | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                            some { enclosing := position.enclosing, cursor := Cursor.forest children }
                          | Cursor.tree (RuleTree.existsE binder body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.existsE binder],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.forallE binder body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.forallE binder],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.initializerE site body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.executionE binder body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.sharedE binder body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.atPublication binding body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.choice site left right), false =>
                            some { enclosing := position.enclosing, cursor := Cursor.tree left }
                          | Cursor.tree (RuleTree.choice site left right), true =>
                            some { enclosing := position.enclosing, cursor := Cursor.tree right }
                          | Cursor.forest (RuleForest.cons head tail), false =>
                            some { enclosing := position.enclosing, cursor := Cursor.tree head }
                          | Cursor.forest (RuleForest.cons head tail), true =>
                            some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                          | x, x_1 => none).bind
                        fun position =>
                        (match position.cursor, false with
                            | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                              some { enclosing := position.enclosing, cursor := Cursor.forest children }
                            | Cursor.tree (RuleTree.existsE binder body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.existsE binder],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.forallE binder body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.forallE binder],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.initializerE site body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.executionE binder body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.sharedE binder body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.atPublication binding body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.choice site left right), false =>
                              some { enclosing := position.enclosing, cursor := Cursor.tree left }
                            | Cursor.tree (RuleTree.choice site left right), true =>
                              some { enclosing := position.enclosing, cursor := Cursor.tree right }
                            | Cursor.forest (RuleForest.cons head tail), false =>
                              some { enclosing := position.enclosing, cursor := Cursor.tree head }
                            | Cursor.forest (RuleForest.cons head tail), true =>
                              some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                            | x, x_1 => none).bind
                          fun position =>
                          (match position.cursor, false with
                              | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                                some { enclosing := position.enclosing, cursor := Cursor.forest children }
                              | Cursor.tree (RuleTree.existsE binder body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.existsE binder],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.forallE binder body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.forallE binder],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.initializerE site body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.executionE binder body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.sharedE binder body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.atPublication binding body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.choice site left right), false =>
                                some { enclosing := position.enclosing, cursor := Cursor.tree left }
                              | Cursor.tree (RuleTree.choice site left right), true =>
                                some { enclosing := position.enclosing, cursor := Cursor.tree right }
                              | Cursor.forest (RuleForest.cons head tail), false =>
                                some { enclosing := position.enclosing, cursor := Cursor.tree head }
                              | Cursor.forest (RuleForest.cons head tail), true =>
                                some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                              | x, x_1 => none).bind
                            fun position =>
                            (match position.cursor, false with
                                | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                                  some { enclosing := position.enclosing, cursor := Cursor.forest children }
                                | Cursor.tree (RuleTree.existsE binder body), false =>
                                  some
                                    { enclosing := position.enclosing ++ [ScopeFrame.existsE binder],
                                      cursor := Cursor.tree body }
                                | Cursor.tree (RuleTree.forallE binder body), false =>
                                  some
                                    { enclosing := position.enclosing ++ [ScopeFrame.forallE binder],
                                      cursor := Cursor.tree body }
                                | Cursor.tree (RuleTree.initializerE site body), false =>
                                  some
                                    { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                                      cursor := Cursor.tree body }
                                | Cursor.tree (RuleTree.executionE binder body), false =>
                                  some
                                    { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                                      cursor := Cursor.tree body }
                                | Cursor.tree (RuleTree.sharedE binder body), false =>
                                  some
                                    { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder],
                                      cursor := Cursor.tree body }
                                | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                                  some
                                    { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                                      cursor := Cursor.tree body }
                                | Cursor.tree (RuleTree.atPublication binding body), false =>
                                  some
                                    { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                                      cursor := Cursor.tree body }
                                | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                                  some
                                    {
                                      enclosing :=
                                        position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                                      cursor := Cursor.tree body }
                                | Cursor.tree (RuleTree.choice site left right), false =>
                                  some { enclosing := position.enclosing, cursor := Cursor.tree left }
                                | Cursor.tree (RuleTree.choice site left right), true =>
                                  some { enclosing := position.enclosing, cursor := Cursor.tree right }
                                | Cursor.forest (RuleForest.cons head tail), false =>
                                  some { enclosing := position.enclosing, cursor := Cursor.tree head }
                                | Cursor.forest (RuleForest.cons head tail), true =>
                                  some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                                | x, x_1 => none).bind
                              fun position =>
                              (match position.cursor, true with
                                  | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                                    some { enclosing := position.enclosing, cursor := Cursor.forest children }
                                  | Cursor.tree (RuleTree.existsE binder body), false =>
                                    some
                                      { enclosing := position.enclosing ++ [ScopeFrame.existsE binder],
                                        cursor := Cursor.tree body }
                                  | Cursor.tree (RuleTree.forallE binder body), false =>
                                    some
                                      { enclosing := position.enclosing ++ [ScopeFrame.forallE binder],
                                        cursor := Cursor.tree body }
                                  | Cursor.tree (RuleTree.initializerE site body), false =>
                                    some
                                      { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                                        cursor := Cursor.tree body }
                                  | Cursor.tree (RuleTree.executionE binder body), false =>
                                    some
                                      { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                                        cursor := Cursor.tree body }
                                  | Cursor.tree (RuleTree.sharedE binder body), false =>
                                    some
                                      { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder],
                                        cursor := Cursor.tree body }
                                  | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                                    some
                                      { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                                        cursor := Cursor.tree body }
                                  | Cursor.tree (RuleTree.atPublication binding body), false =>
                                    some
                                      { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                                        cursor := Cursor.tree body }
                                  | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                                    some
                                      {
                                        enclosing :=
                                          position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                                        cursor := Cursor.tree body }
                                  | Cursor.tree (RuleTree.choice site left right), false =>
                                    some { enclosing := position.enclosing, cursor := Cursor.tree left }
                                  | Cursor.tree (RuleTree.choice site left right), true =>
                                    some { enclosing := position.enclosing, cursor := Cursor.tree right }
                                  | Cursor.forest (RuleForest.cons head tail), false =>
                                    some { enclosing := position.enclosing, cursor := Cursor.tree head }
                                  | Cursor.forest (RuleForest.cons head tail), true =>
                                    some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                                  | x, x_1 => none).bind
                                fun position =>
                                (match position.cursor, false with
                                    | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                                      some { enclosing := position.enclosing, cursor := Cursor.forest children }
                                    | Cursor.tree (RuleTree.existsE binder body), false =>
                                      some
                                        { enclosing := position.enclosing ++ [ScopeFrame.existsE binder],
                                          cursor := Cursor.tree body }
                                    | Cursor.tree (RuleTree.forallE binder body), false =>
                                      some
                                        { enclosing := position.enclosing ++ [ScopeFrame.forallE binder],
                                          cursor := Cursor.tree body }
                                    | Cursor.tree (RuleTree.initializerE site body), false =>
                                      some
                                        { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                                          cursor := Cursor.tree body }
                                    | Cursor.tree (RuleTree.executionE binder body), false =>
                                      some
                                        { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                                          cursor := Cursor.tree body }
                                    | Cursor.tree (RuleTree.sharedE binder body), false =>
                                      some
                                        { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder],
                                          cursor := Cursor.tree body }
                                    | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                                      some
                                        { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                                          cursor := Cursor.tree body }
                                    | Cursor.tree (RuleTree.atPublication binding body), false =>
                                      some
                                        { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                                          cursor := Cursor.tree body }
                                    | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                                      some
                                        {
                                          enclosing :=
                                            position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                                          cursor := Cursor.tree body }
                                    | Cursor.tree (RuleTree.choice site left right), false =>
                                      some { enclosing := position.enclosing, cursor := Cursor.tree left }
                                    | Cursor.tree (RuleTree.choice site left right), true =>
                                      some { enclosing := position.enclosing, cursor := Cursor.tree right }
                                    | Cursor.forest (RuleForest.cons head tail), false =>
                                      some { enclosing := position.enclosing, cursor := Cursor.tree head }
                                    | Cursor.forest (RuleForest.cons head tail), true =>
                                      some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                                    | x, x_1 => none).bind
                                  fun position =>
                                  match position.cursor with
                                  | Cursor.tree (RuleTree.existsE binder body) =>
                                    if
                                        (match binder.kind with
                                          | BinderKind.viewLogic => true
                                          | BinderKind.eventProof => true
                                          | BinderKind.publishedInstance => true
                                          | x => false) =
                                          true then
                                      some { binder := binder, enclosing := position.enclosing, subtree := body }
                                    else none
                                  | x => none) =
    some
      { binder := { site := body.site, kind := BinderKind.eventProof },
        enclosing :=
          scope ++
            ([ScopeFrame.existsE { site := formalSite, kind := BinderKind.description },
                ScopeFrame.existsE { site := site, kind := BinderKind.viewLogic },
                ScopeFrame.forallE { site := site, kind := BinderKind.invocation },
                ScopeFrame.existsE { site := formalSite, kind := BinderKind.receipt }] ++
              ([ScopeFrame.executionE { site := formalSite, kind := BinderKind.returnRebind }] ++
                [ScopeFrame.sharedE { site := formalSite, kind := BinderKind.shared }])),
        subtree :=
          RuleTree.rule Rule.sequence body.site
            (List.filter
                (fun binding =>
                  !(formalName == binding.name || List.any context fun prior => prior.name == binding.name))
                pattern.bindingRecords ++
              { name := formalName, owner := formalSite, kind := BindingKind.formal, annotation := formalAnnotation,
                  entry := some Entry.value, singleUse := Source.nameCount formalName body == 1 } ::
                context)
            (List.map
                (fun kind =>
                  Premise.atom
                    (atom kind body.site
                      (List.filter
                          (fun binding =>
                            !(formalName == binding.name || List.any context fun prior => prior.name == binding.name))
                          pattern.bindingRecords ++
                        { name := formalName, owner := formalSite, kind := BindingKind.formal,
                            annotation := formalAnnotation, entry := some Entry.value,
                            singleUse := Source.nameCount formalName body == 1 } ::
                          context)
                      [site, formalSite]))
                [AtomKind.completeBodyConsumer, AtomKind.actualReturnOrPendingSuffix] ++
              [Premise.checking
                  { mode := CheckMode.computation, site := body.site,
                    context :=
                      List.filter
                          (fun binding =>
                            !(formalName == binding.name || List.any context fun prior => prior.name == binding.name))
                          pattern.bindingRecords ++
                        { name := formalName, owner := formalSite, kind := BindingKind.formal,
                            annotation := formalAnnotation, entry := some Entry.value,
                            singleUse := Source.nameCount formalName body == 1 } ::
                          context,
                    lower := { site := body.site, port := Port.finalRoot },
                    upper := { site := site, port := Port.bodyConsumer } }])
            (RuleForest.cons
              (sourceRules
                (List.filter
                    (fun binding =>
                      !(formalName == binding.name || List.any context fun prior => prior.name == binding.name))
                    pattern.bindingRecords ++
                  { name := formalName, owner := formalSite, kind := BindingKind.formal, annotation := formalAnnotation,
                      entry := some Entry.value, singleUse := Source.nameCount formalName body == 1 } ::
                    context)
                body)
              RuleForest.nil) }

case some.true
context : Context
pattern : Source Category.pattern
body : Source Category.expression
scope : List ScopeFrame
site formalSite : Site
formalName : Name
formalAnnotation : Option Annotation
val✝ : Annotation
⊢ ((match
          Cursor.tree
            (annotated { site := site, annotation := some val✝ } context
              (RuleTree.existsE { site := formalSite, kind := BinderKind.description }
                (RuleTree.existsE { site := site, kind := BinderKind.viewLogic }
                  (node Rule.lambda site context [AtomKind.captureWholeEnvironment, AtomKind.closureFormation]
                    [formalSite, pattern.site, body.site]
                    (RuleForest.cons
                      (RuleTree.forallE { site := site, kind := BinderKind.invocation }
                        (RuleTree.existsE { site := formalSite, kind := BinderKind.receipt }
                          (RuleTree.rule Rule.parameterEntry formalSite
                            ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                annotation := formalAnnotation, entry := some Entry.computation,
                                singleUse := Source.nameCount formalName body == 1 } ::
                              context)
                            (Premise.atom
                                {
                                  kind :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).kind,
                                  site :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).site,
                                  context :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).context,
                                  operands :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).operands,
                                  order :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).order,
                                  names :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).names,
                                  declaration :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).declaration,
                                  annotation := formalAnnotation,
                                  annotations :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).annotations,
                                  labels :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).labels,
                                  flag :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).flag,
                                  arity :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).arity,
                                  merges :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).merges,
                                  literal :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).literal,
                                  entry := some Entry.computation,
                                  binding :=
                                    (atom AtomKind.sourceFormalRole formalSite
                                        ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                            annotation := formalAnnotation, entry := some Entry.computation,
                                            singleUse := Source.nameCount formalName body == 1 } ::
                                          context)).binding } ::
                              premises [AtomKind.receiptFormation, AtomKind.retainedEntry] formalSite
                                ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                    annotation := formalAnnotation, entry := some Entry.computation,
                                    singleUse := Source.nameCount formalName body == 1 } ::
                                  context)
                                [site, pattern.site, body.site])
                            (RuleForest.cons
                              (RuleTree.sharedE { site := formalSite, kind := BinderKind.shared }
                                (RuleTree.rule Rule.sequence formalSite
                                  ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                      annotation := formalAnnotation, entry := some Entry.computation,
                                      singleUse := Source.nameCount formalName body == 1 } ::
                                    context)
                                  []
                                  (RuleForest.cons
                                    (sourceRules
                                      ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                          annotation := formalAnnotation, entry := some Entry.computation,
                                          singleUse := Source.nameCount formalName body == 1 } ::
                                        context)
                                      pattern)
                                    (RuleForest.cons
                                      (RuleTree.existsE { site := body.site, kind := BinderKind.eventProof }
                                        (RuleTree.rule Rule.sequence body.site
                                          (patternContext
                                            ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                                annotation := formalAnnotation, entry := some Entry.computation,
                                                singleUse := Source.nameCount formalName body == 1 } ::
                                              context)
                                            pattern)
                                          (premises
                                              [AtomKind.completeBodyConsumer, AtomKind.actualReturnOrPendingSuffix]
                                              body.site
                                              (patternContext
                                                ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                                    annotation := formalAnnotation, entry := some Entry.computation,
                                                    singleUse := Source.nameCount formalName body == 1 } ::
                                                  context)
                                                pattern)
                                              [site, formalSite] ++
                                            [check CheckMode.computation body.site
                                                (patternContext
                                                  ({ name := formalName, owner := formalSite,
                                                      kind := BindingKind.formal, annotation := formalAnnotation,
                                                      entry := some Entry.computation,
                                                      singleUse := Source.nameCount formalName body == 1 } ::
                                                    context)
                                                  pattern)
                                                (endpoint body.site) (endpoint site Port.bodyConsumer)])
                                          (RuleForest.cons
                                            (sourceRules
                                              (patternContext
                                                ({ name := formalName, owner := formalSite, kind := BindingKind.formal,
                                                    annotation := formalAnnotation, entry := some Entry.computation,
                                                    singleUse := Source.nameCount formalName body == 1 } ::
                                                  context)
                                                pattern)
                                              body)
                                            RuleForest.nil)))
                                      RuleForest.nil))))
                              RuleForest.nil))))
                      RuleForest.nil))))),
          false with
        | Cursor.tree (RuleTree.rule rule site context premises children), false =>
          some { enclosing := scope, cursor := Cursor.forest children }
        | Cursor.tree (RuleTree.existsE binder body), false =>
          some { enclosing := scope ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.forallE binder body), false =>
          some { enclosing := scope ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.initializerE site body), false =>
          some { enclosing := scope ++ [ScopeFrame.initializerE site], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.executionE binder body), false =>
          some { enclosing := scope ++ [ScopeFrame.executionE binder], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.sharedE binder body), false =>
          some { enclosing := scope ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.publishGroup bindings body), false =>
          some { enclosing := scope ++ [ScopeFrame.publishGroup bindings], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.atPublication binding body), false =>
          some { enclosing := scope ++ [ScopeFrame.atPublication binding], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
          some { enclosing := scope ++ [ScopeFrame.aliasPublication original aliasName], cursor := Cursor.tree body }
        | Cursor.tree (RuleTree.choice site left right), false =>
          some { enclosing := scope, cursor := Cursor.tree left }
        | Cursor.tree (RuleTree.choice site left right), true =>
          some { enclosing := scope, cursor := Cursor.tree right }
        | Cursor.forest (RuleForest.cons head tail), false => some { enclosing := scope, cursor := Cursor.tree head }
        | Cursor.forest (RuleForest.cons head tail), true => some { enclosing := scope, cursor := Cursor.forest tail }
        | x, x_1 => none).bind
      fun position =>
      (match position.cursor, false with
          | Cursor.tree (RuleTree.rule rule site context premises children), false =>
            some { enclosing := position.enclosing, cursor := Cursor.forest children }
          | Cursor.tree (RuleTree.existsE binder body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.forallE binder body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.initializerE site body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.initializerE site], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.executionE binder body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.executionE binder], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.sharedE binder body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.publishGroup bindings body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.atPublication binding body), false =>
            some { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding], cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
            some
              { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                cursor := Cursor.tree body }
          | Cursor.tree (RuleTree.choice site left right), false =>
            some { enclosing := position.enclosing, cursor := Cursor.tree left }
          | Cursor.tree (RuleTree.choice site left right), true =>
            some { enclosing := position.enclosing, cursor := Cursor.tree right }
          | Cursor.forest (RuleForest.cons head tail), false =>
            some { enclosing := position.enclosing, cursor := Cursor.tree head }
          | Cursor.forest (RuleForest.cons head tail), true =>
            some { enclosing := position.enclosing, cursor := Cursor.forest tail }
          | x, x_1 => none).bind
        fun position =>
        (match position.cursor, false with
            | Cursor.tree (RuleTree.rule rule site context premises children), false =>
              some { enclosing := position.enclosing, cursor := Cursor.forest children }
            | Cursor.tree (RuleTree.existsE binder body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.forallE binder body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.initializerE site body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.initializerE site], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.executionE binder body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.executionE binder], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.sharedE binder body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.publishGroup bindings body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.atPublication binding body), false =>
              some { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding], cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
              some
                { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                  cursor := Cursor.tree body }
            | Cursor.tree (RuleTree.choice site left right), false =>
              some { enclosing := position.enclosing, cursor := Cursor.tree left }
            | Cursor.tree (RuleTree.choice site left right), true =>
              some { enclosing := position.enclosing, cursor := Cursor.tree right }
            | Cursor.forest (RuleForest.cons head tail), false =>
              some { enclosing := position.enclosing, cursor := Cursor.tree head }
            | Cursor.forest (RuleForest.cons head tail), true =>
              some { enclosing := position.enclosing, cursor := Cursor.forest tail }
            | x, x_1 => none).bind
          fun position =>
          (match position.cursor, false with
              | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                some { enclosing := position.enclosing, cursor := Cursor.forest children }
              | Cursor.tree (RuleTree.existsE binder body), false =>
                some { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.forallE binder body), false =>
                some { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.initializerE site body), false =>
                some { enclosing := position.enclosing ++ [ScopeFrame.initializerE site], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.executionE binder body), false =>
                some { enclosing := position.enclosing ++ [ScopeFrame.executionE binder], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.sharedE binder body), false =>
                some { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                some
                  { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.atPublication binding body), false =>
                some
                  { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding], cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                some
                  { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                    cursor := Cursor.tree body }
              | Cursor.tree (RuleTree.choice site left right), false =>
                some { enclosing := position.enclosing, cursor := Cursor.tree left }
              | Cursor.tree (RuleTree.choice site left right), true =>
                some { enclosing := position.enclosing, cursor := Cursor.tree right }
              | Cursor.forest (RuleForest.cons head tail), false =>
                some { enclosing := position.enclosing, cursor := Cursor.tree head }
              | Cursor.forest (RuleForest.cons head tail), true =>
                some { enclosing := position.enclosing, cursor := Cursor.forest tail }
              | x, x_1 => none).bind
            fun position =>
            (match position.cursor, false with
                | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                  some { enclosing := position.enclosing, cursor := Cursor.forest children }
                | Cursor.tree (RuleTree.existsE binder body), false =>
                  some { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.forallE binder body), false =>
                  some { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.initializerE site body), false =>
                  some { enclosing := position.enclosing ++ [ScopeFrame.initializerE site], cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.executionE binder body), false =>
                  some { enclosing := position.enclosing ++ [ScopeFrame.executionE binder], cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.sharedE binder body), false =>
                  some { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                  some
                    { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                      cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.atPublication binding body), false =>
                  some
                    { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                      cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                  some
                    { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                      cursor := Cursor.tree body }
                | Cursor.tree (RuleTree.choice site left right), false =>
                  some { enclosing := position.enclosing, cursor := Cursor.tree left }
                | Cursor.tree (RuleTree.choice site left right), true =>
                  some { enclosing := position.enclosing, cursor := Cursor.tree right }
                | Cursor.forest (RuleForest.cons head tail), false =>
                  some { enclosing := position.enclosing, cursor := Cursor.tree head }
                | Cursor.forest (RuleForest.cons head tail), true =>
                  some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                | x, x_1 => none).bind
              fun position =>
              (match position.cursor, false with
                  | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                    some { enclosing := position.enclosing, cursor := Cursor.forest children }
                  | Cursor.tree (RuleTree.existsE binder body), false =>
                    some { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.forallE binder body), false =>
                    some { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.initializerE site body), false =>
                    some
                      { enclosing := position.enclosing ++ [ScopeFrame.initializerE site], cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.executionE binder body), false =>
                    some
                      { enclosing := position.enclosing ++ [ScopeFrame.executionE binder], cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.sharedE binder body), false =>
                    some { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                    some
                      { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                        cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.atPublication binding body), false =>
                    some
                      { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                        cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                    some
                      { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                        cursor := Cursor.tree body }
                  | Cursor.tree (RuleTree.choice site left right), false =>
                    some { enclosing := position.enclosing, cursor := Cursor.tree left }
                  | Cursor.tree (RuleTree.choice site left right), true =>
                    some { enclosing := position.enclosing, cursor := Cursor.tree right }
                  | Cursor.forest (RuleForest.cons head tail), false =>
                    some { enclosing := position.enclosing, cursor := Cursor.tree head }
                  | Cursor.forest (RuleForest.cons head tail), true =>
                    some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                  | x, x_1 => none).bind
                fun position =>
                (match position.cursor, false with
                    | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                      some { enclosing := position.enclosing, cursor := Cursor.forest children }
                    | Cursor.tree (RuleTree.existsE binder body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.forallE binder body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.initializerE site body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                          cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.executionE binder body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                          cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.sharedE binder body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                          cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.atPublication binding body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                          cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                      some
                        { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                          cursor := Cursor.tree body }
                    | Cursor.tree (RuleTree.choice site left right), false =>
                      some { enclosing := position.enclosing, cursor := Cursor.tree left }
                    | Cursor.tree (RuleTree.choice site left right), true =>
                      some { enclosing := position.enclosing, cursor := Cursor.tree right }
                    | Cursor.forest (RuleForest.cons head tail), false =>
                      some { enclosing := position.enclosing, cursor := Cursor.tree head }
                    | Cursor.forest (RuleForest.cons head tail), true =>
                      some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                    | x, x_1 => none).bind
                  fun position =>
                  (match position.cursor, false with
                      | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                        some { enclosing := position.enclosing, cursor := Cursor.forest children }
                      | Cursor.tree (RuleTree.existsE binder body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.existsE binder], cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.forallE binder body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.forallE binder], cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.initializerE site body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                            cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.executionE binder body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                            cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.sharedE binder body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder], cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                            cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.atPublication binding body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                            cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                        some
                          { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                            cursor := Cursor.tree body }
                      | Cursor.tree (RuleTree.choice site left right), false =>
                        some { enclosing := position.enclosing, cursor := Cursor.tree left }
                      | Cursor.tree (RuleTree.choice site left right), true =>
                        some { enclosing := position.enclosing, cursor := Cursor.tree right }
                      | Cursor.forest (RuleForest.cons head tail), false =>
                        some { enclosing := position.enclosing, cursor := Cursor.tree head }
                      | Cursor.forest (RuleForest.cons head tail), true =>
                        some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                      | x, x_1 => none).bind
                    fun position =>
                    (match position.cursor, false with
                        | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                          some { enclosing := position.enclosing, cursor := Cursor.forest children }
                        | Cursor.tree (RuleTree.existsE binder body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.existsE binder],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.forallE binder body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.forallE binder],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.initializerE site body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.executionE binder body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.sharedE binder body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.atPublication binding body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                          some
                            { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                              cursor := Cursor.tree body }
                        | Cursor.tree (RuleTree.choice site left right), false =>
                          some { enclosing := position.enclosing, cursor := Cursor.tree left }
                        | Cursor.tree (RuleTree.choice site left right), true =>
                          some { enclosing := position.enclosing, cursor := Cursor.tree right }
                        | Cursor.forest (RuleForest.cons head tail), false =>
                          some { enclosing := position.enclosing, cursor := Cursor.tree head }
                        | Cursor.forest (RuleForest.cons head tail), true =>
                          some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                        | x, x_1 => none).bind
                      fun position =>
                      (match position.cursor, false with
                          | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                            some { enclosing := position.enclosing, cursor := Cursor.forest children }
                          | Cursor.tree (RuleTree.existsE binder body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.existsE binder],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.forallE binder body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.forallE binder],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.initializerE site body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.executionE binder body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.sharedE binder body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.atPublication binding body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                            some
                              { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                                cursor := Cursor.tree body }
                          | Cursor.tree (RuleTree.choice site left right), false =>
                            some { enclosing := position.enclosing, cursor := Cursor.tree left }
                          | Cursor.tree (RuleTree.choice site left right), true =>
                            some { enclosing := position.enclosing, cursor := Cursor.tree right }
                          | Cursor.forest (RuleForest.cons head tail), false =>
                            some { enclosing := position.enclosing, cursor := Cursor.tree head }
                          | Cursor.forest (RuleForest.cons head tail), true =>
                            some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                          | x, x_1 => none).bind
                        fun position =>
                        (match position.cursor, false with
                            | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                              some { enclosing := position.enclosing, cursor := Cursor.forest children }
                            | Cursor.tree (RuleTree.existsE binder body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.existsE binder],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.forallE binder body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.forallE binder],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.initializerE site body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.executionE binder body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.sharedE binder body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.atPublication binding body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                              some
                                { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                                  cursor := Cursor.tree body }
                            | Cursor.tree (RuleTree.choice site left right), false =>
                              some { enclosing := position.enclosing, cursor := Cursor.tree left }
                            | Cursor.tree (RuleTree.choice site left right), true =>
                              some { enclosing := position.enclosing, cursor := Cursor.tree right }
                            | Cursor.forest (RuleForest.cons head tail), false =>
                              some { enclosing := position.enclosing, cursor := Cursor.tree head }
                            | Cursor.forest (RuleForest.cons head tail), true =>
                              some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                            | x, x_1 => none).bind
                          fun position =>
                          (match position.cursor, false with
                              | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                                some { enclosing := position.enclosing, cursor := Cursor.forest children }
                              | Cursor.tree (RuleTree.existsE binder body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.existsE binder],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.forallE binder body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.forallE binder],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.initializerE site body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.executionE binder body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.sharedE binder body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.atPublication binding body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                                some
                                  { enclosing := position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                                    cursor := Cursor.tree body }
                              | Cursor.tree (RuleTree.choice site left right), false =>
                                some { enclosing := position.enclosing, cursor := Cursor.tree left }
                              | Cursor.tree (RuleTree.choice site left right), true =>
                                some { enclosing := position.enclosing, cursor := Cursor.tree right }
                              | Cursor.forest (RuleForest.cons head tail), false =>
                                some { enclosing := position.enclosing, cursor := Cursor.tree head }
                              | Cursor.forest (RuleForest.cons head tail), true =>
                                some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                              | x, x_1 => none).bind
                            fun position =>
                            (match position.cursor, true with
                                | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                                  some { enclosing := position.enclosing, cursor := Cursor.forest children }
                                | Cursor.tree (RuleTree.existsE binder body), false =>
                                  some
                                    { enclosing := position.enclosing ++ [ScopeFrame.existsE binder],
                                      cursor := Cursor.tree body }
                                | Cursor.tree (RuleTree.forallE binder body), false =>
                                  some
                                    { enclosing := position.enclosing ++ [ScopeFrame.forallE binder],
                                      cursor := Cursor.tree body }
                                | Cursor.tree (RuleTree.initializerE site body), false =>
                                  some
                                    { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                                      cursor := Cursor.tree body }
                                | Cursor.tree (RuleTree.executionE binder body), false =>
                                  some
                                    { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                                      cursor := Cursor.tree body }
                                | Cursor.tree (RuleTree.sharedE binder body), false =>
                                  some
                                    { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder],
                                      cursor := Cursor.tree body }
                                | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                                  some
                                    { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                                      cursor := Cursor.tree body }
                                | Cursor.tree (RuleTree.atPublication binding body), false =>
                                  some
                                    { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                                      cursor := Cursor.tree body }
                                | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                                  some
                                    {
                                      enclosing :=
                                        position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                                      cursor := Cursor.tree body }
                                | Cursor.tree (RuleTree.choice site left right), false =>
                                  some { enclosing := position.enclosing, cursor := Cursor.tree left }
                                | Cursor.tree (RuleTree.choice site left right), true =>
                                  some { enclosing := position.enclosing, cursor := Cursor.tree right }
                                | Cursor.forest (RuleForest.cons head tail), false =>
                                  some { enclosing := position.enclosing, cursor := Cursor.tree head }
                                | Cursor.forest (RuleForest.cons head tail), true =>
                                  some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                                | x, x_1 => none).bind
                              fun position =>
                              (match position.cursor, false with
                                  | Cursor.tree (RuleTree.rule rule site context premises children), false =>
                                    some { enclosing := position.enclosing, cursor := Cursor.forest children }
                                  | Cursor.tree (RuleTree.existsE binder body), false =>
                                    some
                                      { enclosing := position.enclosing ++ [ScopeFrame.existsE binder],
                                        cursor := Cursor.tree body }
                                  | Cursor.tree (RuleTree.forallE binder body), false =>
                                    some
                                      { enclosing := position.enclosing ++ [ScopeFrame.forallE binder],
                                        cursor := Cursor.tree body }
                                  | Cursor.tree (RuleTree.initializerE site body), false =>
                                    some
                                      { enclosing := position.enclosing ++ [ScopeFrame.initializerE site],
                                        cursor := Cursor.tree body }
                                  | Cursor.tree (RuleTree.executionE binder body), false =>
                                    some
                                      { enclosing := position.enclosing ++ [ScopeFrame.executionE binder],
                                        cursor := Cursor.tree body }
                                  | Cursor.tree (RuleTree.sharedE binder body), false =>
                                    some
                                      { enclosing := position.enclosing ++ [ScopeFrame.sharedE binder],
                                        cursor := Cursor.tree body }
                                  | Cursor.tree (RuleTree.publishGroup bindings body), false =>
                                    some
                                      { enclosing := position.enclosing ++ [ScopeFrame.publishGroup bindings],
                                        cursor := Cursor.tree body }
                                  | Cursor.tree (RuleTree.atPublication binding body), false =>
                                    some
                                      { enclosing := position.enclosing ++ [ScopeFrame.atPublication binding],
                                        cursor := Cursor.tree body }
                                  | Cursor.tree (RuleTree.aliasPublication original aliasName body), false =>
                                    some
                                      {
                                        enclosing :=
                                          position.enclosing ++ [ScopeFrame.aliasPublication original aliasName],
                                        cursor := Cursor.tree body }
                                  | Cursor.tree (RuleTree.choice site left right), false =>
                                    some { enclosing := position.enclosing, cursor := Cursor.tree left }
                                  | Cursor.tree (RuleTree.choice site left right), true =>
                                    some { enclosing := position.enclosing, cursor := Cursor.tree right }
                                  | Cursor.forest (RuleForest.cons head tail), false =>
                                    some { enclosing := position.enclosing, cursor := Cursor.tree head }
                                  | Cursor.forest (RuleForest.cons head tail), true =>
                                    some { enclosing := position.enclosing, cursor := Cursor.forest tail }
                                  | x, x_1 => none).bind
                                fun position =>
                                match position.cursor with
                                | Cursor.tree (RuleTree.existsE binder body) =>
                                  if
                                      (match binder.kind with
                                        | BinderKind.viewLogic => true
                                        | BinderKind.eventProof => true
                                        | BinderKind.publishedInstance => true
                                        | x => false) =
                                        true then
                                    some { binder := binder, enclosing := position.enclosing, subtree := body }
                                  else none
                                | x => none) =
    some
      { binder := { site := body.site, kind := BinderKind.eventProof },
        enclosing :=
          scope ++
            ([ScopeFrame.existsE { site := formalSite, kind := BinderKind.description },
                ScopeFrame.existsE { site := site, kind := BinderKind.viewLogic },
                ScopeFrame.forallE { site := site, kind := BinderKind.invocation },
                ScopeFrame.existsE { site := formalSite, kind := BinderKind.receipt }] ++
              ([] ++ [ScopeFrame.sharedE { site := formalSite, kind := BinderKind.shared }])),
        subtree :=
          RuleTree.rule Rule.sequence body.site
            (List.filter
                (fun binding =>
                  !(formalName == binding.name || List.any context fun prior => prior.name == binding.name))
                pattern.bindingRecords ++
              { name := formalName, owner := formalSite, kind := BindingKind.formal, annotation := formalAnnotation,
                  entry := some Entry.computation, singleUse := Source.nameCount formalName body == 1 } ::
                context)
            (List.map
                (fun kind =>
                  Premise.atom
                    (atom kind body.site
                      (List.filter
                          (fun binding =>
                            !(formalName == binding.name || List.any context fun prior => prior.name == binding.name))
                          pattern.bindingRecords ++
                        { name := formalName, owner := formalSite, kind := BindingKind.formal,
                            annotation := formalAnnotation, entry := some Entry.computation,
                            singleUse := Source.nameCount formalName body == 1 } ::
                          context)
                      [site, formalSite]))
                [AtomKind.completeBodyConsumer, AtomKind.actualReturnOrPendingSuffix] ++
              [Premise.checking
                  { mode := CheckMode.computation, site := body.site,
                    context :=
                      List.filter
                          (fun binding =>
                            !(formalName == binding.name || List.any context fun prior => prior.name == binding.name))
                          pattern.bindingRecords ++
                        { name := formalName, owner := formalSite, kind := BindingKind.formal,
                            annotation := formalAnnotation, entry := some Entry.computation,
                            singleUse := Source.nameCount formalName body == 1 } ::
                          context,
                    lower := { site := body.site, port := Port.finalRoot },
                    upper := { site := site, port := Port.bodyConsumer } }])
            (RuleForest.cons
              (sourceRules
                (List.filter
                    (fun binding =>
                      !(formalName == binding.name || List.any context fun prior => prior.name == binding.name))
                    pattern.bindingRecords ++
                  { name := formalName, owner := formalSite, kind := BindingKind.formal, annotation := formalAnnotation,
                      entry := some Entry.computation, singleUse := Source.nameCount formalName body == 1 } ::
                    context)
                body)
              RuleForest.nil) }
YulangClosure.OriginalSource.LogicalOccurrencesR93.inventory_iff_lookup : ∀
  (index : YulangClosure.OriginalSource.LogicalOccurrencesR93.Index)
  (route : YulangClosure.OriginalSource.LogicalOccurrencesR93.Route)
  (occurrence : YulangClosure.OriginalSource.LogicalOccurrencesR93.Occurrence),
  (route, occurrence) ∈ YulangClosure.OriginalSource.LogicalOccurrencesR93.inventory index ↔
    YulangClosure.OriginalSource.LogicalOccurrencesR93.lookup index route = some occurrence
'YulangClosure.OriginalSource.LogicalOccurrencesR93.inventory_iff_lookup' depends on axioms: [propext, Quot.sound]
YulangClosure.OriginalSource.LogicalOccurrencesR93.encode_lookup : ∀
  (scope : List YulangClosure.OriginalSource.LogicalOccurrencesR93.ScopeFrame)
  (cursor : YulangClosure.OriginalSource.LogicalOccurrencesR93.Cursor)
  (route : YulangClosure.OriginalSource.LogicalOccurrencesR93.Route),
  YulangClosure.OriginalSource.LogicalOccurrencesR93.lookup
      (YulangClosure.OriginalSource.LogicalOccurrencesR93.encode scope cursor) route =
    YulangClosure.OriginalSource.LogicalOccurrencesR93.observe scope cursor route
'YulangClosure.OriginalSource.LogicalOccurrencesR93.encode_lookup' depends on axioms: [propext, sorryAx]
YulangClosure.OriginalSource.LogicalOccurrencesR93.observe_eq_follow : ∀
  (scope : List YulangClosure.OriginalSource.LogicalOccurrencesR93.ScopeFrame)
  (cursor : YulangClosure.OriginalSource.LogicalOccurrencesR93.Cursor)
  (route : YulangClosure.OriginalSource.LogicalOccurrencesR93.Route),
  YulangClosure.OriginalSource.LogicalOccurrencesR93.observe scope cursor route =
    (YulangClosure.OriginalSource.LogicalOccurrencesR93.follow scope cursor route).bind fun position =>
      YulangClosure.OriginalSource.LogicalOccurrencesR93.payload position.enclosing position.cursor
'YulangClosure.OriginalSource.LogicalOccurrencesR93.observe_eq_follow' depends on axioms: [propext]
YulangClosure.OriginalSource.LogicalOccurrencesR93.source_membership_iff : ∀
  (context : YulangClosure.OriginalSource.Context) {category : YulangClosure.OriginalSource.Category}
  (source : YulangClosure.OriginalSource.Source category)
  (scope : List YulangClosure.OriginalSource.LogicalOccurrencesR93.ScopeFrame)
  (route : YulangClosure.OriginalSource.LogicalOccurrencesR93.Route)
  (occurrence : YulangClosure.OriginalSource.LogicalOccurrencesR93.Occurrence),
  (route, occurrence) ∈ YulangClosure.OriginalSource.LogicalOccurrencesR93.sourceInventory context source scope ↔
    YulangClosure.OriginalSource.LogicalOccurrencesR93.observe scope
        (YulangClosure.OriginalSource.LogicalOccurrencesR93.Cursor.tree
          (YulangClosure.OriginalSource.sourceRules context source))
        route =
      some occurrence
'YulangClosure.OriginalSource.LogicalOccurrencesR93.source_membership_iff' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
YulangClosure.OriginalSource.LogicalOccurrencesR93.full_route_unique : ∀
  (context : YulangClosure.OriginalSource.Context) {category : YulangClosure.OriginalSource.Category}
  (source : YulangClosure.OriginalSource.Source category)
  (scope : List YulangClosure.OriginalSource.LogicalOccurrencesR93.ScopeFrame)
  (route : YulangClosure.OriginalSource.LogicalOccurrencesR93.Route)
  (first second : YulangClosure.OriginalSource.LogicalOccurrencesR93.Occurrence),
  (route, first) ∈ YulangClosure.OriginalSource.LogicalOccurrencesR93.sourceInventory context source scope →
    (route, second) ∈ YulangClosure.OriginalSource.LogicalOccurrencesR93.sourceInventory context source scope →
      first = second
'YulangClosure.OriginalSource.LogicalOccurrencesR93.full_route_unique' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
YulangClosure.OriginalSource.LogicalOccurrencesR93.source_provenance : ∀
  (context : YulangClosure.OriginalSource.Context) {category : YulangClosure.OriginalSource.Category}
  (source : YulangClosure.OriginalSource.Source category)
  (scope : List YulangClosure.OriginalSource.LogicalOccurrencesR93.ScopeFrame)
  (route : YulangClosure.OriginalSource.LogicalOccurrencesR93.Route)
  (occurrence : YulangClosure.OriginalSource.LogicalOccurrencesR93.Occurrence),
  (route, occurrence) ∈ YulangClosure.OriginalSource.LogicalOccurrencesR93.sourceInventory context source scope →
    ∃ binder body,
      YulangClosure.OriginalSource.LogicalOccurrencesR93.follow scope
            (YulangClosure.OriginalSource.LogicalOccurrencesR93.Cursor.tree
              (YulangClosure.OriginalSource.sourceRules context source))
            route =
          some
            { enclosing := occurrence.enclosing,
              cursor :=
                YulangClosure.OriginalSource.LogicalOccurrencesR93.Cursor.tree
                  (YulangClosure.OriginalSource.RuleTree.existsE binder body) } ∧
        YulangClosure.OriginalSource.LogicalOccurrencesR93.logicalKind binder.kind = true ∧
          occurrence.binder = binder ∧ occurrence.subtree = body
'YulangClosure.OriginalSource.LogicalOccurrencesR93.source_provenance' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
YulangClosure.OriginalSource.LogicalOccurrencesR93.app_exact : ∀ (context : YulangClosure.OriginalSource.Context)
  (mark : YulangClosure.OriginalSource.Mark)
  (callee argument : YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression)
  (scope : List YulangClosure.OriginalSource.LogicalOccurrencesR93.ScopeFrame),
  YulangClosure.OriginalSource.LogicalOccurrencesR93.observe scope
      (YulangClosure.OriginalSource.LogicalOccurrencesR93.Cursor.tree
        (YulangClosure.OriginalSource.sourceRules context
          (YulangClosure.OriginalSource.Source.app mark callee argument)))
      (YulangClosure.OriginalSource.LogicalOccurrencesR93.annotationRoute mark) =
    some
      { binder := { site := mark.site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic }, enclosing := scope,
        subtree := YulangClosure.OriginalSource.LogicalOccurrencesR93.appRule context mark callee argument }
'YulangClosure.OriginalSource.LogicalOccurrencesR93.app_exact' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
YulangClosure.OriginalSource.LogicalOccurrencesR93.lambda_body_exact : ∀
  (context : YulangClosure.OriginalSource.Context) (mark : YulangClosure.OriginalSource.Mark)
  (formal : YulangClosure.OriginalSource.Formal)
  (pattern : YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.pattern)
  (body : YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression)
  (scope : List YulangClosure.OriginalSource.LogicalOccurrencesR93.ScopeFrame),
  YulangClosure.OriginalSource.LogicalOccurrencesR93.observe scope
      (YulangClosure.OriginalSource.LogicalOccurrencesR93.Cursor.tree
        (YulangClosure.OriginalSource.sourceRules context
          (YulangClosure.OriginalSource.Source.lambda mark formal pattern body)))
      (YulangClosure.OriginalSource.LogicalOccurrencesR93.bodyRoute mark formal) =
    some
      { binder := { site := body.site, kind := YulangClosure.OriginalSource.BinderKind.eventProof },
        enclosing := YulangClosure.OriginalSource.LogicalOccurrencesR93.bodyScope scope mark formal,
        subtree := YulangClosure.OriginalSource.LogicalOccurrencesR93.bodyRule context mark formal pattern body }
'YulangClosure.OriginalSource.LogicalOccurrencesR93.lambda_body_exact' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
YulangClosure.OriginalSource.LogicalOccurrencesR93.app_inventory : ∀ (context : YulangClosure.OriginalSource.Context)
  (mark : YulangClosure.OriginalSource.Mark)
  (callee argument : YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression)
  (scope : List YulangClosure.OriginalSource.LogicalOccurrencesR93.ScopeFrame),
  (YulangClosure.OriginalSource.LogicalOccurrencesR93.annotationRoute mark,
      { binder := { site := mark.site, kind := YulangClosure.OriginalSource.BinderKind.viewLogic }, enclosing := scope,
        subtree := YulangClosure.OriginalSource.LogicalOccurrencesR93.appRule context mark callee argument }) ∈
    YulangClosure.OriginalSource.LogicalOccurrencesR93.sourceInventory context
      (YulangClosure.OriginalSource.Source.app mark callee argument) scope
'YulangClosure.OriginalSource.LogicalOccurrencesR93.app_inventory' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
YulangClosure.OriginalSource.LogicalOccurrencesR93.lambda_body_inventory : ∀
  (context : YulangClosure.OriginalSource.Context) (mark : YulangClosure.OriginalSource.Mark)
  (formal : YulangClosure.OriginalSource.Formal)
  (pattern : YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.pattern)
  (body : YulangClosure.OriginalSource.Source YulangClosure.OriginalSource.Category.expression)
  (scope : List YulangClosure.OriginalSource.LogicalOccurrencesR93.ScopeFrame),
  (YulangClosure.OriginalSource.LogicalOccurrencesR93.bodyRoute mark formal,
      { binder := { site := body.site, kind := YulangClosure.OriginalSource.BinderKind.eventProof },
        enclosing := YulangClosure.OriginalSource.LogicalOccurrencesR93.bodyScope scope mark formal,
        subtree := YulangClosure.OriginalSource.LogicalOccurrencesR93.bodyRule context mark formal pattern body }) ∈
    YulangClosure.OriginalSource.LogicalOccurrencesR93.sourceInventory context
      (YulangClosure.OriginalSource.Source.lambda mark formal pattern body) scope
'YulangClosure.OriginalSource.LogicalOccurrencesR93.lambda_body_inventory' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]

```

### Complete stderr

```text

```

## Independent result review

Pending. An independent reviewer who did not author the candidate or input
review must check the pushed authorization, exact command/input digest, exit
status and all ten type/axiom outputs. The result remains a candidate until
that review and Luna's adjudication; source/native and original parent gates
remain OPEN.
