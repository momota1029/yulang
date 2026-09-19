# Binding and `use` statement forms

## Status and authority

This page records the Binding and `use` statement forms accepted by `syntax-v0` and their direct Rowan CST.
The Authoritative *canonical `Statement` binding / use declaration extension* section in `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` defines Binding grammar, placement, CST, and layout.
The Authoritative *Complete `use` declaration grammar and projection* section in the same record defines `UseTree` grammar and CST; its *Oracle state machine* and *UseQualifiers*, `UseAnchor` subsections define anchor admission.
The Authoritative `notes/design/2026-09-08-successor-binding-current-item-recovery.md` defines Binding current-Item recovery.
The Authoritative `notes/design/2026-09-12-successor-use-group-foreign-close-topology.md` defines `UseGroupForeignClose`.

[Syntax content model](../conventions/syntax-content-model.md) is a placement inventory and does not replace those authorities.

## Placement and accepted source forms

Binding and `use` are accepted at `Root` and in nested statement owners.
At `Root`, `BindingStatement` or `UseDeclaration` is a direct child.
In a nested statement owner, one `Statement` contains exactly one direct `BindingStatement` or `UseDeclaration` child.
`BindingDeclaration` must not be a direct child of `Root` or `Statement`.

The root-only operator definition is not a statement form on this page.
Its `OperatorHeader` and following sibling `OperatorChain` are direct `Root` children and never occur in a nested `Statement`.

```text
BindingStatement :=
    VisibilityKw Gbind Pattern
    [ Gbind Equals BindingBody ]

VisibilityKw := MyKw | OurKw | PubKw

BindingBody :=
    G0* OperatorChain
  | IndentedStatementBlock

UseDeclaration := [ VisibilityKw I+ ] UseKw I+ UseTree

UseTree :=
    UseGroup GroupSuffix
  | ModKw I+ ModPath UsePathSuffix
  | RealmKw Slash SeparatorTarget
  | BandKw ColonColon SeparatorTarget
  | UsePath UsePathSuffix

UsePathSuffix :=
    SingleSuffix
  | TerminalJoin UseGroup GroupSuffix
  | TerminalJoin UseGlob GlobSuffix

SeparatorTarget :=
    UsePath UsePathSuffix
  | UseGroup GroupSuffix
  | UseGlob GlobSuffix

SingleSuffix := (I+ UseAlias)* UseQualifiers?
GroupSuffix := (I+ UseAlias)* UseQualifiers?
GlobSuffix := UseQualifiers?

TerminalJoin := ColonColon | Slash
UsePath := PathSegment ((ColonColon | Slash) PathSegment)*
ModPath := Identifier ((ColonColon | Slash) PathSegment)*
PathSegment := Identifier | OperatorName
OperatorName := LParen Operator RParen

UseGroup := LBrace G* (UseTree G* (Comma G*)?)* RBrace
UseAlias := AsKw I+ Identifier
UseGlob := Star (I+ UseAlias)*
    (I+ WithoutKw I+ UseExclusion (Comma G* UseExclusion)*)?
UseQualifiers := I+ UseVersion (I+ UseAnchor)? | I+ UseAnchor
UseVersion := Version
UseAnchor := WithKw I+ UseAnchorPath
UseAnchorPath := Identifier ((ColonColon | Slash) Identifier)*
UseExclusion := Identifier | OperatorName | Star | UseExclusionGroup
UseExclusionGroup :=
    LParen G* (UseTree G* (Comma G*)?)* RParen
  | LBrace G* (UseTree G* (Comma G*)?)* RBrace
```

`I` is one or more inline trivia tokens, and `G` is maximal trivia in the position that uses it.
`G*` can contain a physical newline; `I+` cannot.
Adjacent `UseTree` items in a `UseGroup` or `UseExclusionGroup` require a comma or intervening `G*` containing a physical newline.
In a top-level `without` list, inline trivia is required before the first exclusion, and commas separate later exclusions.
`UseGroup` is admitted only at spec start or after a separator target.
`UseGlob` is admitted only after a separator target.
`mod` requires the initial `Identifier` in `ModPath`.
`realm/` and `band::` consume their qualifying separator before `SeparatorTarget`; other spellings remain ordinary `UsePath` segments.
`ModPath` creates the same `UsePath` CST node as `UsePath`, with an `Identifier` as its first segment.
`UseAnchorPath` also creates a `UsePath` CST node, but every anchor-path segment is an `Identifier`.

## Direct Rowan CST

`BindingStatement` has exactly one `BindingHeader` child and zero or one `BindingBody` child.
`BindingHeader` contains `VisibilityKw`, `Gbind`, `Pattern`, and, when accepted, `Gbind` and `Equals` in source order.
A bodyless Binding has no empty `BindingBody` node.
Each accepted `Equals` creates one `BindingBody`.
The only structural child of `BindingBody` is either an inline `OperatorChain` or an indented `IndentedStatementBlock`.

`UseDeclaration` contains an optional `VisibilityKw` and following `I+`, `UseKw`, following `I+`, and exactly one `UseTree`, in source order.
When visibility is absent, it creates neither a visibility token nor a zero-width node.

A spec-start group `UseTree` contains exactly one `UseGroup`, zero or more `UseAlias`, and optional `UseQualifiers`, in source order.
A `mod` `UseTree` contains `ModKw`, `I+`, exactly one identifier-first `UsePath`, then its selected `UsePathSuffix` children.
A `realm/` or `band::` `UseTree` contains its two form-marker tokens, then the selected `SeparatorTarget` children.
An ordinary path `UseTree` contains exactly one `UsePath`, then its selected `UsePathSuffix` children.
`TerminalJoin` creates no wrapper node; it is a direct `UseTree` token.

The Single suffix has zero or more `UseAlias` and optional `UseQualifiers`.
A group terminal has exactly one direct `UseGroup`, followed by zero or more `UseAlias` and optional `UseQualifiers`.
A glob terminal has exactly one direct `UseGlob`, followed by optional `UseQualifiers`.

A non-empty `UsePath` contains exactly one `PathSegment`, followed by zero or more separator-token and `PathSegment` pairs.
Each segment is exactly one unwrapped `Identifier` or `OperatorName`.
`UseAlias` contains exactly one each of `AsKw`, `I+`, and `Identifier`.
`UseQualifiers` contains exactly one `UseVersion` and optional `UseAnchor`, or exactly one `UseAnchor`.
`UseAnchor` contains `WithKw`, `I+`, and exactly one `UsePath` whose segments are all `Identifier` tokens.
`UseExclusion` contains exactly one of `Identifier`, `OperatorName`, `Star`, or `UseExclusionGroup`.
`UseGlob`, `UseGroup`, and `UseExclusionGroup` contain their tokens, trivia, and items directly in source order under their source productions.

All direct children preserve source order.
Trivia and literal tokens remain in the lossless CST.

## Boundaries, layout, and composition

`Gbind` is maximal trivia without a physical newline, or maximal trivia containing a physical newline whose following indent is deeper than the Binding start indent.
An equal-or-shallower newline does not belong to Binding and returns to the outer statement owner.

After an exact `=`, no physical newline makes the `BindingBody` structural child an inline `OperatorChain`.
A physical newline followed by an indent deeper than the Binding start indent makes it a non-empty `IndentedStatementBlock`.
The outer owner retains statement separators, dedents, matching closes, outer commas, and companion stops.

A `use` path does not cross a physical newline.
`UseGroup` owns its braces and commas, and `UseExclusionGroup` owns its delimiters and commas.

See also [Rowan CST notation](../conventions/rowan-cst.md), [layout-aware separator authority](../cross-cutting/layout-aware-separator-authority.md), and [recovery `Error` and `Invalid` topology](../conventions/recovery-error-invalid-topology.md).

## Accepted source and CST example

The following is an accepted `use` declaration with a group.

```text
use std::io::{read, write}
```

Its XML-like Rowan notation is:

```xml
<UseDeclaration>
  <UseKw text="use"/>
  <Whitespace text=" "/>
  <UseTree>
    <UsePath>
      <Identifier text="std"/>
      <ColonColon text="::"/>
      <Identifier text="io"/>
    </UsePath>
    <ColonColon text="::"/>
    <UseGroup>
      <LBrace text="{"/>
      <UseTree><UsePath><Identifier text="read"/></UsePath></UseTree>
      <Comma text=","/>
      <Whitespace text=" "/>
      <UseTree><UsePath><Identifier text="write"/></UsePath></UseTree>
      <RBrace text="}"/>
    </UseGroup>
  </UseTree>
</UseDeclaration>
```

## Recovery CST

A missing Binding target is a zero-width `Missing` at the target slot; a malformed target run is a maximal non-empty `Error`.
A retry to a valid Pattern uses the same target slot.
After accepting an exact `=`, a missing body is a zero-width `Missing` within `BindingBody`.
A malformed inline-body run is a maximal non-empty `Error` and does not add a body Missing after reaching a boundary.
An indented Binding body is the completed child owner, so the outer Binding does not duplicate its recovery.

A missing `use` path is a zero-width `Missing` at the path slot.
A missing group item is a zero-width `Missing(GroupEntry)` within its group; a malformed group-entry run is direct `Error+`.
When a group terminal phase lacks its close, `UseGroup` or `UseExclusionGroup` has a direct terminal zero-width `Missing(Close)` for its opener.

Only a locally consumed, unclaimed mismatched `RParen` or `RBrace` creates transparent `UseGroupForeignClose` after outer-close protection.

```text
UseGroupForeignClose := Error+
```

The wrapper occurs once for each consumed foreign close and contains only its non-empty raw `Error` token leaves.
It contains no native trivia, `Missing`, `Invalid`, accepted punctuation, or `UseTree`.
A direct group-entry `Error+` does not enter the wrapper.
`RBracket`, an accepted local close, a protected outer close, and a foreign close inside `recover_group` do not create this wrapper.

## Non-goals

This page does not define Binding destructuring, visibility, body result, recursive scope, or lowering.
For `use`, it does not define lexical import scope, module resolution, export, the meaning of versions or anchors, or qualifier projection.

Other declarations and control statements, future Pattern surface, declaration companions, `derives`, and method attachment are also outside this page.
