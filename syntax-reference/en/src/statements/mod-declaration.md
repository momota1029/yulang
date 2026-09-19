# `mod` declaration

## 1. Authority and scope

This page specifies the `syntax-v0` `ModDeclaration`. The Authoritative
canonical `Statement` and root `Declaration` `mod` extension in
`notes/design/2026-08-20-yu-syntax-chasa-architecture.md`, including Mod,
governs this page. It does not specify module loading, namespaces, exports,
test execution, derives, companions, or lowering.

## 2. Accepted syntax

```text
ModDeclaration := [ VisibilityKw Gmod ] ModKw Gmod ModIdentity Gmod ModBody
VisibilityKw := MyKw | OurKw | PubKw
ModKw := exact maximal word "mod"
ModIdentity := Name | TestModuleMarker [ Gmod Name ]
Name := Identifier
TestModuleMarker := Identifier("test")
BodyStarter := Semicolon | LBrace | Colon
ModBody := Semicolon | BracedStatementBlockExpression | Colon ModColonBody
ModColonBody := G0* Statement [ Semicolon ] | IndentedStatementBlock
G0* := maximal trivia containing no physical newline
```

`Gmod` is empty or maximal same-line trivia, or trivia whose following indent
is strictly deeper than the declaration base. `Statement`,
`BracedStatementBlockExpression`, and `IndentedStatementBlock` use their
named reference productions.

## 3. Admission and boundaries

An exact bare `mod`, or one after an admitted visibility prefix, selects this
declaration. Maximal words such as `module`, `modular`, and `my_mod` are not
split. `test` immediately after `mod` is a marker; it is anonymous only when
a body starter follows. Thus `mod test` at EOF has a missing second name.

Only exact `;`, `{`, and a lone `:` start a body. After `:`, same-line trivia
starts one inline `Statement`; a strictly deeper newline starts an indented
block. Equal-or-shallower newlines, outer separators, closes, dedents, and
stops remain with their outer owner.

## 4. Source-order Rowan schema

`ModDeclaration` has this closed, source-order child schema:

```text
ModDeclaration := [ VisibilityKw Trivia ] ModKw Trivia
                  ( Name | TestModuleMarker [ Trivia Name ] ) Trivia
                  ( Semicolon | BracedStatementBlockExpression |
                    Colon ( Statement [ Semicolon ] | IndentedStatementBlock ) )
TestModuleMarker := Identifier("test")
```

There is no header, body, anonymous-name, or inline-body wrapper. The schema
contains exactly one identity alternative and exactly one body alternative.

## 5. Recovery CST

`Name`, `TestName`, `BodyIntroducer`, and colon-body failures occupy their own
documented slots. A missing slot is `Missing`; a malformed run is one or more
adjacent `Error` leaves in that slot. Name failure does not add a same-cause
body-introducer failure. Block recovery, including close handoff, remains in
the selected block node.

```xml
<ModDeclaration>
  <ModKw text="mod" />
  <Whitespace text=" " />
  <Missing />
  <Semicolon text=";" />
</ModDeclaration>
```

Here `Missing` is the name slot. The semicolon remains the selected body.

For `mod @;`, the same name slot retains the raw malformed source as `Error+`.

```xml
<ModDeclaration><ModKw text="mod" /><Whitespace text=" " /><Error text="@" /><Semicolon text=";" /></ModDeclaration>
```

## 6. Source and CST examples

The accepted source `mod test {}` has one marker and one braced body.

```xml
<ModDeclaration>
  <ModKw text="mod" />
  <Whitespace text=" " />
  <TestModuleMarker>
    <Identifier text="test" />
  </TestModuleMarker>
  <Whitespace text=" " />
  <BracedStatementBlockExpression>
    <LBrace text="{" />
    <RBrace text="}" />
  </BracedStatementBlockExpression>
</ModDeclaration>
```

## 7. Composition and non-goals

At `Root`, `ModDeclaration` is direct. In a nested canonical owner, it is the
one declaration child of `Statement`. See [Rowan CST notation](../conventions/rowan-cst.md)
and [recovery topology](../conventions/recovery-error-invalid-topology.md).
