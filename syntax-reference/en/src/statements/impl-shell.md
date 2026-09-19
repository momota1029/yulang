# Standalone `impl` declaration shell

## 1. Authority and scope

This page specifies the standalone `ImplDeclaration` shell in `syntax-v0`.
`IMD-G`, `IMD-J`, `IMD-T`, and `IMD-R`, plus the Impl current-Item recovery
record, govern it. Type-attached tails, companions, member semantics,
conformance, lowering, resolution, inference, and formatting are outside this
page.

## 2. Accepted syntax

```text
ImplDeclaration := [ VisibilityKw Gimpl+ ] ImplKw Gimpl-head RequiredTypeExpression(Impl::Head) ImplAfterHead
VisibilityKw := MyKw | OurKw | PubKw
ImplKw := exact maximal word "impl"
ImplAfterHead := ImplDescription ImplBody | ImplBody
ImplDescription := DescriptionColon G0* RequiredTypeExpression(Impl::Description)
ImplBody := BodylessSemicolon | BracedStatementBlockExpression | ImplColonBody
ImplColonBody := BodyColon G0* RequiredCanonicalStatement(Impl::Body) [ InlineTerminalSemicolon ] | BodyColon Gimpl-indent IndentedStatementBlock(Impl::IndentedStatement)
G0* := maximal trivia containing no physical newline
Gimpl-indent := non-empty continuation trivia followed by indent strictly deeper than the declaration base
```

`RequiredTypeExpression` uses the full required type production in the
[TypeExpression reference](../types/type-expression-core.md). `RequiredCanonicalStatement`
uses the named canonical `Statement` production.

## 3. Admission, phase selection, and boundaries

Exact bare or visibility-led `impl` selects this declaration. `implFoo`,
`implement`, and `my_impl` are not split. The first bare colon after the head
is a description colon only when its following trivia contains no physical
newline; after a description, a later colon is a body colon. `;`, `{`, and the
body colon select the three body forms. Outer separators, dedents, matching
closes, and unclaimed boundaries remain outer-owned.

## 4. Source-order Rowan schema

```text
ImplDeclaration := [ VisibilityKw Trivia ] ImplKw Trivia TypeExpression
                   [ ImplDescription ] ( Semicolon | BracedStatementBlockExpression |
                     Colon ( Statement [ Semicolon ] | IndentedStatementBlock ) )
ImplDescription := Colon Trivia TypeExpression
```

The declaration has exactly one head, zero or one description, and exactly one
selected body form. It has no header, body, member-list, or separator wrapper.

## 5. Recovery CST

An absent head is `Missing(Impl::Head)` and does not cascade to a body
introducer. A missing description after an accepted description colon is
`Missing(Impl::Description)` and does not create same-cause body recovery. An
absent body starter after a complete head is `Missing(Impl::BodyIntroducer)`.
After an accepted body colon, an absent inline body is `Missing(Impl::Body)`.
After accepted or retried head or description content begins, malformed nested
content remains TypeExpression-owned; braced and indented recovery stays with
their selected child nodes.

```xml
<ImplDeclaration><ImplKw text="impl" /><Whitespace text=" " /><TypeExpression><Identifier text="T" /></TypeExpression><Missing /></ImplDeclaration>
```

An initial malformed head run is `Error+` directly in `ImplDeclaration`. An
initial malformed description run is directly in `ImplDescription`. A
`TypeExpression` occurs only for accepted or retried content.

```xml
<ImplDeclaration><ImplKw text="impl" /><Whitespace text=" " /><Error text="@" /><Semicolon text=";" /></ImplDeclaration>
```

## 6. Source and CST examples

The accepted source `impl int: Eq;` has one description and one bodyless body.

```xml
<ImplDeclaration>
  <ImplKw text="impl" /><Whitespace text=" " /><TypeExpression><Identifier text="int" /></TypeExpression>
  <ImplDescription><Colon text=":" /><Whitespace text=" " /><TypeExpression><Identifier text="Eq" /></TypeExpression></ImplDescription>
  <Semicolon text=";" />
</ImplDeclaration>
```

## 7. Composition and non-goals

Head and description retain ordinary full TypeExpression grammar. The body
uses canonical statements and existing statement blocks; `via` is not an Impl
keyword. See [bare nominal `type` declaration form](bare-nominal-type.md) and
[recovery topology](../conventions/recovery-error-invalid-topology.md).
