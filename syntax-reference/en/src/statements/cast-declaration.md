# Standalone `cast` declaration

## 1. Authority and scope

This page specifies `CastDeclaration` in `syntax-v0`. `CAST-G`, `CAST-J`,
`CAST-T`, and `CAST-R`, including the TargetType and retained caller-boundary
residual, govern it. Conversion registration and application, expected-type
behavior, coherence, lowering, resolution, inference, and formatting are
outside this page.

## 2. Accepted syntax

```text
CastDeclaration := [ VisibilityKw Gcast+ ] CastKw Gcast-pattern CastPatternGroup Gcast-target CastTarget Gcast-form CastForm
VisibilityKw := MyKw | OurKw | PubKw
CastKw := exact maximal word "cast"
CastPatternGroup := LParen Gcast-delimited* RequiredPattern(Cast::Pattern) Gcast-delimited* RParen
CastTarget := Colon Gcast-type RequiredTypeExpression(Cast::TargetType)
CastForm := Semicolon | Equals CastDefinitionBody
CastDefinitionBody := Gcast-inline RequiredOperatorChain(Cast::Body) | IndentedStatementBlock(item-role := Cast::IndentedStatement)
```

`RequiredPattern`, `RequiredTypeExpression`, and `RequiredOperatorChain` name
the required productions in the [Pattern reference](../patterns/pattern-core.md),
[TypeExpression reference](../types/type-expression-core.md), and
[OperatorChain reference](../expressions/operator-chain.md). `Gcast+` and
`Gcast-*` are Cast declaration-continuing trivia.

## 3. Admission, layout, and boundaries

Exact bare or visibility-led `cast` selects this declaration; `casting` and
`castaway` remain ordinary words. Only the matching close of the accepted
Cast-local `(` closes its pattern. Exact `:` starts the target, then exact `;`
or `=` selects the form. After `=`, same-line trivia selects one inline
OperatorChain; a strictly deeper newline selects an indented statement block.
Equal-or-shallower newlines and protected boundaries remain outer-owned.

## 4. Source-order Rowan schema

```text
CastDeclaration := [ VisibilityKw Trivia ] CastKw Trivia CastPattern Trivia CastTarget Trivia
                   ( Semicolon | Equals CastBody )
CastPattern := LParen Trivia Pattern Trivia RParen
CastTarget := Colon Trivia TypeExpression
CastBody := Trivia OperatorChain | IndentedStatementBlock
```

There is exactly one `CastPattern`, one `CastTarget`, and one selected form.
Bodyless form has a direct semicolon; definition has one direct `Equals` and
one `CastBody`. No signature, conversion-rule, source-type, or synthetic body
node is added.

## 5. Recovery CST

The Cast-owned slots are `Cast::PatternIntroducer`, `Cast::Pattern`, the
`CastPattern` close, `Cast::TargetIntroducer`, `Cast::TargetType`,
`Cast::BodyIntroducer`, and `Cast::Body`. A missing slot is `Missing`; a raw
malformed run is `Error+` in that slot. Prefix failures do not consume `)`,
`:`, `;`, or `=` merely to scan, and do not cascade same-cause downstream
missing nodes. Nested Pattern, TypeExpression, and expression recovery remains
with those children.

After an accepted or recovered target colon, EOF, `;`, or `=` produces
`Missing(Cast::TargetType)` before the form is retried at that punctuation.
This is distinct from missing `Cast::TargetIntroducer`.

```xml
<CastDeclaration>
  <CastKw text="cast" /><CastPattern><LParen text="(" /><Pattern><IdentifierPattern><Identifier text="x" /></IdentifierPattern></Pattern><RParen text=")" /></CastPattern>
  <CastTarget><Colon text=":" /><Whitespace text=" " /><TypeExpression><Missing /></TypeExpression></CastTarget>
  <Semicolon text=";" />
</CastDeclaration>
```

The known limitation is retained: when a missing delimiter inside the Cast
pattern or target hides an outer caller boundary that the nested owner can
consume or reinterpret, that boundary is a documented caller-boundary residual,
not accepted syntax or Cast recovery. It requires separate authority.

An initial malformed target run is `Error+` directly in `CastTarget`. A
`TypeExpression` occurs only for accepted or retried target content.

```xml
<CastDeclaration><CastKw text="cast" /><CastPattern><LParen text="(" /><Pattern><IdentifierPattern><Identifier text="x" /></IdentifierPattern></Pattern><RParen text=")" /></CastPattern><CastTarget><Colon text=":" /><Whitespace text=" " /><Error text="@" /></CastTarget><Semicolon text=";" /></CastDeclaration>
```

## 6. Source and CST examples

The accepted source `cast(x: A): B = x` has one pattern, target, and inline
body.

```xml
<CastDeclaration>
  <CastKw text="cast" /><CastPattern><LParen text="(" /><Pattern><IdentifierPattern><Identifier text="x" /></IdentifierPattern><PatternTypeAnnotation><Colon text=":" /><Whitespace text=" " /><TypeExpression><Identifier text="A" /></TypeExpression></PatternTypeAnnotation></Pattern><RParen text=")" /></CastPattern>
  <CastTarget><Colon text=":" /><Whitespace text=" " /><TypeExpression><Identifier text="B" /></TypeExpression></CastTarget>
  <Whitespace text=" " /><Equals text="=" /><CastBody><Whitespace text=" " /><OperatorChain><IdentifierExpression><Identifier text="x" /></IdentifierExpression></OperatorChain></CastBody>
</CastDeclaration>
```

## 7. Composition and non-goals

Pattern and target use their ordinary referenced grammars. Cast adds neither a
brace or colon declaration body, a punctuation-free target/body split, nor a
Cast-specific `via` keyword. See [Rowan CST notation](../conventions/rowan-cst.md)
and [recovery topology](../conventions/recovery-error-invalid-topology.md).
