# `case` and `catch` expressions

## 1. Authority and scope

This page defines `CaseExpression` and `CatchExpression` in `syntax-v0`.
The 2026-08-20 `yu-syntax` architecture defines their accepted grammar and direct Rowan CST.
The Authoritative 2026-09-08 CaseLike structural and Arrow/Body recovery records, and the 2026-09-09 separator and Catch-close record, define their recovery CST.
Admission and CST for scrutinee-less `case:` follow WP-14 of the Authoritative `2026-11-07-parser-gap-closure-addendum-2.md`.
Target-less `catch:` follows WP-16 of the same addendum.

The page covers expression primaries, labels, scrutinees, arm families, patterns, optional guards and Catch handlers, exact arrows, bodies, separators, and Catch braces.
It does not define exhaustiveness, guard, handler, label, exception, or value semantics; function desugaring; HIR; types; diagnostics wording; or formatting.

## 2. Accepted syntax

```text
CaseExpression  := CaseKw (CaseHead | G*) CaseBlock
CatchExpression := CatchKw (CatchHead CatchBlock | G* ":" (CatchInlineArm | CatchIndentedArms))
CaseHead := G* [ CaseLabel G* ] CaseScrutinee
CatchHead := G* [ CatchLabel G* ] CatchScrutinee
CaseLabel := SigilIdentifier
CatchLabel := SigilIdentifier
SigilIdentifier := Apostrophe!Identifier
CaseScrutinee := OperatorChain
CatchScrutinee := OperatorChain
CaseBlock := ":" (CaseInlineArms | CaseIndentedArms)
CatchBlock := ":" (CatchInlineArm | CatchIndentedArms) | "{" CatchBracedArms "}"
CaseInlineArms := CaseArm { CaseArmSeparator CaseArm } [ CaseArmSeparator ]
CatchBracedArms := CatchArm { CatchArmSeparator CatchArm } [ CatchArmSeparator ]
CaseArmSeparator := ","
CatchArmSeparator := ","
CaseArm  := ArmPattern [ CaseGuard ] "->" ArmBody [ ";" ]
CatchArm := ArmPattern [ "," ArmPattern ] [ CatchGuard ] "->" ArmBody [ ";" ]
CaseGuard := (IfKw | WhereKw) OperatorChain
CatchGuard := (IfKw | WhereKw) OperatorChain
ArmBody := OperatorChain | IndentedStatementBlock
```

`case` and `catch` are separate operand-starting primaries.
Case inline arms are comma-separated; colon-inline Catch has exactly one arm.
Indented Case and Catch arms, and braced Catch arms, can have multiple arms.
Case does not accept a braced arm block.

## 3. Admission and boundaries

Only exact maximal contextual `case` and `catch` words admit the corresponding primary; `casefold` and `catcher` remain identifiers.
The case scrutinee stops at `:`.
The catch scrutinee stops at `:` or `{`, allowing only Catch to own a direct braced block.

A `:` immediately after `case` or `catch`, or after trivia on the same line, opens the arm block without a scrutinee.
This form has no label either.
Without `:`, an absent scrutinee keeps its existing recovery.
This omission applies only to colon blocks; a direct braced Catch block still requires a target.

The apostrophe and identifier in a label are adjacent; whitespace cannot split `SigilIdentifier`.
`->` is exact fixed punctuation, not a dynamically associated operator.
A Catch handler comma is a direct `CatchArm` child; an arm-list comma belongs to the selected arm family.
Current-depth Catch-brace newlines and indented arm-indent newlines belong to that family, while an indented body block owns its statement newlines.
The active arm owner returns nested colon, comma, arrow, brace, guard word, and close spelling to their immediate owners.

A line at the arm baseline starts a new arm even when it begins with a sign, as in `-1 -> 2`.
The `-` must touch the integer; the negative integer remains one `Integer` token inside `Pattern`.
A line continuing the preceding arm body must be indented more deeply (WP-15, `spec/01-lexical.md` §1.3).
Neither `+1` nor `- 1` is admitted as a pattern.

An `ArmPattern` whose application head is a bare identifier admits same-line Pattern arguments.
For example, `just x -> x` and `op x, k -> k x` place `x` in a `PatternMlApplicationTail`; the Catch comma still belongs to `CatchArm`.
The parser records only this structure.
Name resolution decides whether the bare head is a binding or a variant.
The Authoritative parser-gap design memo WP-9 supersedes R280's earlier qualified-only rule in this arm context.

## 4. Direct Rowan CST

`CaseExpression` and `CatchExpression` are direct primary children of `OperatorChain`.
With a scrutinee, `CaseExpression` contains its keyword, optional `CaseLabel`, direct `CaseScrutinee`, and direct case block in source order.
In scrutinee-less `case:`, the keyword is followed by a direct `CaseBlock`, with no `CaseScrutinee` node.
The absence of `CaseScrutinee` identifies this form.
With a target, `CatchExpression` contains its keyword, optional `CatchLabel`, direct `CatchScrutinee`, and direct catch block in source order.
In target-less `catch:`, the keyword is followed by a direct `CatchBlock`, with no `CatchScrutinee` node.
Both inline and indented arms use this same `CatchBlock`; the CST of `catch a:` and direct braced Catch blocks is unchanged.
Each label contains one `SigilIdentifier` token, whose apostrophe and identifier are adjacent.
Each scrutinee directly contains its `OperatorChain`.
A `CaseArm` contains direct `Pattern`, optional `CaseGuard`, exact `Arrow`, body, and optional semicolon.
A `CatchArm` contains direct `Pattern`, optional handler `Pattern`, optional `CatchGuard`, exact `Arrow`, body, and optional semicolon.
There is no generic case-like wrapper.

`CatchBlock` directly contains its braces when present; those braces do not create `BracedStatementBlockExpression`.
Case inline arm commas occur in direct `CaseArmSeparator` wrappers.
Catch-braced arm commas occur in direct `CatchArmSeparator` wrappers.
An arm body contains either one direct `OperatorChain` or one direct `IndentedStatementBlock`.

```text
CaseExpression := CaseKw [ CaseLabel ] CaseScrutinee CaseBlock | CaseKw CaseBlock
CatchExpression := CatchKw [ CatchLabel ] CatchScrutinee CatchBlock | CatchKw CatchBlock
CaseInlineArms := CaseArm { CaseArmSeparator CaseArm } [ CaseArmSeparator ]
CatchBracedArms := CatchArm { CatchArmSeparator CatchArm } [ CatchArmSeparator ]
CaseArm := ArmPattern [ CaseGuard ] Arrow ArmBody [ Semicolon ]
CatchArm := ArmPattern [ Comma ArmPattern ] [ CatchGuard ] Arrow ArmBody [ Semicolon ]
```

## 5. Recovery CST

An absent block introducer places one zero-width `Missing` in `CaseLike(Block)` with colon expectation.
After Catch has admitted `{`, a missing local close instead uses `CaseLike(Block)` with brace-close expectation.
A same-or-shallower post-colon arm absence uses `CaseLike(Arm)` and leaves the complete following item with the outer owner.
First-arm and Catch-handler pattern recovery use `CaseLike(Pattern)` and `CaseLike(Handler)` through the Pattern owner exactly once.

If an admitted body NUD occurs where the arrow is absent, one `CaseLike(Arrow)` missing node precedes body parsing.
When arrow and body are absent at the same boundary, that one Arrow node carries the ordered Arrow-punctuation and Body-expression expectations; it creates no second `Missing` node.
After an admitted arrow, an absent body uses `CaseLike(Body)`.
A malformed body is one maximal non-empty raw `Error` group in `CaseLike(Body)` and may retry the same slot.

Before a next admitted pattern without an arm comma, one zero-width `CaseLike(Separator)` missing node precedes exactly one same-item retry.
It creates no separator wrapper or separator error scan.
After every Catch arm-sequence exit, `CatchBlock` emits its matching `}` or one local close missing node, leaving every other protected item unconsumed.
Nested pattern, guard, and body recovery is never duplicated by the arm family.

## 6. Source/CST examples

`case: 0 -> 1` has an inline arm without a scrutinee.

```xml
<CaseExpression>
  <CaseKw text="case" />
  <CaseBlock>
    <Colon text=":" /><Whitespace text=" " />
    <CaseArm><Pattern><IntegerPattern><Integer text="0" /></IntegerPattern></Pattern><Whitespace text=" " /><Arrow text="->" /><Whitespace text=" " /><OperatorChain><IntegerLiteral><Integer text="1" /></IntegerLiteral></OperatorChain></CaseArm>
  </CaseBlock>
</CaseExpression>
```

Indented arms use the same `CaseBlock`; the CST of `case n:` is unchanged.

`catch: v -> v` has one inline arm without a target.

```xml
<CatchExpression>
  <CatchKw text="catch" />
  <CatchBlock>
    <Colon text=":" /><Whitespace text=" " />
    <CatchArm><Pattern><IdentifierPattern><Identifier text="v" /></IdentifierPattern></Pattern><Whitespace text=" " /><Arrow text="->" /><Whitespace text=" " /><OperatorChain><IdentifierExpression><Identifier text="v" /></IdentifierExpression></OperatorChain></CatchArm>
  </CatchBlock>
</CatchExpression>
```

With indented arms, `catch:` also keeps handler patterns in their existing slots: `flip::coin(), k -> k true` has two direct `Pattern` children separated by the handler comma inside `CatchArm`.

`case 'go x: 1 if ok -> yes, _ -> no` places its label, scrutinee, two direct arms, and arm separator in source order.

```xml
<CaseExpression>
  <CaseKw text="case" /><Whitespace text=" " />
  <CaseLabel><SigilIdentifier text="'go" /></CaseLabel><Whitespace text=" " />
  <CaseScrutinee><OperatorChain><IdentifierExpression><Identifier text="x" /></IdentifierExpression></OperatorChain></CaseScrutinee>
  <CaseBlock>
    <Colon text=":" /><Whitespace text=" " />
    <CaseArm><Pattern><IntegerPattern><IntegerLiteral text="1" /></IntegerPattern></Pattern><Whitespace text=" " /><CaseGuard><IfKw text="if" /><Whitespace text=" " /><OperatorChain><IdentifierExpression><Identifier text="ok" /></IdentifierExpression></OperatorChain></CaseGuard><Whitespace text=" " /><Arrow text="->" /><Whitespace text=" " /><OperatorChain><IdentifierExpression><Identifier text="yes" /></IdentifierExpression></OperatorChain></CaseArm>
    <CaseArmSeparator><Comma text="," /></CaseArmSeparator><Whitespace text=" " />
    <CaseArm><Pattern><WildcardPattern><Underscore text="_" /></WildcardPattern></Pattern><Whitespace text=" " /><Arrow text="->" /><Whitespace text=" " /><OperatorChain><IdentifierExpression><Identifier text="no" /></IdentifierExpression></OperatorChain></CaseArm>
  </CaseBlock>
</CaseExpression>
```

`catch action { err, handler -> recover; }` gives the handler comma, second pattern, arrow, body, and semicolon to one `CatchArm` inside a direct braced `CatchBlock`.

When a braced Catch block has more than one arm, each arm-list comma is a `CatchArmSeparator`; it is distinct from the handler comma inside a `CatchArm`.

`catch action: err, handler -> recover` is the exactly-one colon-inline Catch arm with its optional second handler pattern.

## 7. Composition

[Dynamic operator chains](operator-chain.md) define primary placement, scrutinees, guards, and inline bodies.
The [pattern reference](../patterns/pattern-core.md) defines arm Pattern grammar and owns nested pattern recovery.
The [layout-aware separator authority](../cross-cutting/layout-aware-separator-authority.md) and shared indented block define current-depth arm and body boundaries.
