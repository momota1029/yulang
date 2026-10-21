# R278 — Yulang2 dotted Binding target syntax addendum

Status: implementation addendum for the user-authorized unchanged Yulang2
playground source scope. This does not define method lookup or runtime
semantics. R149 and every proof/production gate remain as recorded.

## Evidence and compatibility boundary

The R149 pinned `lib/std/core/fmt.yu` contains both required role signatures
such as `pub a.show: str` and implementation members such as
`our value.show = ...`. The Yulang2 oracle represents these Binding targets as
an identifier Pattern followed by a `Field(DotField)` continuation. The
Yulang3 Chasa design deliberately kept this continuation out of Pattern and
records it as a separate deferred feature. The R277 exact-source census shows
the role and implementation target rows among root-level parser error groups.
R149's unchanged-source requirement supplies the missing compatibility scope
for these target forms.

## Grammar and CST

Extend ordinary Pattern syntax with this continuation:

```text
DottedPattern := IdentifierPattern (AdjacentDot Identifier)*
AdjacentDot   := Dot token with no trivia before it
Identifier    := one ordinary identifier token with no trivia after the dot
```

The tree is lossless and Yulang3-native: each continuation is a
`PatternFieldTail` node containing the actual `Dot` token and member
`Identifier` token. It is a direct child of the containing `Pattern`, in
source order. Chaining repeats the same constructor. Existing
`PatternPathTail` continues to own `::`; expression `FieldTail` continues to
own expression receiver projection. These constructors are not interchangeable.

An identifier is required on the right. If it is absent, recovery stays under
the one `PatternFieldTail` owner and leaves the caller's active separator,
close, dedent, or next statement available. A dot with preceding whitespace,
`..`, numeric/member punctuation, and a bare `.` do not form a dotted Pattern.
The feature adds syntax structure only: it does not determine whether a
Binding is a role signature, default method, implementation, or ordinary
binding, and it does not resolve the receiver or member.

## Preservation obligations

- Existing identifier, constructor path, call-pattern, alias, alternation,
  annotation, and ML-application patterns keep their prior ownership/order.
- Dotted continuations are accepted only after an identifier primary and
  adjacent source punctuation; all actual bytes and trivia remain in order.
- A malformed member consumes/reports only its own bounded continuation and
  cannot steal binding `:`, `=`, comma, body close, or following statement.
- `a.b` inside an expression continues to use expression `FieldTail` unchanged.
- The exact pinned library source stays byte-identical. Parsing target rows does
  not imply that all `fmt.yu` syntax is supported.

The open R149 and Simple-sub/evaluator proof obligations are unchanged. This
addendum authorizes no implementation or runtime behavior for the field name.
