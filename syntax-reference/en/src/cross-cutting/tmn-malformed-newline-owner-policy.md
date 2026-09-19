# TypeExpression malformed-newline owner policy (TMN)

## Scope

TMN assigns a physical newline after a nonempty malformed TypeExpression
prefix. It applies to required type slots, path segments, arrow right-hand
sides, delimited type items owned by `Call`, `Parenthesized`, or `EffectRow`,
`forall` phases, and NamedRecord type fields. The policy also defines the
explicit handoff used by polymorphic variants and an incomplete NamedRecord
field-name phase.

TMN does not change accepted TypeExpression grammar, type precedence,
delimiter ownership, or diagnostic wording. It classifies recovery trivia
only. `BracketRow` retains `BracketRowAlignmentPolicy` and `BR-RP1`; it does
not use generic TMN.

## Newline ownership

Each continuation-qualified recovery slot captures its continuation base when
the slot begins. A newline continues that slot only when the indentation after
its last physical newline is deeper than that captured base.

```text
continues_after_newline(trivia, base) :=
    trivia contains a physical newline
    and following-line indentation > base
```

An active caller newline takes priority over every TMN policy and indentation
comparison. Otherwise, continuation-qualified slots treat an equal-or-shallower
newline as an owner boundary and a deeper newline as same-slot continuation.
The explicit any-physical handoff policy returns on any physical newline. It
applies where the inner phase cannot safely decide what follows, including the
polymorphic-variant recovery described by its construct page.

The outer required type entry of a Pattern annotation uses that Pattern's
captured continuation base. Nested type recovery uses the ordinary active type
base.

## Source order in the Rowan CST

TMN adds no source syntax or CST node. A malformed source fragment remains an
`Error` token in its documented grammar slot. When the same slot continues,
the retained trivia occurs once in source order between that `Error` token and
the retried type child. When TMN hands a boundary back, the malformed `Error`
ends before the trivia; the enclosing owner retains the trivia and following
boundary.

`Missing`, `Error`, and `Invalid` use the shared [recovery topology](../conventions/recovery-error-invalid-topology.md).
TMN does not authorize a new structured recovery owner.

## Recovery and handoff

TMN distinguishes these observable outcomes.

| Outcome | Ownership |
| --- | --- |
| Retry at the current position | The valid retry candidate remains unconsumed for the same required slot. |
| Retry after deeper trivia | The same slot consumes the exact trivia once, then retries its candidate. |
| Boundary at the current position | The current byte remains with the owner that recognizes the boundary. |
| Boundary after trivia | The malformed `Error` ends before the trivia; the enclosing owner consumes the trivia and following boundary. |

An any-physical handoff also leaves its newline trivia untouched for the
candidate-complete outer owner. A handoff or boundary must not add a
same-cause `Missing` after the malformed `Error`.

## Examples

| Source | Result |
| --- | --- |
| `x: @\n  Int` | The deeper newline retries `Int` in the same required annotation type slot. The `Error` covers `@` only. |
| `A::@\n  B` | The deeper newline retries `B` as the same path segment. |
| `T(@\n  A)` | The deeper newline retries `A` as the call item; the call owns `)`. |
| `x: @\n  <EOF>` | The `Error` covers `@` only. The outer owner receives the trivia, and no same-cause `Missing` is added. |
| `:{@\n  B}` | The polymorphic-variant inner phase hands off at the physical newline; it does not claim `B` as its own continuation. |

## Composition and limits

TMN supplies the malformed-newline result. The owning construct still decides
its local close, separator, active stop, and recovery slot. A caller-owned
newline preserved through nested TypeExpressions follows the
[positional-fence rule](positional-fence.md). Layout separators for complete
items use [layout-aware separator authority](layout-aware-separator-authority.md),
not TMN.

The governing source is the Authoritative *TypeExpression malformed recovery
newline owner policy* in
`notes/design/2026-08-20-yu-syntax-chasa-architecture.md`,
lines 16557–16860.
