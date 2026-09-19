# ASOB participation and precedence

This page shows where [ASOB](ambient-statement-owner-boundary.md) participates.
It is a syntax-v0 ownership reference, not an implementation record.

## Participation

ASOB is consulted only after a completed or recovered local anchor and before
that anchor's gap can become local continuation, retry, or an implicit
separator. It does not run for an opener's first item, a next item already
opened by an explicit separator, a local matching close, or an ordinary
mandatory right-hand side already opened by accepted syntax. The `IfExpression`
condition, `forall` bounded phases, and `BR-H`/`BR-A` are the enumerated
mandatory-phase exceptions.

| Construct family | Participating boundary |
| --- | --- |
| Operator chains and fixed tails | A continuation gap before a tail, ML argument, or terminal tail is attached. |
| Expression-delimited forms | A completed or recovered item gap in parenthesized, call, index, and projection forms. |
| If expressions | The condition's enumerated mandatory-phase judge point. |
| Patterns | A Pattern continuation gap and a completed or recovered gap in parenthesized, list, and record patterns. |
| Struct and NamedRecord type fields | A field continuation, retry, or inter-field gap. |
| Type expressions | A path, call, application, arrow, malformed continuation, or delimited type-item gap. |
| Polymorphic variants and bracket rows | A completed or recovered tag, payload, continuation, or designated bounded phase gap. |
| `forall` and inline colon arguments | The designated bounded phase transition or the colon argument decision after its first argument. |

## Precedence at a participating gap

The local close and explicit separator take priority. ASOB then takes a strict
dedent or visible `else`/`elsif` companion. Only when neither applies does the
construct use its ordinary local continuation, layout, or recovery rule.

If ASOB takes the gap, it remains unconsumed for the ambient owner. If a local
implicit boundary has already been committed, its one next slot remains local;
ASOB applies only at the later gap.

## Non-participating boundaries

ASOB does not claim the following boundaries:

- An ordinary same-indent statement candidate after a missing inner close.
- A braced statement-owner boundary at the current brace depth.
- A case or catch arm-sequence boundary.
- A contextual stop other than an `IfExpression` companion, including arm
  `if` or `where`, `->`, and binding `=` behind a missing nested delimiter.

These remain outside ASOB. Their ownership follows their construct pages and
existing recovery contracts.

## Related rules

Use [layout-aware separator authority](layout-aware-separator-authority.md)
to classify a local complete-item newline. Use [TMN](tmn-malformed-newline-owner-policy.md)
for malformed TypeExpression newline ownership. ASOB only decides whether its
two ambient statement-context claims preempt a participating local gap.

The governing source is the Authoritative ASOB addendum in the
`notes/design/2026-08-20-yu-syntax-chasa-architecture.md`,
lines 18358–19160.
