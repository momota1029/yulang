# TypeCall close-slot structural boundary

Status: Authoritative; private construction complete

Date: 2026-09-10

Approved-by: user, selecting the structural close-phase node option

## Scope and authority

This amendment resolves the TypeCall close-slot architecture return recorded
on 2026-09-10. It is governed by the CST-derived diagnostics amendment's
single-Rowan-tree requirement and prohibition on opaque Error relexing, the
direct-Rowan amendment, the TypeCall recovery authority, and the current
recovery/boundary contracts. It supersedes no accepted grammar or recovery
continuation rule.

Scope is one new `TypeCallClose` Rowan kind and the terminal close phase of
`TypeCallTail` only. TypeCall arguments, argument recovery and separators;
parenthesized/effect-row close slots; `Invalid` ownership; parser-ledger
retirement; public diagnostic API; and other delimited owners remain outside
this construction.

## Decision

Every constructed `TypeCallTail` whose existing path reaches its terminal
close publication has one final `TypeCallClose` child. It identifies the
closing-parenthesis slot without a parser record, Error-payload relexing or
hidden provenance.

```text
TypeCallTail := LParen <argument/separator children> TypeCallClose
TypeCallClose := NativeTrivia* (Error NativeTrivia*)* (RParen | Missing)
```

The notation elides ordinary direct `TypeCallTail` trivia and does not add an
argument wrapper. `TypeCallClose` contains zero or more raw Error tokens and
exactly one terminal native `RParen` token or zero-width `Missing`. Existing
leading already emitted by opening, argument or separator ownership remains
outside the close node. Remaining leading emitted only after close construction
begins is native inside it. Protected pending leading remains unread.

An unprotected mismatched close irreversibly enters `TypeCallClose`.
Subsequent non-boundary Items remain close Error content until matching `)` or
the existing EOF/protected-boundary exit. Accepted `)` and absent `)` use the
same node. Existing token consumption, Missing anchors, contextual suspension,
successor Item, line entry and fence handoff are unchanged.

Argument Error leaves remain direct `TypeCallTail` children. The node boundary
therefore makes these occurrences structurally distinct:

```text
T(@)   => LParen Error("@") TypeCallClose(RParen)
T(])   => LParen TypeCallClose(Error("]") RParen)
T(@])  => LParen Error("@") TypeCallClose(Error("]") RParen)
T(     => LParen Missing TypeCallClose(Missing)
```

The CST interpreter derives `Close(Parenthesis)` from `TypeCallClose`.
Adjacent close Error leaves under this immediate parent form one group; native
trivia terminates that group. The node boundary prevents grouping with an
argument Error. `TypeCallClose` itself emits no diagnostic.

This deliberately changes accepted TypeCall tree topology by adding one node,
but preserves accepted source, token order, ranges and continuations. Consumers
that relied on a direct `TypeCallTail/RParen` relationship must migrate.

## Construction gate

`type_expr::delimited` owns construction. It must centralize terminal TypeCall
close emission and open `TypeCallClose` exactly once around the complete,
irreversible close phase, not once per Error leaf. Other delimited owners retain
their existing topology. No persistent open-node flag, replay, checkpoint,
second builder or diagnostic metadata is permitted.

Before asserting that every committed TypeCall has this final child, prove the
generic post-child fallback is unreachable for Call. If it is reachable, stop
construction and return that existing close-publication contradiction; do not
manufacture a Missing or broaden this amendment.

## Evidence and verification

Direct Rowan evidence must cover accepted empty/full/nested/trailing-separator
calls; the four distinction witnesses above; argument versus close Error groups;
irreversible close Error; Missing after initial/post-item/post-separator and
retry paths; spaces/comments/LF/CRLF/EOF leading; caller and outer closes;
contextual words; quoted fences; UTF-8; and public Root conservation. It must
prove exact pending Item, origin, line entry and remainder at protected exits.
It must also prove that closed TypeCalls retain external tails.

Run focused TypeCall and direct-CST tests, one package check, format and diff.
Review the terminal-path proof with compiler/recovery and the ordered schema
with specification review. Benchmark budget is zero samples/processes: the
change adds one Rowan node per TypeCall with no scan, replay or allocation path
beyond normal node construction.

## Implementation status

The private construction completed on 2026-09-10. `TypeCallClose` is appended
to the syntax-kind domain and `type_expr::delimited` centralizes every existing
Call terminal token/Missing path plus the complete close-error loop under that
node. The generic residual fallback was found reachable, so its stop condition
is superseded only by the later user-approved residual-policy amendment. Focused
TypeCall controls and a package check passed; compiler/recovery and
specification review closed the bounded delta. Public reference reconstruction,
the complete CST diagnostic interpreter and parser-ledger retirement remain
outside this gate.
