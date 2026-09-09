# TypeCall post-argument residual close recovery

Status: Authoritative; private construction pending

Date: 2026-09-10

Approved-by: user, selecting policy A

## Scope and supersession

This amendment resolves the reachable `T(A@)` contradiction recorded by the
TypeCall close-slot structural-boundary amendment. It supersedes only that
amendment's construction-gate stop condition for Call's residual post-argument
fallback. The `TypeCallClose` node decision, all existing recognized dispatch
paths, accepted grammar, argument/separator ownership, protected-boundary
handoff, direct-Rowan rules and CST-derived diagnostic destination remain in
force.

Scope is the final unclassified Item after an admitted TypeCall argument. It
does not apply before an argument, to separators, to an admitted next argument,
to matching/mismatched close dispatch already selected, or to another
delimited owner. It adds no `Invalid`, Error relexing, parser ledger, parser
state, replay or generic recovery API.

## Selected policy

After all existing Call post-argument dispatch has declined an Item, that
unprotected residual enters irreversible terminal close recovery. It and every
following nonboundary Item are raw `TypeCallClose` Error content until matching
`)` or the existing EOF/protected-boundary exit. The close slot then completes
normally or hands its protected Item out unchanged.

```text
T(A@)  => TypeCallTail(LParen TypeExpression("A")
                       TypeCallClose(Error("@") RParen))
T(A@B) => TypeCallTail(LParen TypeExpression("A")
                       TypeCallClose(Error("@") Error("B") RParen))
```

The close diagnostic projects `Close(Parenthesis)` from the maximal adjacent
Error group under `TypeCallClose`. Native trivia terminates a group. No
separator Missing or CallArgument Error is fabricated for the residual;
recovering a further argument is expressly not selected. This prioritizes
completion of the committed Call over interpreting later text as a possible
argument.

Existing priority remains exact: matching close, protected caller/outer/fence
boundary, explicit separator, pipe-special handling, implicit layout
continuation and admitted inherited-ML argument dispatch all run before this
residual rule. Thus accepted argument/separator paths do not change. Initial
and retry leading follow the established close-recovery owner rules; protected
leading remains pending. EOF and protected exits retain exactly one terminal
close Missing after close Error; duplicate close-Missing publication remains
forbidden.

## Construction and evidence

`type_expr::delimited` owns the one residual dispatch into its existing
terminal TypeCall close-recovery procedure. `TypeCallClose` opens once around
that complete procedure; no special case by payload spelling or caller is
permitted.

Direct Rowan evidence must pin `T(A@)`, `T(A@B)`, `T(A@,B)`, comments and
UTF-8; matching close and EOF/protected-boundary exits; LF/CRLF; caller and
outer boundaries; quoted fences; and accepted/separator/inherited-ML controls.
It must prove Error grouping, source conservation, exact pending Item/origin/
line/remainder, one final close node and preserved external tails after a
closed Call. Existing direct fallback evidence remains a before-state witness
and must be replaced only by this approved behavior.

Use one bounded implementation pass, focused tests, package check, format and
diff. Compiler/recovery and specification review cover the changed owner and
ordered CST schema. Benchmark budget is zero samples/processes: the rule
reuses the existing close scan and adds no accepted-input work, replay or
allocation beyond the approved close node.
