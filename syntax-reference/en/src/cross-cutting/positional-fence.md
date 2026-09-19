# TypeExpression malformed caller-boundary fence

## Scope

This rule preserves a caller-owned newline selected by TMN while nested
TypeExpression recovery unwinds. It applies only after TMN has classified an
untouched maximal trivia run as a caller boundary. It is not source syntax,
an additional type form, or a new recovery node.

## Boundary preservation rule

Once TMN returns a caller boundary, the exact start of its untouched trivia is
fenced. While parsing remains at that position, a nested TypeExpression owner
must not consume the trivia, classify past it, or consume a local close. The
enclosing caller receives the whole trivia run and its following boundary.

Ordinary multiline layout does not create a fence. A newline is protected only
when TMN has already selected caller ownership. This keeps normal local
sequence boundaries distinct from malformed-recovery handoff.

## Source order in the Rowan CST

The fence creates no source-bearing leaf, structural node, or `Missing` node.
It preserves existing source order: the malformed `Error` token ends before
the fenced trivia, and the caller later owns that trivia and its boundary.

If a fenced boundary leaves an accepted delimited construct unclosed, that
construct retains its documented zero-width `Missing` for its own close slot.
Nested accepted constructs do not share one close recovery: each unclosed
instance realizes its own close slot once.

## Recovery and handoff

The fence does not change the malformed `Error` range or convert a handoff
into a retry. It prevents a nested owner from consuming the protected gap and
then lets the caller make the next boundary decision. A single construct
instance must not create duplicate close `Missing` nodes for the same gap;
separate nested instances remain separate recovery owners.

If the recovery branch is abandoned, the fence is abandoned with it. It has no
effect after the caller consumes the named trivia.

## Examples

| Source | Result |
| --- | --- |
| `T((@ \n  A))` under a caller-owned newline | The inner `ParenthesizedTypeGroup` and outer `TypeCall`/`Call` are separate close owners and each retain one missing close. The newline and `A` remain caller-owned. |
| `{@ \n  a: A}` under a caller-owned newline | The malformed field has its `Error`; the unclosed NamedRecord retains one missing close; the run remains caller-owned. |
| `A::@ \n  B` without a caller-owned newline | No fence is created. TMN retries `B` after the deeper trivia. |
| `T(A\n  B)` | No malformed recovery occurred, so no fence is created and ordinary layout handling applies. |

## Composition and limits

TMN alone decides whether a malformed newline is caller-owned. The fence
preserves that result across nested TypeExpressions; it does not replace
delimiter, stop, or layout rules. See [TMN](tmn-malformed-newline-owner-policy.md)
for the classification and [recovery topology](../conventions/recovery-error-invalid-topology.md)
for `Error` and `Missing`.

The governing source is the Authoritative *TypeExpression malformed caller
boundary positional fence* in
`notes/design/2026-08-20-yu-syntax-chasa-architecture.md`,
lines 16862–17289.
