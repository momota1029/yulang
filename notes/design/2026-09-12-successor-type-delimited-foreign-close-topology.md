# Parenthesized/EffectRow foreign-close CST topology

Status: Authoritative; private M2 construction complete

Date: 2026-09-12

Approved-by: user

Approved-at: 2026-09-12

Drafted-by: architect from the P/E CST collision investigation

Reviewed-by: compiler/recovery and specification pre-write audits

Scope: one shared transparent Rowan topology distinction for the existing
locally consumed mismatched-close branch shared by `ParenthesizedTypeGroup`
and `EffectRowType`. It does not change accepted Type grammar, P/E Item or
Separator recovery, close admission, current-Item continuation, source or
leading ownership, boundary protection, temporary recovery records, public
diagnostics, the CST interpreter/API migration or recovery-ledger retirement.

Supersedes: the Error/Invalid topology-ordering addendum's direct raw-placement
rule only for Error emitted by this P/E locally consumed foreign-close branch.
Every other raw malformed fragment retains its current topology.

Governing authority: the Authoritative CST-derived diagnostics amendment and
P/E current-Item recovery. This record resolves the owner-schema gap found
while cataloging their existing Item and Close diagnostics.

## Proven collision

The current direct CST kinds, ranges and order cannot distinguish these pairs:

```text
(@ A)   / (] A)
'[@ A]  / '[) A]
```

In each pair the first source has an Item Error expecting `TypeExpression` and
the second has a locally consumed Close Error expecting the owner's matching
delimiter. Both currently appear as one direct opaque `Error` token followed
by the same native whitespace, retried `TypeExpression` and actual matching
close under the same P/E parent. Error spelling and retained parser phase are
not valid projection inputs.

The other bounded P/E alternatives remain structurally distinguishable:
direct Missing and Error order selects Item, Separator and terminal Close
positions. This gate therefore repairs only the demonstrated foreign-close
collision.

## Approved topology

Add one transparent node:

```text
TypeDelimitedForeignClose := Error+
```

Its immediate parent is only `ParenthesizedTypeGroup` or `EffectRowType`. The
parent determines the existing ClosingDelimiter role and its expected close:
Parenthesis for `ParenthesizedTypeGroup`, Bracket for `EffectRowType`. The
wrapper itself projects no diagnostic. Its one maximal adjacent Error-token
group projects the existing owner-specific Close diagnostic.

The local Rowan shapes become:

```xml
<ParenthesizedTypeGroup>
  <LParen text="("/>
  <TypeDelimitedForeignClose><Error text="]"/></TypeDelimitedForeignClose>
  <Whitespace text=" "/>
  <TypeExpression>...</TypeExpression>
  <RParen text=")"/>
</ParenthesizedTypeGroup>

<EffectRowType>
  <Apostrophe text="'"/>
  <LBracket text="["/>
  <TypeDelimitedForeignClose><Error text=")"/></TypeDelimitedForeignClose>
  <Whitespace text=" "/>
  <TypeExpression>...</TypeExpression>
  <RBracket text="]"/>
</EffectRowType>
```

Only the existing P/E mismatched-close branch may emit the node. Open it
immediately before its unchanged `emit_recovery_error_item` call and close it
immediately after, before successor acquisition and retry. Existing outer and
caller protection checks and initial-leading emission stay before the wrapper.

Each locally consumed unclaimed mismatched close produces one wrapper. Two
successive consumed closes produce two sibling wrappers; Item Error followed
by Close Error, and the reverse order, remain separate direct slots. The
wrapper contains exactly the nonempty Error leaves emitted for that one
consumed Item and has their combined UTF-8 range. It contains no native trivia,
Missing, Invalid, accepted punctuation, TypeExpression, returned Item, retry
leading or protected source.

Matching local closes, protected outer/caller closes and abstract boundaries
retain their existing priority and never create this wrapper. Parenthesized
and EffectRow Item errors remain direct Error groups. Call and BracketRow are
excluded even though they share implementation helpers.

Append `SyntaxKind::TypeDelimitedForeignClose = 283` after the already selected
`UseGroupForeignClose = 282`. Existing discriminants must not move.

## Alternatives not selected

- Separate P and E wrapper kinds duplicate information already supplied by the
  immediate parent.
- Wrapping Item Error broadens a separate malformed-run mechanism and affects
  BracketRow sharing without need.
- Collapsing Item and Close expectations loses an existing individual
  diagnostic.
- `Invalid(Error+)` would invent a structured-recovery diagnostic.
- Error spelling, expected attributes or a side table would recreate parallel
  state forbidden by the CST-only architecture.

## Construction gate

The user's selection of option A approves the shared name, its two-owner
scope, one-wrapper-per-consumed-close cardinality, parent-selected delimiter
and this narrow direct-placement supersession. The independent architecture,
compiler/recovery and specification pre-write audits closed without findings.
No further user decision remains in this scope.

Use M2: append the SyntaxKind, change only the existing P/E local
foreign-close emission site, and add focused direct Rowan evidence for both
collision pairs, repeated and mixed Item/Close runs, exact parent/content/range
and source flattening. Retain controls for leading and retry trivia, matching
close, EOF Missing, protected caller/outer/fence handoff, fresh/shifted/frozen
records, accepted P/E, Call and BracketRow. Run focused P/E and SyntaxKind
tests, one package check, scoped format/diff and one closure review with at most
one batched repair.

The accepted path gains no parser branch, traversal or allocation. The
malformed local-close path gains one Rowan start/finish pair and one node for
source already emitted. Complexity remains `O(bytes + structural work)`.
Benchmark budget is zero samples and zero processes unless implementation
exposes material uncertainty.

Stop if accepted syntax or source ownership changes, a wrapper spans more than
one consumed close, an outer/protected close is consumed, records/ranges or
handoff change, an existing SyntaxKind discriminant moves, or another owner
requires this node.

## Implementation status

Private M2 construction completed on 2026-09-12. The append-only
`TypeDelimitedForeignClose = 283` kind wraps only the existing locally
consumed mismatched-close Error emission in the shared P/E branch. Protection
and leading remain before the wrapper; successor acquisition and retry remain
after it. Call, BracketRow, direct Item Error, records and handoff are
unchanged.

Direct Rowan evidence covers both collision pairs, separated and contiguous
repeated closes, mixed Item/Close order, exact wrapper ancestry/content/range,
UTF-8 trivia, shifted origins and fresh/frozen equality. Malformed Call and
BracketRow, accepted owners, EOF, caller/fence handoff and nested/PV paths fix
the exclusion and cardinality boundaries. P/E tests passed 9/9, SyntaxKind
tests 3/3, and `cargo check -p yu-syntax` passed with three pre-existing
warnings in untouched responsibilities. Compiler/recovery review was clean;
one regression-review evidence bundle added the central catalog row and the
negative/cardinality controls, then a fresh specification delta audit closed
without findings. Benchmark use was zero samples and zero processes.

The central P/E slot row is catalog-audited. Other Type rows, the global CST
interpreter, public API migration, recovery-ledger retirement and aggregate
certification remain open.
