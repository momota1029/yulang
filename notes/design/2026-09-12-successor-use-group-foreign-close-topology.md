# Use group foreign-close CST topology

Status: Authoritative; private construction pending

Date: 2026-09-12

Approved-by: user

Approved-at: 2026-09-12

Drafted-by: primary from the UseDeclaration CST collision investigation and
the user's selection of option A

Reviewed-by: specification and compiler/recovery pre-write audits

Scope: one transparent Rowan topology distinction for the existing locally
consumed mismatched-close branch in `declaration::use_decl::parse_group`. It
covers `UseGroup` and both brace- and parenthesis-opened `UseExclusionGroup`
callers of that shared owner. It does not change accepted use grammar, import
projection, group phase, current-Item continuation, source/leading ownership,
temporary recovery records, `OperatorName` close recovery, public diagnostics,
the CST interpreter/API migration or recovery-ledger retirement.

Supersedes: the Error/Invalid topology-ordering addendum's direct raw-placement
rule only for Error emitted by this locally consumed Use-group foreign-close
branch. Every other raw malformed fragment remains in its current direct owner
slot.

Governing authority: the Authoritative CST-derived diagnostics amendment and
Error/Invalid topology-ordering addendum. This record resolves the owner-schema
gap found while cataloging the current UseDeclaration recovery leaves.

## Proven collision

The current parser gives these complete inputs the same direct kinds and ranges:

```text
use {)} -> UseGroup(LBrace@4..5, Error-token@5..6, RBrace@6..7)
use {@} -> UseGroup(LBrace@4..5, Error-token@5..6, RBrace@6..7)
```

The first Error is the locally consumed foreign close and currently publishes
`ClosingDelimiter(ImportGroup, Brace)` with expected `Close(Brace)`. The second
is the group-entry raw run and publishes `Declaration(Import(GroupEntry))` with
expected `Path`. A CST walker may not inspect `)` versus `@` spelling or retain
parser phase, so the two documented slots cannot be derived from this tree.

The same shared `parse_group` branch serves brace-opened `UseGroup` and
brace- or parenthesis-opened `UseExclusionGroup`. For `UseExclusionGroup`, its
direct opener distinguishes the required local delimiter even though the node
kind is shared.

## Approved topology

Add one transparent node:

```text
UseGroupForeignClose := Error+
```

Only `declaration::use_decl::parse_group` emits it, immediately around the
unchanged `error_item` call in the existing mismatched-close branch, after the
outer-close protection check. It is emitted once for each locally consumed
unclaimed `RParen` or `RBrace` which does not match that group's selected local
close. The existing `mismatched_close` predicate remains the admission rule;
this gate does not add `RBracket` or any new close classification.

The ordered grammar skeleton becomes:

```text
UseGroup := LBrace
  (NativeTrivia | Comma | UseTree | Missing(GroupEntry)
   | Error+(GroupEntry) | UseGroupForeignClose)*
  (RBrace | Missing(Close))

UseExclusionGroup := (LParen | LBrace)
  (NativeTrivia | Comma | UseTree | Missing(GroupEntry)
   | Error+(GroupEntry) | UseGroupForeignClose)*
  (RParen | RBrace | Missing(Close))
```

For `UseExclusionGroup`, the accepted direct opener fixes whether its local
close expectation is Parenthesis or Brace. The Error-token group inside
`UseGroupForeignClose` projects the existing
`ClosingDelimiter(ImportGroup, <opener delimiter>)` occurrence with singleton
expected `Close(<opener delimiter>)`, primary alternative zero. The wrapper
itself projects no diagnostic. Direct raw Error groups retain the existing
GroupEntry/Path slot selected by ordered group context.

The wrapper has exactly the combined UTF-8 range of its nonempty Error-token
children. Initial leading is already emitted by `parse_group` before the
mismatched-close decision and remains direct native group content. The wrapper
contains no native trivia, Missing, Invalid, accepted punctuation, UseTree,
returned Item, retry leading or outer-owned source. Consecutive foreign closes
produce distinct wrappers because each is one existing consumed Item
occurrence; one direct group-entry lexical run remains one adjacent Error-token
group.

The XML-like notation is:

```xml
<UseGroup>
  <LBrace text="{"/>
  <UseGroupForeignClose><Error text=")"/></UseGroupForeignClose>
  <RBrace text="}"/>
</UseGroup>
```

For `use {@}`, the `Error` token remains a direct `UseGroup` child. For an
outer close borrowed by a nested group, the existing local-close Missing and
unchanged Item handoff remain; no foreign-close wrapper is emitted.

The order of admission is intentionally observable in mixed controls.
`use {)@}` produces one foreign-close wrapper followed by one direct GroupEntry
Error group. `use {@)}` stays one direct GroupEntry Error group containing both
physical Error fragments because `recover_group` has already admitted that
maximal run; it does not reconstruct a foreign-close phase from a later token.
`RBracket` remains a negative admission control because the existing
`mismatched_close` predicate does not select it.

## Alternatives not selected

- Collapsing close and GroupEntry into one expectation loses an existing
  individual diagnostic even though the owner can preserve the distinction.
- A uniform node around accepted and missing closes changes normal CST ancestry
  and adds topology outside the demonstrated ambiguity.
- `Invalid(Error+)` would add a structured-recovery diagnostic and broaden the
  established meaning of `Invalid`.
- Error spelling, expected attributes, parser provenance or another side table
  would recreate the parallel state the CST-only architecture removes.
- Reusing a sibling family's foreign-close kind would hide the Use grammar
  owner and make the schema depend on unrelated parser implementation sharing.

## Construction gate

The user's 2026-09-12 selection of option A approves the transparent
`UseGroupForeignClose` node, its two immediate group owner kinds, opener-selected
delimiter, one-wrapper-per-consumed-close cardinality, and this narrow direct
raw-placement supersession. Independent pre-write specification and
compiler/recovery audits must close before production implementation.

Both required pre-write audits closed without findings. They confirmed all five
shared call sites, opener-selected delimiter ownership, outer-close/caller-stop
priority, one-Item Error emission, unchanged projection/records/handoff and the
constant malformed-only Rowan cost. No further user decision is required inside
this scope.

Use M2: append one SyntaxKind without renumbering existing values; change only
the existing mismatched-close emission site; add focused Rowan and unchanged
record/frozen controls for the collision, both UseExclusionGroup openers,
repeated/mixed Error groups, source flattening, wrapper range/cardinality,
leading, nested outer-close protection and accepted groups. Run the focused Use
and SyntaxKind tests, one package check, scoped format and diff, then one closure
review and at most one batched repair.

The accepted path gains no parser branch, traversal or allocation. The malformed
foreign-close path gains one Rowan start/finish pair around source already
emitted. Static complexity remains `O(bytes + structural work)`; benchmark
budget is zero samples/processes unless implementation exposes material
uncertainty.

Stop if accepted syntax or source ownership changes, a wrapper spans more than
one consumed close, an outer/protected close is consumed, records/ranges/handoff
change, any existing SyntaxKind value moves, or another owner would need this
node.

## Implementation status

Pending the required pre-write audits and private construction.
