# Source root, headers, and diagnostic ownership

This page defines the approved target for source-root, header, and diagnostic
ownership. Direct Rowan construction, header discovery/selection, and the
`Error`-token and `Invalid`-node topology are implemented. The later
CST-derived diagnostic migration remains pending.

## Source root

`Root` is the containing node for a complete source CST. Its source-bearing
descendants preserve the source in order. The root schema does not invent a
second tree for headers, recovery facts, or diagnostics.

Construct schemas define the ordered child grammar below `Root`. This page
does not infer any construct-specific child list from the root node alone.

## Header selection

Implemented header discovery precedes full parsing because operator syntax must
be selected before the rest of the source is parsed. It retains source identity,
coverage, imports, and complete local operator facts needed for that selection.

The current full parse compiles those facts with the supplied syntax environment
into the table used to parse the root. It still publishes parser-produced
recovery and conflict diagnostics.

In the pending target, the full-parse planner returns one effective operator
table. Imported capabilities precede local header declarations in source order,
and the existing first-capability-wins rule selects the accepted site. The
selected syntax environment and effective table remain available with the
parsed CST because they are syntax inputs for analysis. They are not a second
syntax tree or a recovery ledger.

In that target, header discovery may use a temporary tree with opaque bodies,
but it publishes no header recovery diagnostics. Full-CST analysis is the only
syntax-diagnostic publication path. Header and full parses do not reconcile or
compare diagnostic streams.

## CST-derived diagnostic ownership

The completed topology-only migration changed only CST shape. It records raw malformed
source with `Error` tokens and uses `Invalid` only for the approved structured
owners. Existing parser recovery records, frozen-header reconciliation, and
published diagnostics remain as temporary compatibility machinery.

In the later CST-derived diagnostic target, the parser records structural
recovery in `Missing`, `Error`, and `Invalid`.
The syntax-schema interpreter derives structural diagnostics while a frontend
walks the red CST. Until a frontend/type traversal exists, a whole-tree
collector performs that same interpretation for tools and tests.

A grammar slot identifies an ordered child position and any ancestor context
needed to interpret it. A parent kind alone is not a slot identity. Every
recovery-bearing slot must be documented before the parser diagnostic ledger is
removed; this initial slice deliberately does not assign individual slots.

The interpreter visits source order.

- Entering `Missing` emits the slot's missing diagnostic at the node's
  zero-width range.
- A maximal adjacent sequence of `Error` tokens in one slot and immediate
  parent emits one malformed-input diagnostic over the combined range. Ordinary
  trivia, `Missing`, a nested node, or a slot boundary ends the sequence.
- Entering `Invalid` emits its structured-recovery diagnostic over
  `Invalid.text_range()` before visiting its children. An `Invalid` node is not
  transparent: it can contain valid nested syntax and still require an outer
  diagnostic.

Equal ranges are ordered by documented slot order and occurrence ordinal. A
diagnostic identity is local to one snapshot: tree occurrence path, grammar
slot, diagnostic kind, and ordinal. Ranges are UTF-8 byte ranges; diagnostic
identities are not promised to remain stable across source revisions.

The target public result is one ordered sequence from this traversal, rather
than a diagnostic array on `ParsedFile`. Expected alternatives and primary
alternatives are schema constants. Raw malformed spelling remains in the CST
token group or its source range, not in a parallel parser record.

## Environment diagnostics

In the pending target, the selected effective table also supports environment
diagnostics. On entry to each complete local `OperatorHeader` occurrence, the
same CST analysis compares that occurrence with the accepted capability site
for the same spelling and fixity. A different site that already won emits a
conflicting-operator diagnostic at the `OperatorHeader` occurrence before any
child recovery diagnostics. The traversal then continues through its children
in source order. Equal declarations also compare as conflicts; the test is not
a binding-power comparison alone.

An environment diagnostic must not write `Invalid` into the CST. A change that
only changes capability provenance can reuse the CST and rerun analysis. A
change to the effective table can change parsing, so identical source text is
not promised an identical CST in that case. The initial safe reuse unit is a
whole source revision and its effective syntax-table identity.

## Current and pending publication

The current implementation publishes parser-produced recovery diagnostics while
the completed topology-only migration emits `Error` tokens and restricted
`Invalid` nodes. A later target removes the parser ledger and derives both
structural recovery diagnostics and environment conflict diagnostics during the
single CST walk described above. The remaining per-slot schema audit and
implementation migration are required before that later target replaces current
publication.
