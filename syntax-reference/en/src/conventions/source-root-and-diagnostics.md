# Source root, headers, and diagnostic ownership

This page defines `syntax-v0` conventions for the complete source CST, header
placement, and diagnostic ownership. It is a reference boundary, not a parser
implementation chronology.

## Authority and scope

The Authoritative *Syntax freeze and vertical-implementation completion-policy
amendment* (2026-09-17) freezes the accepted grammar and direct Rowan topology
as `syntax-v0`. The Authoritative *Rowan CST-only successor amendment* requires
one durable lossless CST. The Authoritative recovery and topology records
define the retained recovery facts.

Construct pages define their own ordered child grammars. This page does not
infer a construct-specific child list from `Root` alone.

## Source root

`Root` contains the complete source CST. Its source-bearing descendants retain
the complete source in order. `Root` does not create a second tree for headers,
recovery facts, or diagnostics.

Root expressions, declarations, and root-only operator definitions occupy the
placements defined by the [syntax content model](syntax-content-model.md).
Nested statement ownership is defined by the owning construct; it does not add
a root-level statement-sequence wrapper.

## Headers and syntax environment

Header constructs retain their source-order placement in the CST. They do not
form a separate header syntax tree. The selected syntax environment and its
effective operator table are syntax inputs associated with the parsed source,
not recovery facts or a second CST.

For operator capability selection, imported capabilities precede local header
declarations in source order. The first accepted capability site wins. On each
complete local `OperatorHeader`, the selected environment compares the same
spelling and fixity with that accepted site. A different site that already won
is a conflict; equal declarations also conflict. Binding power alone does not
trigger that conflict. Environment facts do not add `Invalid` or otherwise
change CST structure.

## Recovery facts and diagnostics

`Missing`, raw `Error`, and structured `Invalid` are the structural recovery
facts in the CST. They preserve recovery structure without making malformed
source an accepted alternative. The recovery topology keeps source ownership,
retry and continuation, caller boundary, and fence handoff unchanged.

Structural recovery interpretation is CST-derived. It preserves source order
and deterministic ordering for equal-range occurrences. Expected alternatives
and primary alternatives are schema facts; an uncataloged recovery occurrence
may use the deterministic generic structural interpretation defined by the
recovery-topology convention.

Environment facts contribute separately to final syntax diagnostics. They must
not mutate the CST. A syntax-environment change can therefore change an
environment diagnostic without adding recovery structure.

See [recovery `Error` and `Invalid` topology](recovery-error-invalid-topology.md)
for recovery structure and [Rowan CST notation](rowan-cst.md) for source and
range conventions.
