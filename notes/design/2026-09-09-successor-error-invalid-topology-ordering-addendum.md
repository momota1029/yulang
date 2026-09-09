# Error-token and Invalid-node topology ordering addendum

Status: Authoritative

Approved-by: user

Approved-at: 2026-09-09

Drafted-by: primary from the reviewed gate-order clarification

Reviewed-by: specification pre-write audit

Date: 2026-09-09

Scope: ordering only for the direct Rowan Error-token and Invalid-node CST
topology migration. This narrowly clarifies the construction order between the
direct-Rowan amendment and the later CST-derived-diagnostics amendment.

## Decision

Before the complete per-slot diagnostic schema is published, the parser may
perform one topology-only migration:

1. every ordinary raw malformed physical fragment is emitted as an `Error`
   token leaf in its existing owner slot, with no structural Error wrapper;
2. only the two existing structured recovery owners, polymorphic-variant
   tag-name recovery and record-pattern wrong-kind item/separator recovery,
   emit an `Invalid` node that retains their nested syntax;
3. `Invalid` is appended to `SyntaxKind` without renumbering any existing
   kind.

During this topology-only gate, existing parser recovery records, structured
reservations, frozen-header reconciliation, diagnostic IDs, public diagnostic
construction and their temporary retry-leading extents remain unchanged. They
are temporary compatibility machinery, not new CST authority. The gate does
not authorize a CST diagnostic interpreter, a `ParsedFile` API change, header
diagnostic removal, a new diagnostic ordering, or retirement of any record
field.

Every physical fragment emitted by raw-recovery mode uses the Error token kind,
including interior trivia, Yumark quote prefixes, same-line EOF leading and
both existing consumed retry-leading prefixes. Leading already emitted by an
owner, and retry/boundary leading left for a successor, remain outside raw
Error tokens. Accepted/trivia emission retains its native token kinds.

Test assertions about one structural Error node or native token kinds inside
that wrapper are changed only to the approved Error-token/Invalid topology.
They continue to prove exact source spelling and order, recovery continuation,
record facts and protected leading. No assertion may replace a node count with
an Error-token count without identifying the relevant raw-token group or
Invalid containment.

## Narrow supersession

This addendum supersedes only the phrase "before implementation" in
`2026-09-09-successor-cst-derived-diagnostics-amendment-draft.md` **Narrow
supersession** and Construction/proof gate 1, where that phrase would prohibit
this topology-only migration. The complete independently audited per-slot
schema remains mandatory before the parser diagnostic ledger or public
diagnostic API is removed. All other gates and rollback conditions remain in
force.

## Verification

Use M2 focused checks for raw recovery output, both structured owners,
UTF-8/CRLF/foreign-prefix fragments, consumed and protected leading, nested
Invalid with valid nested syntax and nested recovery, accepted controls,
normalization and public boundaries. Then run one package check, scoped format
and diff checks. The existing `SyntaxKind::Unknown` discriminant failure is
outside this gate; appending `Invalid` must not alter it.
