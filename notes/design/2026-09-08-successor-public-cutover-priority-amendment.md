# Successor public cutover priority

Status: Authoritative; construction pending

Date: 2026-09-08

Approved-by: user's current explicit instruction to prioritize connecting the
successor entrypoints and removing the old parser once sufficient validation
functionality exists, without completing every private successor owner first.

## Supersession and retained requirements

This amendment supersedes the prior execution ordering that treated exhaustive
private O3/O4 owner completion as an automatic prerequisite for public cutover.
It does not authorize a fallback parser, source replay, a second production
authority, weakened accepted syntax/losslessness, or weakened header/frozen
diagnostic identity. Deferred owner rows remain open and are not represented as
completed merely to reach cutover.

The public authority must be exactly one successor path: `scan_header` and
`parse_file` must use rewrite-owned header/root construction. The legacy parser
may be removed only after those paths are exercised by public integration tests
and no production `grammar::` parser caller remains.

## Required construction order

1. Add rewrite-owned header discovery that produces the public `HeaderInfo`
   facts and ranges required to compile the full operator table.
2. Add rewrite-owned root construction that owns Root topology, top-level
   statement progression, trivia/layout/separators, pending/end exits and
   committed recovery records.
3. Connect `scan_header`, then `parse_file`, without fallback to grammar.
   Preserve `compile_full_parse_operators_recovering`, public API shape and
   recovery-before-construction diagnostic order.
4. Validate actual `scan_header -> parse_file` operation, including header
   record reconciliation and operator facts, before deleting legacy parser
   modules and their direct-root/header tests.

## Minimum public proof before removal

The successor public path must prove lossless accepted declarations/expressions,
multiple root statements and layout, source-leading imports and operator
headers, local/imported operator conflicts, malformed header followed by valid
header identity, header/full frozen ID reconciliation, UTF-8/CRLF/fence
boundaries, and Yumark recovery/frame-pop/following-literal continuation where
the public surface reaches it. Differential legacy output may guide temporary
construction but is not final authority.

Run the designated public cutover suite, then a final `yu-syntax` test suite
and workspace check only after the successor entry has no fallback. Deletion is
atomic with the public switch: remove obsolete production `grammar::` parser
entrypoints, legacy-only parser modules/tests and unreachable adapters; retain
   only shared non-parser facilities proven caller-free or migrated.

## Selected entry foundations

`HeaderInfo` retains its originating `Arc<SourceText>` privately. `parse_file`
requires `Arc::ptr_eq` between the supplied source and that retained source
before operator construction or recovery reconciliation. Current supported
callers already retain the same allocation through `Arc::clone`; this preserves
the public API shape while rejecting distinct equal-text snapshots. Content
equality, hash identity and silent same-length acceptance are rejected because
they cannot prove the required header/source relationship. A future query-layer
revision may replace this private allocation identity without altering the
public entry contract.

Header records are not generally a prefix of full-root recoveries: an
operator-body/root recovery can occur before a later shared header record.
Output therefore owns a scoped reconciliation mode. Only rewrite's shared
leading-header publication consumes the frozen cursor. Full-only body/root
records allocate IDs above the frozen maximum while one encounter-ordered vector
is retained. Scope exit restores ordinary publication on every exit. This is a
narrow correction to the old prefix assumption; it adds no lookup, sort,
deduplication or second parser authority.

## Current fact and next gate

At this amendment, `scan_header` calls `grammar::header::discover_header` and
`parse_file` calls `grammar::declaration::parse_direct_root_candidate`. Rewrite
has neither a public header entry nor a multi-statement root loop. Therefore
connecting either current private owner directly is unsound. The immediate gate
is the bounded rewrite header/root entry design and construction, not further
isolated declaration-tail migration.
