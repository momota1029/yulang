# Successor public cutover priority

Status: Authoritative; public entry construction complete, validation and
legacy removal pending

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

## Selected header and root construction contract

Rewrite's shared Use/operator-header owner is the sole producer of header
facts and its typed records. Discovery and full parsing publish the same owner
records inside the header reconciliation scope; operator body and root records
remain full-only. Import projection remains all-or-none per Use declaration:
append its expanded facts only after the complete declaration projects, discard
that declaration's pending batch on projection failure, and do not treat a
recovery record alone as projection failure. Operator facts commit when fixity,
name, required binding powers and actual `=` are complete; body failure cannot
retract that fact.

Header Missing anchors at remaining-start with no unexpected fact. Header Error
is one nonempty lexical run with an OtherCharacter fact; initial leading belongs
to header, internal leading to Error and retry/boundary leading stays pending.
Existing slot roles and expectations remain specific: Import Path/GroupEntry/
Alias and their closes; OperatorHeader Name/Fixity/LeftBindingPower/
RightBindingPower/DefinitionIntroducer. Fixity remains ordered Prefix/Infix/
Suffix/Nullfix, primary zero.

Operator mandatory slots retain their structural safe points. Missing Name stops
before a first binding power or actual `=`; missing binding-power or Definition
Introducer stops before a body NUD. Each publishes its own Missing while the
downstream Item remains pending. A binding power requires I+ separation from a
completed name or preceding binding power. Actual accepted `=` emits
`SyntaxKind::Equals`; `==` is not a DefinitionIntroducer. These rules preserve
accepted header CST and body handoff independently of successor malformed
topology.

Root owns top-level progression and separators. Top-level expression trailing
input selects existing `Statement(Separator)`, expected StatementSeparator;
declaration trailing input retains its specific existing owner. Its lexical
Error tracks delimiter stack: push openers, pop only matching closes and keep
mismatches nested. At outer depth stop before semicolon or root-layout newline;
inside delimiters neither stops. Literal, Rule and Yumark regions are opaque;
abstract boundary is protected at any depth. Initial leading belongs to Root,
internal leading to Error and terminating boundary leading remains pending.
Root never invokes a grammar parser inside Error.

## Current fact and next gate

Rewrite now owns the public `scan_header` and `parse_file` entries without a
fallback. `HeaderInfo` retains the discovery records privately and full Root
consumes them only through shared header scopes; public pair controls cover
source identity, recovery/conflict order, imported/local conflict provenance,
UTF-8/CRLF and fence recovery/continuation. The accepted Yumark NUD owner is
not yet public; the fence control is recovery/continuation evidence only.
The immediate gate is final `yu-syntax`/workspace validation followed by
atomic removal of the now-unrouted legacy parser tree, not further isolated
declaration-tail migration.
