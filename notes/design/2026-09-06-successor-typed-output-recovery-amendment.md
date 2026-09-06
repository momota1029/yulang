# Successor typed output and recovery amendment

Status: Authoritative

Date: 2026-09-06

Scope: successor committed output, typed recovery publication, exact extents,
rollback, frozen-header reconciliation, and ordered public cutover

Drafted-by: architect

Reviewed-by: compiler_referee, spec_auditor, performance_auditor

Approved-by: user

Approved-at: 2026-09-06

Supersedes: `2026-09-03-yu-syntax-minimal-rewrite-token-transaction-amendment.md`
only for the narrow conflicts declared in §1

## 1. Purpose and authority

This amendment defines the committed typed-recovery output required to certify
the private recursive-descent rewrite and later replace public parser
authority.

It resolves one narrow conflict between two existing Authoritative sources:

- the recursive-descent rewrite plan requires exact committed recovery records,
  diagnostic ordering, rollback evidence, and frozen-header reconciliation;
- the later minimal token-transaction amendment fixes successor state `S` as a
  bare `GreenNodeBuilder` and defers any output wrapper or recovery-range side
  channel to a separately approved contract.

If approved, this document supersedes the minimal token-transaction amendment
only where that document requires `S` to remain a bare builder or forbids an
immediate committed recovery-output owner. It refines rewrite-plan §3.2 so that
diagnostic sequencing belongs to committed `S` only when allocation occurs in
a total committed recovery emission.

All existing grammar, CST, recovery-extent, current-Item, fence, SCC, literal,
and atomic-promotion decisions remain unchanged.

## 2. Decision

The successor has one rewrite-local committed output owner:

```rust
struct RewriteOutput<'frozen> {
    builder: GreenNodeBuilder<'static>,
    recoveries: Vec<CommittedRecoveryRecord>,
    diagnostics: DiagnosticSequence<'frozen>,
}
```

`RewriteIn` carries `&mut RewriteOutput` instead of a bare builder:

```rust
type RewriteIn<'parse, 'source, 'local, 'frozen> =
    In<&'source str, &'local mut Recover<'parse>, &'local mut RewriteOutput<'frozen>>;
```

`RewriteOutput` owns exactly one Rowan builder and one ordered recovery vector.
It exposes crate-private forwarding operations for builder checkpoints, node
start/finish, and token emission. It does not implement `Deref` or expose the
builder to grammar modules. The enclosing isolated or root harness alone
constructs and finishes the output.

`Recover` remains operator-only and keeps `Recoverable::Mark = ()`. It does not
gain source text, ranges, a builder, records, an ID allocator, expectations, or
an output reference.

Fallible grammar entries may receive `RewriteIn` and therefore a mutable
reference to this output. Receipt is not permission to emit. Every entry that
can return `None` must be effect-free until it has accepted its owner and
entered a total committed continuation. Returning `None` after any builder,
recovery-vector, frozen-cursor, or next-ID mutation is a contract violation.
O1 audits every fallible entry and source-only optional helper for this rule;
where the rule cannot be established locally, the entry must be split into a
`LexIn` probe and a total output-owning continuation before migration proceeds.

## 3. Recovery representation and diagnostic sequence

The rewrite reuses the existing public/internal recovery representation rather
than introducing a successor-only format:

- `DiagnosticId(u32)`;
- `RecoverySiteKey { role, range }`;
- `RecoveryKind::{Missing, Error}`;
- `UnexpectedSyntax`;
- `SyntaxExpectation`;
- `CommittedRecoveryRecord` with ID, site, kind, unexpected facts, ordered
  expectations, and primary expectation.

During coexistence those types may remain in `session.rs`. Gate 9 may move the
same types mechanically to a neutral `recovery.rs` with temporary re-exports if
zero-caller cleanup requires it. That move is not a semantic gate.

An ID-less `RecoveryDraft` contains every record field except `id`. Construction
validates:

- the expectation union is nonempty;
- the primary index is valid;
- a Missing range is zero-width;
- an Error range is nonempty;
- Error has at least one non-EOF unexpected fact.

`DiagnosticSequence` has two modes:

- `fresh`, beginning at ID zero;
- `reconcile(frozen)`, consuming frozen records in authoritative source order
  and beginning fresh allocation after their highest ID.

The reconcile form borrows the frozen record slice. Its retained state is only
that slice, one monotonically increasing cursor, and checked next-ID state. It
may scan the frozen slice once at construction to validate it and find the
highest ID, but publication compares only the next borrowed record. It performs
no record clone, used-index vector, search, or lookup.

Committed publication is sequential:

1. If a frozen record remains, the draft must match its site, kind, unexpected
   facts, ordered expectations, source flags, and primary expectation exactly.
   The frozen ID is reused and the cursor advances.
2. Otherwise the next checked `u32` ID is allocated.
3. The complete record is appended exactly once to `recoveries`.

Finish fails if a frozen record remains unused. Source-identity mismatch fails
before reconciliation state is constructed. There is no map, fuzzy lookup,
deduplication pass, re-sort, or second publication. Vector order is diagnostic
source order. Recoveries at the same boundary are committed
innermost-to-outermost and receive increasing IDs in that call order.

Header discovery later uses a recovery-only `HeaderRecoveryOutput` with the
same `DiagnosticSequence::fresh()` component. Shared header grammar uses thin
header/full materializers; normal token handling does not branch on an output
mode.

## 4. Committed recovery API

`RecoverySiteSpec { role, expected }` remains the one-expectation convenience.
`RecoveryDraft` is used for exact multi-expectation and source-union sites.

Grammar-facing committed operations are conceptually:

```rust
emit_missing(i, leading, at, draft_without_extent)
emit_error_item(i, item, successor_origin, draft_without_extent)
emit_error_run(i, draft_without_extent, total_committed_body)
commit_recovery(i, complete_draft)
```

Each operation emits the generic `Missing` or `Error` CST node and publishes its
record atomically. After the final migration, grammar owners may not construct
raw recovery nodes directly.

`emit_error_run` accepts only a total lexical or malformed-run body. The body
receives lexical input plus a sealed `ErrorRunOutput`, never `RewriteIn` or
`RewriteOutput`. `ErrorRunOutput` exposes only forward emission of the current
Item or literal segment and explicit append of the corresponding unexpected
fact. It exposes no node-start/finish, diagnostic, recovery, or general builder
operation. The helper itself starts and finishes the one Error node, derives
one final nonempty extent, and publishes the record after the total body
returns. Typed nesting is therefore rejected by the capability boundary, not
by convention or a runtime flag. If an existing Error body cannot be expressed
through that sealed surface, implementation stops and returns to architecture
for an explicit reservation protocol.

The literal cone adds the sixteen slots already named by the literal addendum:

- `StringTerminator`;
- `StringEscapeSimpleTarget`;
- `StringEscapeUnicodeHex`;
- `StringEscapeUnicodeEnd`;
- `StringInterpolationOpenBrace`;
- `StringInterpolationCloseBrace`;
- `RuleBodyCloseBrace`;
- `RuleParenClose`;
- `RuleCaptureRightItem`;
- `RuleFieldName`;
- `RulePathName`;
- `RuleUnexpectedItem`;
- `RuleLiteralTerminator`;
- `RuleLiteralInterpolationCloseBrace`;
- `RuleLazyCaptureName`;
- `RuleLazyCaptureCloseBrace`.

They use `GrammarRole::Literal(LiteralRole)`. The earlier addendum's prose count
of fifteen is corrected to sixteen; the listed names themselves remain the
authority.

Add only these literal expectations:

```rust
ExpectedSyntax::Literal(LiteralExpected)

enum LiteralExpected {
    StringTerminator,
    StringEscapeTarget,
    UnicodeHexDigit,
    RuleItem,
    RuleLiteralTerminator,
}
```

Brace/parenthesis slots reuse exact punctuation expectations. Field, path, and
lazy-capture names reuse `Identifier`. Capture-right and unexpected Rule items
use `RuleItem`. Every other Gate 4–6 site uses its existing authoritative role,
unexpected facts, ordered expectation/source flags, and primary expectation.
There is no universal `TokenKind -> UnexpectedSyntax` inference.

The following table is normative for the literal cone. `LiteralRole` is an
enum containing exactly the sixteen row names. For every row the recovery site
role and the singleton expectation role are
`GrammarRole::Literal(LiteralRole::<slot>)`; the expectation source is exactly
`COMMITTED_RECOVERY_RULE`; the primary index is zero. A Missing uses `at..at`
for both site and expectation range and has an empty unexpected array. An Error
uses the exact physical range emitted inside its Error node for both site and
expectation range and has the unexpected value stated below. No speculative
source flag is added.

| slot | kind and expected syntax | Error unexpected evidence | continuation |
| --- | --- | --- | --- |
| `StringTerminator` | Missing; `Literal(StringTerminator)` | — | return EOF/fence boundary unchanged |
| `StringEscapeSimpleTarget` | Missing; `Literal(StringEscapeTarget)` | — | preserve terminator/EOF/fence sentinel; outer String resumes |
| `StringEscapeUnicodeHex` | Missing or Error; `Literal(UnicodeHexDigit)` | Error is one `Token { range: malformed_run, category: OtherCharacter }` for the maximal nonempty run excluding `}`, terminator, `%`, EOF, and fence | accept a following `}` as unicode end; otherwise preserve sentinel for the unicode-end/String owner |
| `StringEscapeUnicodeEnd` | Missing; `Punctuation(Close(Brace))` | — | preserve terminator/`%`/EOF/fence sentinel; outer String resumes |
| `StringInterpolationOpenBrace` | Missing; `Punctuation(Open(Brace))` | — | finish interpolation and preserve EOF/fence boundary for String terminator |
| `StringInterpolationCloseBrace` | Missing; `Punctuation(Close(Brace))` | — | preserve EOF/fence boundary for String terminator |
| `RuleBodyCloseBrace` | Missing; `Punctuation(Close(Brace))` | — | return EOF/fence/outer close unchanged |
| `RuleParenClose` | Missing; `Punctuation(Close(Parenthesis))` | — | return EOF/fence/outer close unchanged |
| `RuleCaptureRightItem` | Missing; `Literal(RuleItem)` | — | return DSL close/outer boundary unchanged |
| `RuleFieldName` | Missing or Error; `Identifier` | malformed-name Error is one `Token` over the exact one-Item Error range with `rule_item_unexpected_category(item)` | Missing preserves stop/EOF/fence; Error continues the same RuleItem |
| `RulePathName` | Missing or Error; `Identifier` | malformed-name Error is one `Token` over the exact one-Item Error range with `rule_item_unexpected_category(item)` | Missing preserves stop/EOF/fence; Error continues the same RuleItem |
| `RuleUnexpectedItem` | Error; `Literal(RuleItem)` | one `Token` over the exact one-Item Error range with `rule_item_unexpected_category(item)` | continue the same RuleSequence |
| `RuleLiteralTerminator` | Missing; `Literal(RuleLiteralTerminator)` | — | return EOF/fence boundary unchanged |
| `RuleLiteralInterpolationCloseBrace` | Missing; `Punctuation(Close(Brace))` | — | outer quote resumes RuleLiteral; EOF/fence remains pending for its terminator |
| `RuleLazyCaptureName` | Missing; `Identifier` | — | preserve non-`xidc`, quote, EOF, or fence sentinel for RuleLiteral |
| `RuleLazyCaptureCloseBrace` | Missing; `Punctuation(Close(Brace))` | — | preserve EOF/fence boundary for RuleLiteral |

`rule_item_unexpected_category` is Rule-owner vocabulary, not a shared token
inference. It matches the already-owned `TokenKind` and spelling without source
rescan. Add `PunctuationEvidence::Pipe`; this is the only new unexpected
category vocabulary required by the literal cone. The exhaustive mapping is:

- `Identifier`, `SigilIdentifier`, and `Forall` -> `Word`;
- `Integer` -> `DecimalInteger`;
- `Operator`, `DotDot`, and `Unknown` whose owned spelling consists entirely of
  operator-shaped characters -> `OperatorLike`;
- `LParen`/`RParen`, `LBracket`/`RBracket`, and `LBrace`/`RBrace` -> the exact
  `Punctuation(Open/Close(Delimiter))`;
- `Comma`, `Semicolon`, `Dot`, `Arrow`, `Colon`, `Equals`,
  `EffectRowApostrophe`, `PathSeparator`, and `Pipe` -> the matching
  `Punctuation(Comma/Semicolon/Dot/Arrow/Colon/Equals/Apostrophe/ColonColon/Pipe)`;
- `PolymorphicVariantColon` and `PatternSymbolColon` ->
  `Punctuation(Colon)`; and
- every remaining `Unknown` -> `OtherCharacter`.

This covers Rule-local fixed `*`, `+`, `?`, `*?`, and `+?` as
`OperatorLike`, while `|` remains exact Pipe evidence. Caller-owned closes and
fence boundaries never reach this mapping. The malformed-unicode Error
deliberately uses `OtherCharacter` for the whole scanner-owned raw run; it does
not rescan or classify the source.

## 5. Exact source extents

No new recovery range or origin is stored in `Item`. The existing immutable
`PendingFragments::physical` interval remains unchanged as fragment-carrier
validation metadata; recovery derivation must not read it. An `ItemExtent` view
is computed once at a committed recovery site from:

- the already-threaded successor coordinate;
- total owned physical-leading byte length;
- already-emitted leading-prefix byte length;
- owned payload byte length.

For a lexical Item ending at `successor_origin`:

```text
physical_start = successor_origin - (all_leading_bytes + payload_bytes)
leading        = physical_start .. physical_start + all_leading_bytes
remaining      = physical_start + emitted_leading_bytes .. leading.end
payload        = leading.end .. successor_origin
```

Foreign Yumark prefix parts count once as physical leading. Fragment metadata
does not change byte length. EOF insertion uses the successor coordinate. A
pending boundary uses `PendingBoundary::coordinate()` and its inspected fact;
its range is never reconstructed from CST text. A caller-owned boundary stays
unconsumed and cannot become an Error extent.

Detached-leading Missing sites pass an explicit checked insertion coordinate;
the emitter never infers it from builder state.

Extent derivation adds recovery-only linear work over the current Item's trivia
parts and runs once per recovered Item. It introduces no root source, pointer
subtraction to a root slice, new recovery range/origin field on Item, CST/AST
walk, or replay. The retained fragment interval is neither recovery authority
nor an alternate extent input.

## 6. Rollback invariant

Raw source probes receive only `LexIn` where their current boundary permits it.
Existing fallible entries that receive committed `S` remain effect-free before
acceptance: a path returning `None` has not invoked any output method. Recovery
emission is total only after owner commitment. Therefore speculative failure
cannot mutate the builder, recovery vector, frozen cursor, or next diagnostic
ID, and `Recover::Mark` remains unit.

Rollback tests seed output with a prior record/ID, execute a rejected owner,
finish the tree, and compare Rowan output, records, next ID/frozen cursor, input
remainder, and Item identity with a control.

O1 inventories every `Option`-returning procedure that accepts `RewriteIn`; O4
requires an RB witness or an exact effect-free proof for each reachable entry.
If any rejected path must allocate an ID, build a reusable expectation union,
or mutate reconciliation/output state, this amendment fails. The path must be
split into an effect-free probe and total continuation or return to design for
a separately mapped composite `Recover::Mark`; general recovery state must not
be placed in `Recover` by implication.

## 7. Ordered implementation gates

### O0 — authority

Approve this amendment and mark it Authoritative. No code.

### O1 — output shell

Add `rewrite/output.rs`, change `RewriteIn`, and route all builder operations
through forwarding methods while preserving byte-identical CST. Retain clearly
named private node-only recovery helpers temporarily. Do not claim typed
completion.

### O2 — evidence kernel

Add `RecoveryDraft`, `DiagnosticSequence`, `ItemExtent`, typed Missing,
one-Item Error, and Error-run operations, literal vocabulary, and focused
infrastructure tests.

### O3 — prerequisite and one SCC migration

O3a migrates TypeExpression and PolymorphicVariant as the acyclic prerequisite.
After O3a, O3b migrates one mutually recursive SCC containing Pattern,
Expression and its tails/case/if/literal/Rule owners, canonical Statement,
declarations, shared braced/indented/colon/with owners, and
VirtualStatementBlock.

O3b may use internal implementation substeps, but none is an independently
migrated or completed owner. Each procedure remains only a callee until its own
owner-side ledger checkpoint is certified. No procedure calls a legacy parser,
and no expression-private or other private substitute stands in for a later
owner. O3a and O3b are construction checkpoints, not certification claims.

### O4 — zero-untyped and joint Gate 4–6 certification

Remove transitional helpers. Require zero raw recovery constructors outside the
typed output implementation. Close E/P/T/PV/S/D/V/NV, every RB assignment, and
the post-L7 literal deltas together.

### O5 — Gate 7 header/full reconciliation

Add source identity, frozen header records, header recovery output, exact
sequential reconciliation, and isolated public-shaped witnesses.

### O6 — Gate 8 Yumark convergence

Adopt the output in Yumark and close the committed-recovery, frame-pop, then
following-literal ordering evidence.

### O7 — Gate 9 public cutover

Atomically replace public header/root/canonical parser authority and remove
every obsolete legacy parser entrypoint or session adapter once its caller
count is zero. Certification requires no old caller, bridge, fallback, or
duplicated production owner.

## 8. Ledger and verification

Maintain one callsite ledger with columns:

```text
source location | matrix/addendum row | owner/slot | kind | sentinel/run |
range formula | unexpected array | ordered expectations/source flags |
primary | continuation/pending Item | recovery-order predecessor |
focused test | ordinary control | RB row | migration state
```

Every current recovery construction maps to one semantic typed site/helper or
an exact non-recovery proof. O4 requires zero raw recovery constructors outside
the typed output implementation.

O2 infrastructure evidence includes:

- fresh IDs 0/1 and same-offset call ordering;
- exact complete record fields;
- invalid Missing/Error/expectation/primary/overflow rejection;
- UTF-8, CRLF, ordinary and partially emitted leading;
- fragmented Yumark-prefix extent;
- EOF and inspected-boundary anchors;
- one-Item and maximal-run Error;
- malformed Rule field/path evidence for both `.|` (exact Pipe) and `::+`
  (operator-shaped Unknown), plus ordinary non-operator Unknown control;
- rejected branch preserving builder, records, ID, frozen cursor, and Item;
- a capability/API or compile-fail witness that an Error-run body cannot invoke
  recovery or general builder operations.

O4 certification covers every Gate 0 E/P/T/PV/S/D/V/NV cell and subcell,
every RB-E/P/T/PV/S/D/DRV/CMP row, and all sixteen literal slots with ordinary,
at-most-one, boundary-handoff, and innermost-order controls.

O5 covers exact frozen reuse, fresh-after-maximum allocation, mismatch, unused
frozen records, duplicate prevention, and unrelated source identity. O6 covers
the named recovery/frame-pop sequence. O7 covers public losslessness, all
diagnostic fields/order, HeaderInfo facts/ranges, and imported/local operator
conflicts.

Each construction/migration gate runs its owning focused tests, `cargo check -p
yu-syntax`, formatting, and diff checks. O4 runs the complete rewrite ledger
tests plus one `cargo test -p yu-syntax`. O7 runs one `cargo test -p yu-syntax`
and one `cargo check --workspace`. Record-only updates do not repeat broad
suites.

## 9. Performance and review budget

Expected cost:

- valid input allocates no recovery records and retains one Rowan traversal;
  the concrete output forwarding layer is expected to inline;
- recovered input uses amortized `O(records + recovery evidence)` storage and
  `O(Item-leading parts)` extent work once per recovered Item;
- frozen reconciliation is one `O(F)` construction scan followed by `O(1)` per
  committed recovery through a borrowed slice and sequential cursor;
- there is no map, cache, source clone, replay, or additional recursive frame.

M3 pre-approval review uses `compiler_referee`, `spec_auditor`, and
`performance_auditor`, with at most three rounds. O1/O2 use compiler and
performance delta review; O3 uses compiler and specification; O4/O5/O7 use
compiler, specification, and regression review.

Default timing budget is zero after static approval. If wrapper overhead or
valid-path allocation remains materially uncertain, the maximum is one warm-up
plus three paired measurements on one representative large valid root, capped
at eight process invocations and ten minutes.

## 10. Gate 9 and legacy deletion boundary

Gate 9 must replace public root/header authority and remove every obsolete
legacy parser entrypoint or session adapter once its caller count is zero. It
must prove that no old caller, bridge, fallback, or duplicated production owner
remains. Rewrite-plan §6 separately protects the named internal AST/direct
adapters through Gate 9 and requires a later approved deletion plan for them.
This amendment therefore mandates public old-parser replacement and its
obsolete-adapter cleanup, but does not authorize blanket deletion of every
legacy/chasa implementation file.

Complete protected legacy adapter deletion remains a separate future decision.

## 11. Non-goals and failure conditions

This amendment does not authorize:

- a second Rowan builder or event buffer;
- root source storage or a new recovery range/origin field on Items; the
  existing fragment-carrier validation interval is retained but ignored by
  recovery derivation;
- source reread, replay, or CST/AST range reconstruction;
- speculative diagnostic allocation;
- recovery state in `Recover` without a new rollback design;
- fuzzy or out-of-order frozen reconciliation;
- public dispatch before O7;
- deletion at O7 of the specifically protected internal AST/direct adapters.

Return to architecture if an untyped node remains at O4, a caller boundary is
consumed or included in Error, an Error-run contains nested recovery, output
order differs from ID order, valid input allocates recovery storage, or any
required record cannot be derived without a forbidden range/source mechanism.

## 12. Approval requested

Approve replacing the successor's bare-builder `S` with one rewrite-local
composite committed output owning the single builder, ordered
`CommittedRecoveryRecord` publication, and committed-only diagnostic
sequencing; add no recovery range/origin to Items, leave existing fragment
validation metadata unchanged and unused for recovery, and retain
operator-only unit-mark `Recover`; derive ranges immediately from explicit
coordinates and owned Item text; use exact sequential frozen-header
reconciliation; migrate every private recovery site before joint Gate 4–6
certification; preserve Gate 7–9 atomicity; and defer protected legacy
AST/direct-adapter deletion to a separately approved later plan.
