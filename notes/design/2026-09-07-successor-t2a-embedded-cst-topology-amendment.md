# Successor T2a embedded CST-topology amendment

Status: Authoritative

Date: 2026-09-07

Drafted-by: primary after the user-selected T2 ArrowRhs topology decision

Reviewed-by: M3 compiler/recovery, specification, and regression review; one
batched authority repair and clean delta review on 2026-09-07

Approved-by: user (option 1)

Approved-at: 2026-09-07

User-directed scope: user selected option 1 on 2026-09-07: make the
successor's `Error("@")` plus retry-owned leading space the intentional T2
ArrowRhs CST contract, while retaining the exact recovery record range.

Scope: one named T2 ArrowRhs legacy-to-successor CST ownership delta for
`A ->@ B`, including its mapped embedded literal.  This does not authorize a
general CST-compatibility exception, any other Type/PV owner, PathSegment/T2b,
legacy parser/session changes, Item mutation or splitting, source replay,
Yumark integration before O6, public dispatch, or cutover.

Depends-on:

- `2026-09-02-yu-syntax-recursive-descent-rewrite-plan.md`;
- `2026-09-02-yumark-gate3b-recovery-adoption-matrix.md`;
- `2026-09-05-item-emission-ownership-frontier-amendment.md`;
- `2026-09-06-successor-typed-output-recovery-amendment.md`;
- `2026-09-07-successor-retry-leading-diagnostic-extent-amendment.md`;
- `2026-09-07-successor-t2a-yumark-evidence-timing-correction.md`.

Supersedes: only for the one U+0020 retry-leading byte in local `A ->@ B`
and its mapped `R({type T = A ->@ B})` witness, the following legacy-topology
compatibility requirements: typed-output amendment §1's unchanged-CST clause;
rewrite plan §2(1)'s exact green-tree rule and §5's full-CST acceptance
bullet; item-frontier amendment Scope/§1's no-topology-change application;
retry-leading amendment §1's false legacy-topology premise; and timing
correction Scope/§2's no-CST-relaxation sentence.  The supersession is a
one-cell output delta, not a change to language syntax, AST shape, recovery
identity/range/evidence, diagnostic order, losslessness, Item ownership, or
any other matrix row.  Every other eligible horizontal/comment retry-leading
control retains its existing test role and receives no CST-compatibility or
topology credit without a later explicit decision.

## 1. Observed topology and decision

The now-pinned legacy embedded direct baseline for
`\ref({type T = A ->@ B})` has one ArrowRhs Error recovery record at
`19..21`, but its Error CST node is `"@ "` at `19..21`; `B` begins at
`21..22`.  This disproves the earlier retry-leading amendment's premise that
legacy already keeps the space on the retry Item.

The approved successor construction instead owns the observations as follows.
For local `A ->@ B`:

- Error CST is `"@"` at `4..5`;
- the immediate valid retry Item `B` retains the ordinary space at `5..6` and
  its payload at `6..7`;
- the one ArrowRhs Error record and its one `OtherCharacter` unexpected fact
  are both `4..6`.

In an O3 shifted-origin local successor run, Rowan offsets remain local:
Error is `"@"` at `4..5` and RHS payload is `B` at `6..7`, while the record
and unexpected evidence are global `19..21`.  Arithmetic over the same Item
ownership maps its Error byte to source `19..20`, retry-owned space to
`20..21`, and payload `B` to `21..22`.  Only O6's actual embedded successor
Rowan output has those latter source-relative CST offsets.

The user selects this successor CST topology intentionally for this exact
cell.  It is an explicit green-tree trivia-parentage delta from legacy, made
to preserve the sealed Item-emission frontier: `B` remains one unchanged,
borrowed retry Item.  No byte is dropped, duplicated, rescanned, or moved into
the preceding Error node.  The recovery/diagnostic span is deliberately wider
than the Error CST extent through the already-approved sealed terminal
operation.

## 2. Compatibility boundary and gates

Every T2a ArrowRhs recovery fact remains exact: role Type(ArrowRhs), kind
Error, primary TypeExpression, committed-rule source, primary expectation zero, one
`OtherCharacter` fact over the record range, frozen identity/order, and RB-T.
The Gate3b matrix's ordered embedded AST-fact/direct-record equality remains
unchanged.  Only the legacy Error-node parentage for this retry-leading space
is deliberately different in successor output.

The timing correction remains in force:

- O3a proves the local successor topology and `+15 -> 19..21` record mapping;
- O4 may close only T2a ArrowRhs's local direct/CST/Item/frozen/RB-T subproof;
  the aggregate T2 row and excluded T2b PathSegment remain Open, and the T2
  matrix row receives no credit until O6; and
- O6 runs the real successor-Yumark route, proves matrix fact equality and the
  named successor Error/Item topology, but does not assert legacy Error-node
  CST equality for this one cell.  Matrix §7's fixed frame-pop literal remains
  an independent unchanged control.

At O7 public cutover, the successor `Error("@")` / retry-owned-space topology
is the public green-tree contract for this one cell.  No other legacy CST
difference is implied or accepted.

## 3. Required evidence

Before T2a construction can close under this amendment:

- retain the sealed-capability output tests and all retry-leading amendment
  controls, including no newline/CRLF/carrier/boundary/payload extension;
- prove fresh/frozen local successor Error CST `@` `4..5`, retry-owned space
  `5..6`, RHS payload `6..7`, record/unexpected `4..6`, and exact whole-run
  evidence.  The whitespace token must be outside Error and a descendant of
  the retry RHS TypeExpression that also contains `B`;
- prove the shifted local successor origin `15` run: local Rowan Error `@`
  `4..5`, local RHS payload `6..7`, global record/unexpected `19..21`, and
  arithmetic mapping of Error/space/payload to `19..20`/`20..21`/`21..22`
  without claiming Yumark integration.  Its whitespace parentage must match
  the local successor assertion;
- retain the actual legacy embedded baseline as a distinct control: direct
  Error CST `@ ` `19..21`, direct record/evidence `19..21`, AST structural
  baseline, losslessness, remainder, and frame balance, with no fabricated
  AST fact and no equality assertion over the deliberately superseded CST
  topology.  It must assert that the space is a descendant of Error and that
  `B` begins after that node;
- retain ArrowRhs Missing, non-NUD caller/outer-boundary, and successor-native
  RB-T controls; and
- at O6, prove actual successor-Yumark AST/direct fact equality and
  frame-pop/clean-following behavior while asserting this successor topology:
  embedded Error `@` `19..20`, whitespace `20..21` outside Error and under
  the retry RHS TypeExpression containing `B` at `21..22`; and
- at O7, use the real public route for the mapped literal to prove the full
  lossless successor green hierarchy, the same Error/whitespace/RHS parentage,
  record/evidence `19..21`, and one production authority with no legacy
  caller, old/new crossing, bridge, fallback, or replay.

## 4. Cost, review, and approval

The decision changes only expected CST parentage for one existing malformed
recovery case.  It adds no new traversal, allocation, Item state, source
retention, replay, or valid-input work.  The sealed operation remains
recovery-only `O(L)` in retry-leading parts, with zero timing processes.

M3 compiler/recovery, specification, and regression review must confirm that
the supersession is one-cell, the matrix fact contract remains intact, Item
frontier ownership is preserved, and no sibling receives credit.  The
user-selected topology is not implemented until this reviewed amendment
records approval.
