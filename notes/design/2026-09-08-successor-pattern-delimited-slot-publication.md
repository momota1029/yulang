# Pattern delimiter Missing and delegated slot publication

Status: Authoritative; private O3b substep complete

Date: 2026-09-08

Approved-by: user through the ongoing recovery-selection delegation and
continuation direction. Drafted-and-checked-by: primary, without subagents;
this is not independent certification.

Scope: Pattern P5/P6/P7 element, spread, nested-pattern, sequence Missing and
close Missing publication. No accepted grammar, consumed bytes, trivia owner,
completion fact or malformed sequence algorithm changes in this substep.
Record default Expression slots and raw sequence/close Error producers remain
explicitly open, rather than receiving a misleading complete-owner claim.

Authority: the architecture's Pattern/ListPattern/RecordPattern contracts,
layout-aware comma-or-newline correction (separator expectation is
DelimitedSequenceSeparator), the finite matrix P5/P6/P7a–g, and the current
successor typed-output/recovery amendments. The preceding Pattern-primary
amendment continues governing primary Error extents, retry trivia and alias
layout; only its temporary Primary arguments from delimiter callers change
to the established immediate slot roles below.

## Exact publication mapping

| callsite | role | expectation |
| --- | --- | --- |
| parenthesized element Pattern | Pattern::ParenthesizedElement | Pattern |
| ordinary list element Pattern | Pattern::ListItem | Pattern |
| list spread RHS Pattern | Pattern::ListSpreadRhs | Pattern |
| record colon RHS Pattern | Pattern::RecordNestedPattern | Pattern |
| record spread RHS Pattern | Pattern::RecordSpreadRhs | Pattern |
| record fresh comma/empty item | Pattern::RecordItem | Identifier |
| parenthesized/list/record absent separator | respective Pattern::*Separator | DelimitedSequenceSeparator |
| absent `)` / `]` / `}` | ClosingDelimiter of ParenthesizedPattern / ListPattern / RecordPattern with the corresponding delimiter | Punctuation(Close(delimiter)) |

The first five are explicit roles passed to the existing committed Pattern
kernel, for both an absent primary and a nonempty malformed primary run.
Nested accepted owners still publish their own roles; in particular an
alternation RHS remains AlternationRhs, a symbol name remains SymbolName,
and an alias target remains AliasBinding. No record is relabeled afterward.

Missing remains one empty CST node plus one record, no unexpected facts,
one same-role/range expectation with COMMITTED_RECOVERY_RULE and primary
index zero. Use the inspected abstract boundary coordinate, otherwise the
same current Item remaining-start after existing permitted emission. Missing
separator is inserted after its owner has emitted the retry's leading; it
does not consume the retry payload. Missing close is after child records.

Unify the two close-Missing helpers: abstract boundaries and explicitly
carried caller closes retain their whole remaining leading; ordinary EOF
retains the existing owner-emission behavior before anchoring Missing. An
actual same-kind local close still wins before caller-close classification.
This changes no boundary authority or Item frontier.

`record_item` has one caller, guarded by `is_item_start(Record, item)`. Its
spread branch handles DotDot before the ordinary field path, so that remaining
path always has an ordinary/sigil name. Remove the unreachable raw Missing
fallback and express that precondition as a debug assertion. RecordFieldName
has no independent producer here: malformed record heads belong to the outer
sequence's still-open RecordItem Error responsibility. This is an exact
non-recovery proof, not an omitted malformed-source case.

## Pre-write witnesses and limits

Keep existing tests/source literals. Add exact records for `(,a)`, `[,a]`,
`[..]`, `{,a}`, `{a:}`, `{..}`, same-line missing separators, absent closes,
and their accepted empty/trailing-comma/layout/spread/annotation companions.
Use malformed-child retries `(@ x)`, `[@ x]`, `[..@ x]`, `{a:@ x}` and
`{..@ x}` to prove the caller role and preceding amendment's unchanged Error
extent. Include nested symbol/alias/alternation controls to prevent role
overreach. Exercise seeded/frozen/shifted records, actual outer-close
continuation, EOF leading and quoted-fence handoff with complete Item state.

No expected CST text or topology should change in this gate. An assertion
failure outside new metadata must be investigated, not updated automatically.
Malformed sequence and close runs are the next bounded gate. Do not claim
zero raw recovery for `pattern/delimited.rs` until its Error and default
Expression sites are also migrated.

M2 primary-only, one implementation pass and at most two repairs; benchmark
budget zero samples/processes. The mapping and close helper are constant
work per committed slot, with no new valid-path allocation, lookahead, replay
or chasa-recover API. Run focused Pattern tests, the known-small 19-filter
owner/output set, one package check and scoped format/diff checks. Synchronize
the same ledger, task, index and daily record before the coherent commit.
Full SCC, aggregate RB/matrix, actual header/full/Yumark and public cutover
remain open.

## Construction result

All mapped Missing sites are typed, with explicit five-way element/spread/
nested roles passed to the Pattern kernel. The two close helpers are unified
without changing emitted source or pending Item state. The guarded field path
now states its existing name precondition instead of constructing an
unreachable untyped Missing. Four raw sequence/close Error callsites and the
two raw default-Expression Missing callsites remain visible for the next
steps; this is not zero-untyped delimiter completion.

Added seven tests using the preceding seeded/frozen/shifted harness. They
check immediate and nested roles, direct Missing parents, actual outer-close
ownership, innermost-before-close record order, current Item/EOF identity,
owner-emitted EOF leading, quoted-fence coordinates, and accepted layout,
spread, default and duplicate-field controls. No existing expected value or
source literal was changed in this gate.

Validation:

- `cargo test -p yu-syntax --lib rewrite::tests::pattern:: -- --test-threads=1`:
  40 passed, zero failed/ignored; build 33.50s, execution 0.10s.
- `target/debug/deps/yu_syntax-b491637626fa8c73` with the exact 19 filters and
  `--test-threads=1` recorded in the preceding Pattern-primary amendment:
  484 passed, zero failed/ignored, 1.88s execution.
- `cargo check -p yu-syntax`: passed in 6.67s, existing 87 package warnings;
  test builds retain 38 existing warnings.
- `rustfmt --check --edition 2024 crates/yu-syntax/src/rewrite/pattern.rs crates/yu-syntax/src/rewrite/tests/pattern.rs`
  and `git diff --check`: passed, including child modules.

One primary implementation/delta-check pass, zero repairs; no independent
review or broad workspace run. Benchmark usage zero samples/processes. Task,
index, accumulating ledger and daily record are synchronized. Previous
checkpoint `afaa3b24` is pushed; malformed delimiter sequence/close publication
and RecordDefaultExpression remain next, followed by the rest of O3b.
