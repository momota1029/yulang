# Forall current-Item recovery

Status: Authoritative; private Forall-owned construction complete

Date: 2026-09-08

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Drafted-and-checked-by: primary under the user's no-subagent instruction

## Scope and accepted grammar

Complete private `rewrite/type_expr/forall.rs` typed output, simplify its
malformed-run ownership, and remove its superseded source lookahead. Retain
the architecture's Authoritative forall surface (2026-08-23), apostrophe-only
ordered binders with mandatory nonempty bounded trivia, literal colon, full
canonical recursive Type body and terminal-primary disposition. Forall has no
delimiter frame or close role. Type-ML provenance, enclosing separators and
closes, contextual outer boundaries and NUD-versus-TypeApply `for` stay intact.

The Type lexer labels the one-byte colon immediately before `{` as
PolymorphicVariantColon in both ordinary and NUD scanning. At the mandatory
forall colon slot it is still the literal colon: `for 'a:{b:B}` must have a
record body and no recovery. Use a local Colon/PolymorphicVariantColon predicate
only in the head/colon phase. Do not split `::`, change the lexer, or alter a
genuine PV body such as `for 'a: :{A}`. This is conformance to the approved
empty-trivia colon/body grammar, not additional accepted syntax.

## Selected recovery simplification

One iterative head driver handles the first-binder requirement, the mandatory
colon after at least one binder, and a colon slot already covered by Error.
Each accepted binder owns its required leading trivia. Adjacent actual binders
retain their own BinderBoundary Missing, including after a malformed binder or
punctuation placeholder when no real trivia exists.

- Before any binder is accepted, malformed tokens use ForallBinder Error in
  one incomplete ForallTypeBinder node. This includes local comma/semicolon
  and non-binder Type-shaped source. Consume one maximal run until a top-level
  apostrophe binder, local literal colon or protected boundary. A non-binder
  Type atom is not a body or an arbitrary handoff just because a comma was
  seen. Thus `for, T` becomes one Binder Error over `, T`, not a comma Error
  followed by an unclaimed `T`. First-binder recovery never invents a body
  without an actual colon.
- After a binder, a fresh local comma/semicolon retains the exact native-token
  BinderBoundary Error and its existing incomplete binder wrapper. Iterate
  directly; repeated punctuation must not recurse through owner procedures.
  Outer-owned separators remain complete pending Items.
- Other malformed content after a binder uses ForallColon Error directly under
  ForallType, regardless of whether its eventual retry is another binder,
  actual colon or non-binder Type NUD. Local punctuation encountered inside
  that run is part of the same Error. This explicitly supersedes the
  architecture's retry-target-dependent Binder-versus-Colon role choice and
  the successor's speculative malformed-retry probe. A recovered binder may
  extend the list, but does not erase the Error already covering its one
  mandatory colon slot; EOF/outer handoff adds no same-slot Missing colon.
- After an actual colon, the body is mandatory. Missing and malformed source
  use ForallBody. A malformed run retries a canonical Type NUD without an
  additional Body Missing. A nested Type retains its own records and runs
  through the existing full Type entry, not a forall-specific subset.

Fresh boundary failures publish only their current mandatory slot: Binder,
Colon or Body. Missing colon never cascades Body Missing. An Error returning
directly at a boundary does not add a same-slot Missing. BinderBoundary Error
and a still-missing mandatory colon are distinct slots. Missing uses the
pending Item's remaining-start or inspected abstract coordinate. Failed slots
leave all caller/newline/fence/EOF leading pending. Leading before an actual
colon or admitted body is ForallType-owned and is emitted before a Missing
that retries that payload; it is not placed in a fake binder's boundary.

## Current-Item boundaries and output

Fresh attempts and Error retries use the same classification. Abstract
boundary, EOF, non-continuation newline, caller/outer contextual stop, enclosing
separator and unmatched close are protected before retry admission. A local
mandatory colon wins STOP_COLON/colon-shaped outer context only in the head,
never across layout/fence boundaries and never in the body.

First-binder malformed Type-shaped groups use a recovery-local matching-kind
stack, including the initial Item. Only a matching local close may carry a
non-continuation newline inside that run (retaining `for (@\n) 'a: T`). Other
non-continuation newline Items and explicit caller/contextual boundaries are
protected at every depth. Comments are opaque lexical trivia. Unmatched
closes remain pending; Forall does not own a close recovery slot.

The run returns its already-classified immediate target (binder, colon, body,
or boundary). The outer driver must not reopen a nested caller colon or binder
as a fresh local candidate after discarding the local matching stack. This is
an immediate control-flow result, not a persistent carrier, cache or replay.
No source observer is needed for the Error role or target.

All Errors are total and nonempty. Initial/retry leading is outside Error;
intermediate malformed leading is inside it. Native tokens and one singleton
OtherCharacter unexpected fact exactly cover the emitted extent. Missing has
no unexpected facts. Each record has one same-role/range expectation,
COMMITTED_RECOVERY_RULE sources and primary index zero:

| Type role | expected |
| --- | --- |
| ForallBinder | ForallTypeBinder |
| ForallBinderBoundary | TypeBinderBoundary |
| ForallColon | punctuation Colon |
| ForallBody | TypeExpression |

## Pre-write controls and intended test deltas

Ordinary root-Type byte offsets; `B`, `G`, `C`, `T` mean Binder, BinderBoundary,
Colon and Body. `M`/`E` mean Missing/Error.

| source | ordered records / continuation |
| --- | --- |
| `for` / `for ` | B M `3` |
| `for 'a` / `for 'a ` | C M `6` |
| `for 'a:` / `for 'a: ` | T M `7` |
| `for'a:T` | G M `3` |
| `for 'a'b:T` | G M `6` |
| `for: T` / `for : T` | B M `3` / `4`; actual colon and body |
| `for 'a T` | C M `7`; canonical body |
| `for @` / `for @ 'a:T` / `for @:T` | B E `4..5`; boundary/binder/colon retry |
| `for T` / `for, T` | B E `4..5` / `3..6`; no body reinterpretation |
| `for,,;` | B E `3..6`; one maximal first-binder run |
| `for 'a, 'b:T` | G E `6..7`; existing placeholder plus real binder |
| `for 'a, T` | G E `6..7`, C M `8`; body retry |
| `for 'a @` / `for 'a @:T` / `for 'a @ T` | C E `7..8` |
| `for 'a @ 'b:T` / `for 'a @ 'b` | C E `7..8`; two real binders, no malformed-binder wrapper |
| `for 'a @, 'b:T` | C E `7..9`; local comma belongs to the existing run |
| `for 'a: @` / `for 'a: @ T` | T E `8..9` |
| `for (@: T) 'a:T` | B E `4..10`; native matching parentheses |
| `for (@\n) 'a:T` | B E `4..8`; matching local close owns its newline |
| `for (@\n'b:T` | B E `4..6`; full newline/binder Item pending |
| `for (:):T`, active STOP_COLON | B E `4..5`; nested caller colon pending |
| `for (with):T`, active WITH | B E `4..5`; full caller word Item pending |

Accepted controls include `for 'a:{b:B}`, spaced record/PV/row bodies, nested
forall, comments/deeper binder layout, full path/call/apply/arrow bodies, and
the existing terminal/TypeApply controls. The compound-colon repair changes
the malformed normalized literals `for 'a :{A}` and `for 'a @ :{A}` to record
bodies with a shorthand inner field, just as the named-record colon gate did:
inner RecordFieldColon Missing at `10` / `12`; the second also has outer
ForallColon Error `7..8`. Retain both inputs, update their PV/record ancestry
and Missing expectations, and add genuine `for 'a @ : :{A}` as a PV retry
control. No body PV is lost when a distinct actual forall colon exists.

The old `for, T` / `for; T` source controls now require full malformed-run
consumption, no nested Type body, and one Error over punctuation plus `T`.
The `for 'a @ 'b: T` and deeper counterpart lose only their artificial
malformed-binder wrapper; Error belongs to Colon and the two actual binders
remain. Other first/continuation separator wrapper controls stay unchanged.
Normalized fence tests retain their source and pending-boundary assertions;
the obsolete malformed-probe test may be renamed for the forward run.

Add exact fresh/frozen/shifted/seeded records and node counts, caller/contextual
and quoted-fence handoffs, native nested tokens, structured PV reservation
order, actual enclosing-owner continuation and a bounded long punctuation run
to guard against the removed recursive retry. T6 remains open for actual
embedded/header-full certification. Required-Type Missing sites in the parent
are caller-owned and are outside this forall gate.

## Verification and resource budget

M2, primary-only pre-write contract audit, implementation and deterministic
verification; no independent review. One scoped pass and at most two batched
repairs. Use focused forall/Type, normalized Type, declaration/output/recovery-
output tests, one package check and scoped format/diff checks. Do not run the
broad workspace suite. Zero benchmark samples/processes. Remove the role
lookahead and duplicated lexical kind/stop predicates, and retain one forward
`O(bytes + structural work)` scan with recovery-only matching-stack allocation.
Existing sealed Error output and chasa-recover operations suffice; no generic
library API change is required.

## Construction result

Completed 2026-09-08, primary-only under the current user delegation. All
Forall-owned Missing/Error sites use the typed operations. The iterative head
driver retains its immediate boundary classification through malformed runs;
there is no role lookahead or recursive punctuation retry. The actual colon
before a record body is owned correctly without changing Type lexing.

Ten new `tests/type_expr/forall_recovery.rs` tests cover exact fresh/frozen,
shifted and seeded records, native Error extents/ancestry, no-cascade mandatory
slots, caller/contextual/nested and CRLF quoted-fence handoffs, canonical
bodies, real enclosing Call closes, structured PV parent-before-child order,
and bounded 1024-token first-binder / 512-token continuation punctuation runs.
Existing malformed witnesses received only the predeclared ownership deltas.

- `cargo test -p yu-syntax --lib forall -- --test-threads=1`: 32 passed,
  including six historical grammar controls (not a recovery-equality oracle).
- `cargo test -p yu-syntax --lib rewrite::tests::type_expr:: -- --test-threads=1`:
  186 passed.
- Reused `target/debug/deps/yu_syntax-b491637626fa8c73` with the combined filters
  `rewrite::tests::normalized::normalized_type`,
  `rewrite::tests::normalized::ordinary_type_unmatched`,
  `rewrite::tests::type_decl::`, `rewrite::tests::output::`, and
  `rewrite::tests::recovery_output::`, plus `--test-threads=1`: 95 passed
  (27 + 39 + 4 + 25).
- `cargo check -p yu-syntax`, scoped `rustfmt --check --edition 2024`, and
  `git diff --check`: passed. Existing 87 package / 38 test warnings.

No repair round, independent review, broad certification or benchmark run.
Benchmark budget consumed: zero samples/processes. Test compilation took
2m04s; one environment observation found an active rustc around 570 MiB RSS.
No generic chasa-recover operation was missing. Required-Type caller slots,
the complete typed-owner ledger, actual embedded T6/header-full proof and
public/root adoption remain separate open work.
