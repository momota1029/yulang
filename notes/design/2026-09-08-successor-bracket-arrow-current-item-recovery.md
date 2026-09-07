# BracketRowArrow current-Item recovery

Status: Authoritative; private BracketRowArrow construction complete

Date: 2026-09-08

Scope: private mandatory arrow after a trailing BracketRow in
`rewrite/type_expr.rs` (T4A producer). LeadingEffectTypeHead, record/forall,
distinct embedded T7c evidence and aggregate O6/public certification stay open.

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Drafted-and-checked-by: primary under the user's no-subagent instruction

## Selected rule

Retain BR-G/L/A's mandatory arrow, row attachment, full RHS recursion and
right association. An actual arrow uses the existing ArrowRhs procedure.
A Type NUD without an arrow receives one BracketRowArrow Missing and retries
as RHS. Boundary-first ordering protects caller stops, outer contextual
boundaries, punctuation separators/closes, non-continuation newline and
abstract fences before a candidate or recovery attempt.

Fill the currently unimplemented malformed-arrow run with one forward total
Error operation. Emit initial leading at TypeArrowTail, consume complete
malformed Items until an actual arrow, valid Type NUD or protected boundary,
and emit one Error with a singleton OtherCharacter fact over its emitted
extent. Retry leading stays outside Error, as for the selected P/E/B rules;
this supersedes the T4 register amendment's T4A retry-leading/eighth-terminal
proposal. A recovered arrow or RHS never receives a second Arrow Missing.
If this Error reaches a boundary, return it without an ArrowRhs Missing.

When the row itself returns incomplete, do not reinterpret its pending Item
as an arrow or RHS. Publish the distinct required Arrow Missing and return the
same Item. This retains the existing EOF item/close/arrow slot distinction and
fills its missing non-EOF publication. Close failure and the required arrow
remain different slots; do not create an additional ArrowRhs Missing.

All records use `Type(BracketRowArrow)`, expected punctuation Arrow,
`COMMITTED_RECOVERY_RULE`, one same-role/range expectation and primary index
zero. Missing has no unexpected facts. Its anchor is the inspected abstract
boundary coordinate, otherwise the Item's remaining-start after permitted
owner emission. EOF continuation trivia is owner-emitted; protected newline,
caller and fence leading stays pending. No recovery record extends through
unemitted retry trivia.

## Pre-write controls

| source | ordered arrow-owned records / continuation |
| --- | --- |
| `F [e] -> U -> V` | none; existing right-associated RHS |
| `F [e]` | Missing at `5`; no ArrowRhs Missing |
| `F [e] U` | Missing at `6`; `U` is RHS |
| `F [e] @ -> U` | Error `6..7`; retry space outside Error; actual arrow and RHS |
| `F [e] @ U` | Error `6..7`; RHS retry, no additional Missing |
| `F [e] @` / `F [e] @ ` | Error `6..7`; EOF with no Missing cascade |
| `F [e] @\nU` | Error `6..7`; complete newline/`U` Item remains pending |
| `F [e] @ with`, active WITH caller/outer boundary | Error `6..7`; space/word remains pending |
| `F [e]\nU` | Missing at `5`; complete newline/`U` Item pending |
| `F [A` | B close Missing at `4`, then Arrow Missing at `4` |
| `F(T [A)` | B close Missing at `6`, Arrow Missing at `6`; outer Call owns `)` |
| `> > F [e] @\n> > ```\nouter` | Arrow Error `10..11`; abstract boundary Item remains unconsumed |

Controls additionally cover comma/close and explicit word stops, LF/CRLF,
block comments/UTF-8, multiple malformed Items, shifted origins, frozen IDs,
seeded output and structured PV record order. Previously B-only expectations
gain the newly migrated arrow records; row-owned node assertions still count
only their row records. Accepted-input expectations do not change.

## Verification and cost

M2, primary-only. One scoped implementation/repair pass; focused arrow tests,
full Type filter, TypeDeclaration/output/recovery-output siblings, package
check and scoped format/diff checks. Existing total Error-run output needs no
new generic API, partial-Item terminal, rescan or retained source. Linear
forward scanning; allocations only for actual recovery records. Zero benchmark
samples/processes. No independent-review or aggregate certification claim.

## Construction result

Completed 2026-09-08 by the primary under the user's direct-work instruction.
Missing publication now covers every accepted row-arrow continuation, including
an incomplete row's non-EOF handoff. Malformed arrow content uses one typed
total Error run; actual arrow/RHS retries do not add a same-slot Missing.
The valid path classifies its leading boundary once, and Error retry preserves
native token kinds, owner trivia and the complete protected current Item.

Five focused tests pass. The complete Type filter passes 152 tests;
TypeDeclaration 39, output 4 and recovery output 25 pass. Package check, scoped
rustfmt and diff checks pass. B-boundary tests gain the migrated parent arrow
record without changing their pending Item or row extent. Two earlier tests
gain the selected non-EOF Missing arrow and now assert its full fields, not
only a node count. Accepted source controls remain unchanged.

No benchmark samples/processes or independent review were used. The distinct
T7c embedded witness, LeadingEffectTypeHead, record/forall, actual header-full
and production/aggregate adoption gates remain open.
