# Named-record field-internal current-Item recovery

Status: Authoritative; private field-internal construction complete

Date: 2026-09-08

Scope: RecordFieldName, RecordFieldColon and RecordFieldType in private
`rewrite/type_expr/record.rs`, plus removal of the superseded record-only raw
RHS helper and unused ordinary wrapper from `type_expr.rs`. Whole-field,
separator, close, forall and aggregate/public adoption are later gates.

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Drafted-and-checked-by: primary under the user's no-subagent instruction

## Retained grammar and ownership

The architecture's named-record surface grammar and TypeRecordField recovery
table govern this gate: plain Identifier, literal colon, full canonical Type
RHS; comma or qualifying newline list, with no shorthand/default/spread syntax.
Keep the same-line complete-next-field query, deeper continuation, Type-ML,
caller context and nested Type disposition. Retain the field-authority probe's
algorithm, with only the colon-kind correction below: malformed-name +
actual-colon skeleton remains distinct from a malformed whole field. This gate
does not certify that probe or sequence recovery.

Each committed TypeRecordField owns its three internal roles. Actual colon
completes its slot; a missing/malformed colon may retry a Type NUD as RHS.
Colon failure at a boundary never creates a same-cause RecordFieldType Missing.
After an actual colon, a missing/malformed RHS belongs to RecordFieldType;
nested Type failures keep their own roles.

The field-slot audit also found an accepted-input implementation gap: the
Type lexer labels the one-byte `:` before `{` as PolymorphicVariantColon.
At an already-owned field-colon position it is still the actual field colon,
so `{a:{b:B}}` must parse a nested record without recovery. Use one local
colon-kind predicate for field dispatch, colon/name retry and field-head
queries; both Colon and PolymorphicVariantColon represent this one literal
byte. The RHS keeps its usual PV classification. A PathSeparator `::` is not
split or accepted as a colon. This is conformance to the approved empty-trivia
field grammar, not new syntax. Missing-name `{:{b:B}}` uses the same local
colon authority. The parent field-start helper may move to this owning module
to share that predicate.

The old normalized PV-at-field-slot test encodes the opposite malformed
interpretation for `{a :{A}}` and `{a @ :{A}}`: it treats the sole colon as a
PV opener after a failed field colon. That cannot prescribe an accepted-input
contract because the outer field colon was missing. Under the selected
actual-colon priority these are nested records with an inner shorthand `A`:
the first has only inner Colon Missing at `6`; the second has outer Colon
Error `3..4` followed by inner Colon Missing at `8`. Update that test's name
and two shape rows, retaining those literal controls and the unchanged valid
PV RHS rows. Add `{a @ : :{A}}` as the explicit malformed-colon/actual-colon/PV
retry control (outer Colon Error `3..4` only). This is a deliberate recovery
correction alongside the accepted `{a:{b:B}}` repair.

## Current-Item rule

Before a colon/RHS attempt or retry, classify abstract boundary, EOF,
non-continuation newline, sequence separator/close and explicit caller stop.
These remain complete pending Items. An actual colon at an eligible colon
slot is local even if the outer caller has STOP_COLON; it does not override
a layout/fence boundary. In the RHS slot, STOP_COLON remains a caller stop.
Explicit caller words are checked before a fresh NUD, not only after Error.
This fills the current fresh colon/RHS admission gap without changing accepted
no-recovery source under the intended caller contract.

Missing publishes a zero-width record at the remaining-start, or at an
inspected abstract boundary's coordinate. Boundary leading belongs to the
record sequence/caller, not the failed field slot. This replaces the old raw
field Missing branch's eager comma/close/EOF-leading emission. Leading admitted
for a valid colon/Type or a Missing-colon Type retry is field-owned as before.

Colon and RHS malformed runs share one total forward operation. Emit initial
leading at TypeRecordField, consume malformed lexical Items in native syntax
kinds, and return the first allowed retry or boundary. A colon run retries
actual colon or Type NUD; an RHS run retries Type NUD. Initial/retry leading
stays outside Error, intermediate malformed leading stays inside it. A run
ending at a boundary emits no additional same-slot Missing.

The committed malformed-name path uses typed total Error output with its
existing delimiter-depth and plain-Identifier handoff rule. Its actual-colon
retry remains field-owned; abstract and explicit caller boundaries stay
protected. No lookahead, cache, source replay or generic API is added.

Every Error and singleton OtherCharacter unexpected fact cover exactly the
emitted nonempty run. Each Missing has no unexpected facts. Records have one
same-role/range expectation, COMMITTED_RECOVERY_RULE sources and primary zero:

| Type role | expected syntax |
| --- | --- |
| RecordFieldName | Identifier |
| RecordFieldColon | punctuation Colon |
| RecordFieldType | TypeExpression |

## Pre-write controls

All coordinates below are ordinary root-Type byte offsets. Only field-internal
records are listed; an unclosed enclosing record retains its currently raw
close node until the separate sequence/close gate.

| source | ordered field-internal records / continuation |
| --- | --- |
| `{: A}` | Name Missing `1..1` |
| `{:{b:B}}` | Name Missing `1..1`; colon then nested record RHS |
| `{:}` | Name Missing `1..1`, Type Missing `2..2` |
| `{@: A}` / `{'a: A}` / `{1: A}` | Name Error `1..2` / `1..3` / `1..2` |
| `{@ (): A}` | Name Error `1..5`, native parentheses inside Error |
| `{a}` / `{a }` | Colon Missing `2..2`; sequence owns optional space |
| `{a A}` | Colon Missing `3..3`; canonical RHS `A` |
| `{a:}` / `{a: }` | Type Missing `3..3`; sequence owns optional space |
| `{a @ : B}` / `{a @ B}` / `{a @}` | Colon Error `3..4`; actual colon/RHS/boundary retry, no cascade |
| `{a :: B}` / `{a = B}` | Colon Error `3..5` / `3..4`, native punctuation |
| `{a: @ B}` / `{a: @, b: B}` | Type Error `4..5`; retry or next field |
| `{a @\n  B}` / `{a: @\n  B}` | Colon Error `3..4` / Type Error `4..5`; deeper retry leading outside Error |
| `{a:\nb: B}` | Type Missing `3..3`; record-owned newline and second field |
| `{a with tail`, active WITH | Colon Missing `2..2`; complete space/word Item pending |
| `{a: with tail`, active WITH | Type Missing `3..3`; complete space/word Item pending |
| `{a @ with tail` / `{a: @ with tail`, active WITH | Colon Error `3..4` / Type Error `4..5`; complete retry Item pending |
| `> > {a\n> > ```\nouter` | Colon Missing `7..7`; fence leading pending |
| `> > {a:\n> > ```\nouter` | Type Missing `8..8`; fence leading pending |

Check accepted nested Type controls, no same-slot cascades, comma/newline field
continuation, active STOP_COLON's distinct local-colon/RHS behavior, shifted
origins, native CST ancestry, frozen IDs, seeded output and structured PV
outer-before-inner ordering. Existing raw construction tests gain these typed
records, without reclassifying accepted input. The narrow leading-trivia
ownership change follows the rule above, not observed legacy recovery output.

## Verification and cost

M2, primary-only pre-write contract audit, implementation and deterministic
checks; no independent review. One scoped implementation/repair pass; focused
field tests, full Type, normalized Type, TypeDeclaration/output/recovery-output,
package check and scoped format/diff checks. No broad workspace certification.
Zero benchmark samples/processes. The existing malformed-name lexical probe's
algorithm is unchanged; colon/RHS scanning is forward and linear, with
recovery-record allocation only on malformed input. Generic chasa-recover operations already
suffice; owner roles and CST policy stay in yu-syntax.

## Construction result

Completed 2026-09-08. The three field-internal roles publish all their local
Missing/Error records through the existing sealed output. Colon and RHS use
one forward malformed-run helper; boundary-first fresh/retry behavior retains
the full caller Item. Removed the record-only raw RHS helper and its unused
ordinary wrapper. RecordFieldName's existing authority probe and depth policy
remain uncertified until sequence preflight; its committed Error is now typed.

The local colon-kind predicate fixes `{a:{b:B}}`, missing-name nested records,
malformed-colon retry, and the same-line next-field query. Actual PV RHS
parsing remains intact. The two historical malformed normalized PV-candidate
rows now follow the written actual-field-colon priority; their inputs were
retained, with new explicit-PV and exact nested-role controls.

Eight focused tests pass, with fresh/frozen/shifted/seeded records, native CST,
caller words, literal-colon priority, quoted fences and structured PV order.
Complete Type: 167 passed; normalized Type/unmatched head: 27; declaration: 39;
output: 4; recovery output: 25. Package check and scoped rustfmt/diff checks
passed. No independent review, broad suite or performance measurement was
run (zero benchmark samples/processes). Whole-field/sequence/close, forall,
caller-owned required-Type Missing and aggregate/public adoption remain open.
