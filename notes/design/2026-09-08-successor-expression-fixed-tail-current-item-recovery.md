# Expression fixed-tail current-Item recovery

Status: Authoritative; private O3b construction complete

Date: 2026-09-08

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Drafted-by: primary from independent architecture and pre-write specification
audits

Scope: the `FieldTail` and `PathTail` name slots in private
`rewrite/tails.rs`: `field_tail_normalized`, `path_tail_normalized`, their
current-Item scanners and their shared malformed-name Error operation. This
replaces those owners' raw Missing/Error construction only. `Colon`/`With`,
projection, delimiter, literal, Statement and declaration owners, public
dispatch and O4/O5/O6/O7 remain outside this gate.

Authority: the recovery-authority amendment §§1--3, the typed-output amendment
§§3--6, the expression-tail handoff addendum §§2.1 and 3--5, Gate 3 fixed-tail
pilot §§2--3 and 5--6, and the architecture FieldTail/PathTail grammar and
recovery tables. Yulang2 supplies accepted-input evidence only; its malformed
output is not a successor target.

## Slots and accepted controls

The finite mapping is fixed. No role, expectation vocabulary or generic
recovery API is added.

| owner | role | expected syntax | accepted name |
| --- | --- | --- | --- |
| `FieldTail` | `Expression(FieldName)` | `Identifier` | adjacent ordinary `Identifier` with grammar-empty internal leading |
| `PathTail` | `Expression(PathSegment)` | `Identifier` | `Identifier` or `SigilIdentifier` after the existing permitted path `G*` |

The accepted `.` or `::` introducer remains in its existing tail node. Existing
accepted controls, including `x.foo::bar`, `x:: $name`, sigil paths, longest
dot/operator classification and projection handoff, remain unchanged. A
recovered name is not fabricated as an expression primary and no later spaced
word is attached as that name.

Every Missing has the selected role, a zero-width site/expectation range, no
unexpected facts, one `Identifier` expectation with
`COMMITTED_RECOVERY_RULE`, and primary expectation zero. Every Error has the
same role/expectation and exactly one `OtherCharacter` token fact spanning its
nonempty emitted run. Ordinary malformed payload token kinds remain native;
an operator-shaped payload is an `Operator` token, never an accepted operator
node.

## Boundary, leading and Error rule

Classify absence before accepting a candidate name or emitting its current
Item: abstract/fence boundary, active caller stop, an explicit
`STOP_LINE_BREAK` line stop, ordinary EOF, separator, close, accepted dynamic
LED, `(`, `[`, `.`, `::`, or the applicable colon boundary. A lone `:` is
always that terminal outer-tail continuation, whether or not `STOP_COLON` is
active; it is not Error payload for the Field/Path name slot. The active-stop
observation is lexical-only and is made both before Path's word/sigil admission
and from inside the sealed Error run; a contextual stop may not be swallowed as
a path segment. The existing longer operator/projection and deferred-dot
judges retain priority.

Field additionally treats nonempty internal grammar leading as absence. Its
Missing anchors at the dot-adjacent inspected coordinate and returns the whole
following Item, including leading, to the outer tail. Path retains its
authoritative maximal `G*` inside `PathTail`, including a physical newline
when `STOP_LINE_BREAK` is absent; it is not an equal/shallow-layout boundary.
A protected Item after that leading is absent and stays whole. Every protected
non-EOF boundary keeps its remaining Item and leading; anchor at the abstract
coordinate or remaining start. Ordinary EOF may emit remaining path-leading
before anchoring at EOF. No leading is reconstructed.

For a non-boundary non-name Item, emit the initial leading owned by the tail
outside Error, then consume one maximal nonempty lexical Error run. Field uses
the existing total LED lexical current-Item scan. Path uses the corresponding
sigil-aware lexical current-Item scan whose payload rule is the same
`scan_path_segment_payload` used for ordinary Path acquisition; it is still a
lexical operation and exposes no grammar or builder capability. Read forward
once per Item using only the sealed Error-run capability. Stop before a
trivia-bearing retry Item, any boundary above, an accepted Field/Path name, or
a fixed/dynamic tail continuation. Internal run leading belongs to Error;
retry/boundary leading does not. The Error operation never calls a grammar
parser or builder, does not replay source, retain a run vector, rescan CST, or
sort diagnostics.

After Error, do not emit a second Missing for the same name slot. Finish the
tail and hand the retained Item, successor coordinate and line entry to the
ordinary outer tail with its unchanged threshold, ML mode, stops, baseline,
line/fence and ambient context. Normal completion scans again; a lower
threshold same Item is handed back without rescan; caller-visible End
propagates. This owner does not make a colon/with decision.

## Pre-write evidence and adjudication

The retained exact slots are mandatory and initially lack committed records:

| source | selected record |
| --- | --- |
| `x.` | `Missing(Expression(FieldName))` at `2..2` |
| `x.@` | `Error(Expression(FieldName))` at `2..3` |
| `x::` | `Missing(Expression(PathSegment))` at `3..3` |
| `x::123` | `Error(Expression(PathSegment))` at `3..6` |

`x::::name` and `x::::$name` retain one first-Path Missing at `3..3` and let
the second separator form the next PathTail. `x. field` keeps a FieldName
Missing at `2..2` and returns the spaced word. `x:: 123` keeps its path-leading
outside Error and produces the Error at `4..7`. `x::123$name` publishes the
PathSegment Error only at `3..6` and retains the adjacent sigil name as the
next current Item; the equivalent `$name`, `&name` and `'name` witnesses all
stop before their sigil. A generic LED scanner may not absorb that sigil before
the Path-name stop.

Before and after a malformed run, verify active comma/colon/word stops, each
close, ordinary EOF, explicit line stop and quoted fence, plus the accepted
non-stopped Path newline control. Also verify fixed-tail retry, dynamic LED and lower-threshold/ML
handoff, UTF-8/CRLF/foreign-prefix ranges, seeded/frozen record reuse and an
effect-free rejected/deferred tail. Retain existing source literals and node
parent/count assertions for `x.`, `x.@`, `x::`, `x::123`, `x::::name`, accepted
field/path/sigil forms, double-dot and the normalized fence continuation. New
tests may add exact records; they do not weaken those controls.

## Execution boundary

This is an internal M2 parser-recovery gate: one implementation pass, at most
one batched repair pass, and specification plus compiler/recovery delta review.
The hot path adds bounded boundary/role checks only; no material allocation or
traversal is introduced, so the measurement budget is zero samples/processes.
Run focused tails/current-output controls and one package check after repair,
then scoped format/diff checks. Synchronize task, index, ledger and daily
before the coherent commit. No public parser cutover follows from this gate.

## Construction result

Completed 2026-09-08. `FieldTail` and `PathTail` publish typed
`Expression(FieldName)` and `Expression(PathSegment)` Missing/Error records
through one finite local draft mapper. Their malformed runs now use sealed
lexical current-Item operations; Path's scan retains `$`, `&` and `'` sigil
names as retry Items, and a contextual caller stop cannot be accepted first as
a path segment. Lone colon, fixed tails, dynamic LEDs, stops, closes, layout
and fence Items remain pending for their actual owners.

Nine focused tests pass after the pre-write witness failed on the prior empty
record vector. They cover exact fresh/frozen records, nonzero prior/reused IDs,
deferred/rejected effect-free entries, sigil retry, protected stops/closes,
UTF-8/CRLF/fence extents, accepted Path newline, colon and threshold/ML
handoff. Existing tails (14), normalized (83) and recovery-output (25) filters
also pass; `cargo check -p yu-syntax`, scoped format and diff checks pass with
the existing 87 warnings. Independent post-write specification review found
one test-evidence gap; the bounded repair and independent delta review closed
it. No benchmark, broad suite, public cutover or aggregate certification ran.
