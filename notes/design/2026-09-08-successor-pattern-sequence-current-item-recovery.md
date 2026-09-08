# Pattern sequence current-Item recovery

Status: Authoritative; private O3b substep complete

Date: 2026-09-08

Approved-by: user through the ongoing recovery-selection and simplification
delegation. Drafted-and-checked-by: primary under the explicit no-subagent
direction; this is not independent certification.

Scope: the four remaining raw Pattern delimiter Error sites, their sequence
continuation, and the existing literal-primary admission at that boundary.
RecordDefaultExpression and the other SCC owners remain separate obligations.
No public/root/header dispatch changes.

Authority: the current recovery-authority amendment, Pattern primary and
delimited-slot amendments, architecture P5/P6/P7 and comma-or-layout grammar,
and direct-literal LC-5. Yulang2 supplies accepted-input evidence only.
This selects successor recovery instead of the old one-token skip behavior.

## Sequence rule and exact records

The owner retains two phases: expecting an item, and after an item. Matching
local close wins; an explicitly carried caller close and abstract fence/EOF
return through the existing close-Missing handoff. Ordinary outer stop bits
alone do not make a close caller-owned. Fresh repeated commas keep the existing
item-Missing rule, and same-line adjacent accepted items keep separator Missing.

An unclaimed wrong close is one native-token Error in either phase, with
ClosingDelimiter(ParenthesizedPattern/Parenthesis, ListPattern/Bracket, or
RecordPattern/Brace), expecting that owner's close punctuation. Its unexpected
category is Punctuation(Close(actual delimiter)). Its range is the emitted
current Item's remaining extent, including any remaining leading. It consumes exactly that
Item, preserves the phase, and reads the next Item once.

A non-start in Record's item phase belongs to Pattern::RecordItem (Identifier
expectation). A non-start after an item belongs to that owner's
Pattern::*Separator (DelimitedSequenceSeparator expectation). There are two
disjoint nonempty recovery units:

1. Ordinary malformed Items form one maximal lexical Error run. Stop before
   comma, any close, EOF/fence, an accepted owner item start, or a Record
   wrong-kind Pattern primary. Emit initial leading directly under the sequence
   owner; internal trivia belongs to the run; the stopped Item retains all
   remaining leading. Native token kinds are retained.
2. A Record wrong-kind Pattern primary is one structured Error containing its
   canonical Pattern, including its own tails, delimiters and literal owners.
   A number, symbol, parenthesized/list/record Pattern or quote cannot be a
   record field name, but its interior must not be mistaken for outer fields
   or closes. Parse it with the existing local stops, descendant caller-close
   capability, layout baseline, fence and ambient context. Nested owners keep
   their own recovery roles. Emit initial leading before opening Error.

Each unit publishes one Error with one OtherCharacter unexpected fact covering
its actual nonempty extent. The expectation has the same role/range,
COMMITTED_RECOVERY_RULE sources and primary index zero. A lexical prefix and
a subsequent structured Pattern are distinct units, not one retrospective
Error. After either unit, retry an item without an additional separator Missing;
a pending comma is consumed as the separator, without a duplicate item Missing.
Another fresh comma can still open another missing slot. Child completion facts
remain distinct from diagnostic absence; complete malformed units do not by
themselves force PatternCompletion::Incomplete.

## Structured capability and source bounds

Extend only the authorized caller scope of the 2026-09-07 structured-reservation
and extent-validation amendments to the two Record roles above. The existing
total helper reserves the outer record before entering Pattern, so nested
records follow it even though their owners finish first. Start comes from the
leading-cleared current Item; end is the returned pending Item's remaining
start, or the threaded successor coordinate when no pending bytes exist.
An abstract boundary's inspected coordinate is not an emitted end. The existing
byte-delta check, frozen matching, LIFO discipline and discard-only failure
contract remain unchanged. Deferred handoff, if returned, retains its Item and
uses the same end rule. No new output capability or speculative publication.

The sealed lexical Error-run API stays lexical-only. Do not use the structured
helper for raw runs, implement a parallel literal scanner, replay source, retain
a token collection, or derive ranges by walking the completed CST. The static
bound remains O(bytes + structural work); nested Pattern already owns its
structural stack, and each recovery unit adds one ordinary record/reservation.
No new valid-input allocation, search pass or chasa-recover API is required.

LC-5 already admits Pattern literals. The sequence start predicate must use
the same Pattern-primary judge as the canonical entry, including quotes.
Both NUD and tail current-Item scans must preserve a whole literal opener;
a tail-returned heredoc opener must not become a one-quote RuleLiteral when
the sequence retries it. This corrects accepted comma/layout literal elements,
not the literal grammar. Two-quote rejection remains maximal and unaccepted.

## Pre-write evidence and expectation adjudication

The decisive bounded witness is `{"""}""", a}`: RecordItem Error 1..8
contains Pattern > StringLiteral, the inner `}` is StringText, and the outer
native close at 11..12 follows field `a`. Add this and accepted layout literals
as failing tests before production changes. Their accepted basis is LC-5 and
the existing comma-or-layout sequence grammar, not successor success.

Also cover `{@,a}` (one item Error, no duplicate Missing), `[a; b]` and
`(a; b)` (one separator Error), malformed multi-Item runs, wrong closes in both
phases, `{(A}` (outer Error before nested close Missing), recursive `{{1}}`
reservations, actual caller closes, EOF and quoted fences. Seeded records,
nonzero origins, exact full pending Items, fresh/frozen IDs, native kinds and
accepted companions are required. Valid nested literals exercise the source
boundary now; their still-raw recovery sites remain in the O3b ledger.

Existing `{a == b}`, `{a => b}`, `{a =+ b}` sources are retained. Their old
Error text included initial whitespace; the selected rule moves that initial
leading directly under RecordPattern, so Error text becomes only the spelling.
Keep token-kind, no-Equals, next-field and no-Missing assertions, and add the
direct-trivia assertion. Other mismatches require cause analysis, not automatic
expectation changes. Existing Record default Missing is not changed here.

Pre-repair test audit: `{a :tag, b}` is an accepted same-line field-colon
form, not a wrong-kind Symbol in the after-item phase. Retain it as an accepted
control; use `{a\n:tag, b}` for that phase's wrong-kind Symbol, since the field
owner does not take a physical-newline colon. This follows the existing field
grammar and does not change colon admission. The first implementation pass
also exposed a post-Error token query before the loop's fence check; guard the
phase calculation so an abstract Item reaches the boundary handler untouched.

M2 primary-only, one pass and at most two repairs. Run focused Pattern tests,
the known-small owner/output filter set, one package check and scoped
format/diff checks. Benchmark budget: zero samples/processes. Synchronize the
single accumulating ledger, task, index and daily record before commit. O3b
SCC, aggregate RB/matrix, header/full/Yumark and atomic cutover stay open.

## Construction result

The four raw Error sites are replaced by the shared phase-aware sequence loop,
sealed native lexical run, native wrong-close publication, and the two scoped
Record structured callers. Pattern tail scanning preserves maximal literal
openers, and sequence admission uses the canonical Pattern-primary predicate.
The output prerequisite is unchanged except for removing the now-inaccurate
PV-only wording from its leading-precondition assertion.

Before production changes, both new bounded tests failed: the heredoc witness
emitted only `{"""}` and the accepted layout literal acquired spurious
recovery. Both now pass, along with six further exact-record tests. The
first compiled pass passed 46/48; one repair bundle addressed the boundary
phase query and the pre-adjudicated field-colon test premise above. The earlier
compile attempt needed a missing semicolon and the existing nested punctuation
category spelling corrected; no output contract changed for those corrections.

- Focused Pattern command: 48 passed, zero failures/ignored, 0.21s.
- Existing 19 owner/output filters plus `normalized_pattern` and `literal::`:
  533 passed, zero failures/ignored, 1.95s. Before the repair these same
  filters had only the two known new-test failures, 531 passed.
- `cargo check -p yu-syntax`: passed in 5.65s; scoped rustfmt/diff: passed.
- Existing warnings remain 38 test / 87 package. The pre-change test build
  took 1m04s; one build-resource observation showed rustc at about 1.5 GiB
  with available memory. There was no benchmark (zero samples/processes).

The single ledger maps both structured roles and all lexical/close sites,
fresh/frozen ordering, total-entry/RB boundaries and the two still-raw
RecordDefaultExpression Missing sites. No raw Error constructor remains in
Pattern. This is private O3b construction, not independent SCC or public
certification. Task/index/ledger/daily records are synchronized.
