# Named-record sequence and close current-Item recovery

Status: Authoritative; private construction complete

Date: 2026-09-08

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Drafted-and-checked-by: primary under the user's no-subagent instruction

## Scope and retained authority

Complete RecordField, RecordFieldSeparator and NamedRecordType close output in
private `rewrite/type_expr/record.rs`. Audit the malformed-name authority probe
and its committed scan together. Retain the architecture's named-record grammar,
complete-next-field query before TypeApply, full canonical RHS, literal-colon
classification and the completed Name/Colon/Type slot rules. No public/root,
forall or embedded/header certification is included.

The sequence table at `2026-08-20-yu-syntax-chasa-architecture.md` remains the
role/slot basis. The following current-Item rules replace incomplete raw
successor paths and the malformed-name probe's kind-insensitive depth policy.
These are successor recovery choices, not Yulang2 malformed-output equality.

## Sequence and termination

One owner loop distinguishes the initial field slot, a field slot after comma,
the successor of a parsed field, and the successor of a malformed run.

- Actual `}` closes this record; comma belongs to this record, including when
  the enclosing caller also recognizes that punctuation. Neither belongs to
  Error. An actual close after comma is valid trailing punctuation.
- Leading/repeated comma publishes RecordField Missing before that comma.
  After a field, a complete same-line `Identifier ... Colon` head publishes
  RecordFieldSeparator Missing after its record-owned gap, then retries the
  field. The shared accepted-path query is unchanged. A qualifying newline
  before a field-start is an implicit separator, not a Missing separator.
- EOF, abstract boundary, inherited unmatched close and explicit caller stop
  end an incomplete record with exactly one close Missing. A pending field
  after comma also has one RecordField Missing. An ordinary qualifying newline after a
  completed/recovered field opens a separate field slot: if the next Item is
  an outer boundary/EOF instead of a local field, publish Field Missing then
  close Missing. An abstract boundary is not a record-local implicit separator:
  its leading is opaque to that decision, so it adds a Field Missing only in
  the already-established post-comma slot. No Missing is added for an already
  failed field slot itself.
- At a fresh/implicit/retry field position, literal colon is the local
  missing-name skeleton. A complete plain-name/colon head is local even when
  its name is a contextual caller word. Other explicit caller Items retain
  all leading. After a field the same-line query determines that authority
  before TypeApply; a bare caller word does not become a recovered field.
- Semicolon at a field/sequence position is a separator Error unless an
  explicit caller claims it. Other unexpected after-field content also uses
  separator recovery, instead of silently returning an unclosed record.
- An unclaimed mismatched close starts close-only recovery. Emit one maximal
  native-token Close Error through subsequent malformed content until actual
  `}`, EOF, abstract/caller/inherited-close boundary or a non-continuation
  newline. Do not retry field grammar inside this failed close slot. A failed
  retry still publishes the required close Missing; an actual `}` does not.
  This replaces the raw successor's unconditional mismatched-close handoff.

Initial and retry leading admitted by the list is emitted directly under the
record, outside Error. Boundary leading is untouched, including caller words
and inherited closes. Eligible EOF continuation trivia may be list-owned;
non-continuation newline and abstract-boundary trivia stay pending. Missing
anchors use remaining-start or the inspected abstract coordinate. Nested
incomplete record instances each publish their own close; do not deduplicate
equal roles/coordinates. The existing parent Type-tail disposition is retained.

## Forward malformed runs and name authority

Whole-field recovery stops at a complete name/colon head or literal-colon
skeleton. Separator recovery can retry any plain-name/literal-colon field
start; caller words still require a complete head. Both stop at local comma,
record close, unmatched close, caller/fence/EOF, or qualifying newline. Return
the whole Item; the sequence loop decides its ownership and required records.
An explicit caller claim reached inside a malformed nested run is already
decided: carry that immediate exit fact to the sequence loop, which closes
the record without reopening the pending Item as a fresh field skeleton.

Use a recovery-local stack of matching delimiter kinds, accounting for the
initial malformed Item as well as later Items. At nested depth, a matching
local close can include a qualifying newline (retaining the existing
`{a: A; (\n) b: B}` control). Other non-continuation newline Items and explicit
caller Items are protected at every depth. A mismatching close cannot discharge
another kind; actual record `}` and inherited unmatched closes are never
swallowed to manufacture balance. Comments remain opaque lexical trivia.

The name-authority probe remains sink-free and is used once before committing a
malformed field. It must find a real top-level literal colon before any
top-level plain Identifier/separator/close, any physical newline, fence/EOF or
explicit caller stop. A top-level colon is the prospective local mandatory
colon even under STOP_COLON; nested colon has no such authority. The probe and
committed Name Error use the same kind-matching and boundary priorities.
Retain observed token spelling for caller-word checks; do not infer caller
claims from kind alone or let the probe inspect beyond a protected Item.

Every Error is total, nonempty and source-contiguous, with one OtherCharacter
unexpected fact exactly covering its emitted extent. Missing has no unexpected
facts. All records have one same-role/range expectation with
COMMITTED_RECOVERY_RULE sources and primary index zero:

| role | expected |
| --- | --- |
| Type(RecordField) | Identifier |
| Type(RecordFieldSeparator) | DelimitedSequenceSeparator |
| ClosingDelimiter(NamedRecordType, Brace) | punctuation Close(Brace) |

## Pre-write controls and deliberate deltas

Coordinates are ordinary root-Type byte offsets. `F`, `S`, `C`, `N` mean whole
Field, Separator, record Close and field Name. `M`/`E` mean Missing/Error.

| source/context | ordered records / continuation |
| --- | --- |
| `{,a:A}` / `{a:A,,b:B}` | F M `1` / F M `5` |
| `{a:A b:B}` / `{a:A b:{c:C}}` | S M `5` |
| `{a:A; b:B}` | S E `4..5`; two fields |
| `{a:A,` | F M `5`, C M `5` |
| `{a:A\n` | F M `4`, C M `4`; newline stays pending |
| `{@ a:A}` / `{..A,b:B}` | F E `1..2` / `1..4`; next field retries |
| `{@:A}` / `{():A}` / `{(:):A}` | N E `1..2` / `1..3` / `1..4` |
| `{@ (:):A}`, active STOP_COLON | F E `1..4`, C M `4`; nested colon pending |
| `{@ (with):A}`, active WITH | F E `1..4`, C M `4`; `with` pending |
| `{@ (with:A)}`, active WITH | F E `1..4`, C M `4`; nested complete head is still caller-owned |
| `{@ (,b:B)}`, active COMMA | F E `1..4`, C M `4`; nested comma stays pending |
| `{a:A; (\n) b:B}` | S E `4..9`; native nested parentheses, two fields |
| `{a:A]}` | C E `4..5`; actual `}` outside Error |
| `{a:A]` | C E `4..5`, C M `5` |
| `F({a:A])` | C E `6..7`, C M `7`; actual outer Call owns `)` |
| `{a:A] junk}` | C E `4..10`; close-only retry, actual `}` outside Error |
| `{a:A,]`, unclaimed `]` | F M `5`, C E `5..6`, C M `6` |
| `{a:A,]`, inherited `]` | F M `5`, C M `5`; full `]` Item pending |
| `{a:A with tail`, active WITH | C M `4`; full space/word Item pending |
| `{a:A, with tail`, active WITH | F M `5`, C M `5`; full space/word Item pending |
| `{a:A\nwith tail`, active WITH | F M `4`, C M `4`; full newline/word Item pending |

The old two unclaimed-`]` tests must now assert local Close Error/full
consumption, retaining their literal inputs and adding inherited-close
companions. Field-internal boundary tests gain their previously raw outer
Close records. The nested-colon Name Error changes to whole Field Error because
the corrected probe may no longer cross that caller boundary to find a later
colon. Next-head tests gain their previously raw Separator record. None of
these changes removes the original source control or weakens boundary checks.

The new EOF-newline control compares its exit line-entry with the independent
lexical Item control: EOF normalization, not the presence of a physical
newline alone, determines that value. An abstract fence remains a distinct
PhysicalStart boundary. This avoids inventing a lexical contract in a record
test.

Check fresh/frozen/shifted/seeded exact output, native Error ancestry, complete
pending Items and cursor, quoted fence, repeated nested closes, structured PV
reservation ordering, accepted empty/trailing/newline/full-RHS records, and
every record-owned recovery node's typed counterpart. Correct the matrix's
isolated T5a–T5h coverage typo to T5a–T5g; its seven enumerated rows, witnesses
and still-open embedded certification do not change.

### T5f witness correction

The matrix also spells T5f as `R({type T = {a: A,})` but labels its RecordField
Missing as EOF. Under the matrix's `R(p)` expansion the existing `}` actually
closes the named record: that is a valid trailing comma, not a missing field.
Its referenced standalone control in the old Yulang3
`grammar/type_expr.rs::named_record_comma_policy_and_close_recovery_are_typed`
distinguishes accepted `{a: A,}` from incomplete `{a: A,` explicitly. This is a
witness transcription contradiction, not a recovery-equality requirement.

The successor T5f EOF witness is the literal `\ref({type T = {a: A,` with no
closing wrapper punctuation. Its record field slot is Missing at source EOF;
record/block/reference close slots remain independently owned. Retain the old
matrix literal as history and link this correction from its navigation note.
No actual embedded implementation or aggregate T5f proof is certified here.

## Verification and resource budget

M2 primary-only contract audit, implementation and deterministic checks; no
independent review. One scoped pass and at most two repair rounds. Run focused
record controls, known-small full Type and normalized Type, declaration/output/
recovery-output filters, one package check and scoped format/diff checks.
Broad workspace/public certification is deferred. Zero benchmark
samples/processes. Matching stacks allocate only on malformed nested input;
the existing authority probe plus one committed scan is bounded linear work,
not a retained replay/cache. One-token field-head observations remain bounded
per candidate. Existing sealed output and chasa-recover lexical operations
suffice; no owner-specific generic API is added.

## Construction result

Completed 2026-09-08. All named-record-owned Missing/Error sites are typed.
One phase-aware owner loop handles boundaries and required slots; one total
kind-matching run covers malformed whole fields, separators, names and closes.
The old independent field/separator/close raw loops and their two parent raw
Missing helpers were removed. The bounded source probes reuse existing
chasa-recover `token` operations; no new generic API or token allocation was
needed to retain spelling for the caller check.

The pre-write name-probe controls exposed the corresponding handoff risk:
after a nested caller stop the sequence must not reinterpret its colon/comma/
complete head as local. The immediate caller-owned exit fact closes that hole.
Abstract boundary priority also prevents an extra implicit-field Missing at a
fence. Native inherited close, actual outer Call continuation, nested close
cardinality, structured PV ordering and the original accepted inputs pass.

Nine new sequence tests and eight field-internal tests pass. Full Type:
176 passed. Reused the same compiled binary for normalized Type/unmatched head,
TypeDeclaration, output and recovery-output: 95 passed (27 + 39 + 4 + 25).
The final extra nested-caller and real outer-Call controls were then verified
with the 17-test record filter; no implementation changed after the full Type
pass. Package check and scoped rustfmt/diff checks passed. Existing 87 package
and 38 test warnings remain; this gate introduces none.

M2 primary-only, one batched repair and focused follow-up controls; no
independent review or broad workspace/public certification. Zero benchmark
samples/processes. The initial test compilation took 2m24s; a read-only process
sample found one active rustc around 1.8 GiB RSS with available memory, not a
stalled or parallel broad suite. Subsequent focused rebuilds took 38s and 31s.
This observation is environment bookkeeping, not performance certification.

The T5 coverage-label typo and T5f witness contradiction are documented without
closing their aggregate embedded rows. Forall, caller-owned required-Type
Missing, the remaining typed-owner ledger and embedded/header/public cutover
remain open. Task, design index and daily progress are synchronized.
