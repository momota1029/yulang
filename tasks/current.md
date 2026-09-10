# Current task: complete and adopt the successor syntax phase

Updated: 2026-09-09. Branch: `yulang3`; do not modify frozen `main`.

## Objective and current authority

Prioritize syntax-owned public header/root connection and atomic legacy
implementation removal once the entry paths have sufficient validation functionality. Exhaustive
private owner completion is no longer an automatic cutover prerequisite;
deferred rows stay open. Private construction is not itself public cutover.

- `notes/design/2026-09-08-successor-recovery-authority-amendment.md` is the
  current acceptance/recovery authority. Yulang2 is reference evidence only
  for formally accepted input; choose explicit, reasonable successor recovery.
  The local `grammar/` implementation is older Yulang3, not Yulang2.
- Retain accepted syntax, source ownership, caller/fence boundaries,
  effect-free rejection, truthful typed records, structured reservation and
  emitted extent, and successor fresh/frozen/header-full consistency.
- The user authorizes recovery simplification and recommended design changes,
  documentation/environment maintenance, frequent coherent commits, and
  consideration of generally useful `chasa-recover` shorthand.
- The later user instruction explicitly requests subagents. Use only the
  lightest scoped read-only reviewers or one owned implementation worker needed
  for a bounded gate; deterministic verification and honest reporting of review
  scope remain required.
- `notes/design/2026-09-08-successor-public-cutover-priority-amendment.md`
  records the current ordering: build syntax header/root entries, exercise the
  actual public two-phase path, then remove the legacy implementation without fallback.

## Current gate and immediate next action

The user-authorized topology cleanup has no generic internal umbrella.
The concrete `SyntaxIn` in `cursor.rs` borrows the live source, existing
recovery owner and direct Rowan `GreenNodeBuilder`; lexical transactions receive
only an operator-table `LexRecover` view. No mutable diagnostic-owner borrow
escapes to `LexIn`.
`cursor::recovery` owns committed recovery publication and reconciliation.
The former `CstOutput` wrapper and `cst_output/` module are removed under the
Rowan CST-only amendment. Public exports and syntax behavior remain unchanged
in this migration phase. Dated design and daily records retain historical paths;
current source links and test commands name their direct owners.

The standalone `impl` declaration now has the same responsibility boundary as
the approved TAI tail plan: `declaration::impl_decl` owns statement selection,
visibility, the `impl` keyword and the `ImplDeclaration` wrapper, while private
`declaration::impl_tail` owns the post-keyword Type head, description, body,
recovery and successor handoff. This is a behavior-preserving partial Gate 2
extraction, reviewed against the unchanged standalone tests; it neither
activates Type-attached `impl` nor closes the historical owner-spec/AST-direct
parity requirement. The product Draft now identifies that form as approved
authority with successor promotion still pending.

The authoritative expression structural tails contract under
`2026-09-09-successor-expression-structural-tails-draft.md`. It adds no
canonical AST product: `assignment` and `type_annotation` own their distinct
flat CST tails, while `operator_chain` keeps dispatch and rejection. Assignment
uses one-character `=` only after an admitted dynamic LED loses, owns one
inline Expression or indented Statement RHS and terminates the chain. `as`
delegates to full Type with an annotation-specific Missing and Type-owned Error,
then propagates its exact Type exit; it does not re-enter expression scanning
and cannot reinterpret a Type-stopped `+`. M2 implementation, focused tests
and regression review are complete: structural tails 8, dynamic operators 11,
fixed-tail recovery 9, package check, format and diff passed. Benchmark use
was zero. Canonical materialization remains separate and open.

The contextual `RuleExpression` production-entry M2 gate is complete under
`2026-09-05-direct-literal-cone-addendum.md` §§2, 4.2 and 6 / LC-8. Exact
lexical Identifier `rule` plus one brace successor enters the shared RuleBody
from Expression and Pattern; all other successors return unchanged to the
ordinary owner, and registered `rule` word operators remain operators. The
Rule body remains the sole brace/recovery owner before its host tail resumes.
Compiler/recovery review was clean. Regression review established that this
approved exact-form reservation wins over a caller's pending brace stop;
`if rule {a}: body` now records that the Rule expression is the condition and
the later colon/body remain If-owned. Focused entry 7, inherited Rule 26,
package check, format and diff passed; benchmark use was zero. Canonical
materialization and outer Yumark remain separate and open.

The public syntax phase is now split under
`2026-09-09-syntax-phase-topology.md`: `syntax_environment.rs` owns selected
inputs/provenance, `syntax_diagnostic.rs` owns diagnostic data, and
`full_parse.rs` owns their HeaderInfo/root assembly and ParsedFile. The generic
`parse.rs` source is gone; root API remains unchanged. Environment/diagnostic:
5; full parse: 9; public boundary: 8 passed with one existing ignored manual
measurement harness; package/format/diff passed. Benchmark use: zero.

The operator-compilation topology gate is complete under
`2026-09-09-operator-compilation-topology.md`. `operator_table.rs` now owns
only immutable declarations/fixities/sites, mechanical construction, tries,
and matching; `operator_compilation.rs` owns HeaderOperator conversion,
imported/local merge, and conflict collection. Public API, scanner, Pratt
grammar, accepted syntax, and diagnostic contracts are unchanged. Scoped
table/compilation/environment/diagnostic/full-parse/public controls passed 31
tests with one existing manual measurement harness ignored; package/format/diff
passed. Benchmark use: zero.

The source-root statement topology gate is complete under
`2026-09-09-root-statement-topology.md`. `source_file.rs` now owns the Root
product/frozen setup and `root_statement.rs` owns exact source-root statement
progression, operator body handling, root recovery, and concrete header scopes.
Root/header/full-parse/public-boundary/recovery controls passed 63 tests with
one existing manual measurement harness ignored; package/format/diff passed.
Fence-boundary termination remains a separate Yumark prerequisite, not an
incidental change to this mechanical split. The first opaque Root Error
prerequisite is complete: its existing lexical skipper now emits a borrowed
source slice from the entry remainder and consumed byte length, rather than
allocating a copied tail. It preserves all unfenced CST, recovery, origin and
line behavior; it deliberately adds neither a fence parameter nor a cell entry.
The next bounded gate is the fence-aware opaque lexical owner.

After the corrected Role/Impl, Parenthesized newline, and virtual-Colon
controls plus the no-copy preparation, the coherent successor syntax baseline
is green: `cargo test -p yu-syntax --lib -- --test-threads=1` passed 1039
tests, ignored one existing manual measurement harness, and failed none
(1.75s). This is a phase-boundary validation, not evidence that the deferred
Yumark cell/fence owner is complete.

The fence-aware opaque Root Error M2 gate is complete under the parsed-fence
addendum §§3--5/§8. `lexical::opaque_region` owns only continuation after an
already accepted opaque opener; `root_error` remains the typed-record/CST Error
owner. The scanner returns source-backed physical extent and an optional exact
pending boundary Item, never a copied body, parser state, grammar parse,
builder operation, replay or token buffer. Every LF, whole CRLF and physical
EOF through string, interpolation/code, comment, opaque Yumark and nested
fence recursion uses the existing judge. Equivalent prefixes emit ordered
foreign fragments; close/transition facts stay pending. Existing unfenced Root
output/records are exact controls. EOF/BorrowedClose/transition terminate the
nonempty Error without nested literal records; outer Yumark remains the sole
future fence-Missing owner. Compiler/recovery and regression review were clean
after one test-only exact-record repair. Focused matrices passed; full
`yu-syntax` lib passed 1043 with one existing ignored manual harness, package
check, format and diff passed. Static work remains linear in scanned opaque
bytes plus nesting and accepted prefix metadata; the lazy vector/one box
conversion is the approved current-Item bound, so benchmark use is zero.

The boundary-capable root-statement sequence M2 gate is complete. Source root
remains its fixed `None` wrapper and alone emits ordinary EOF leading; the
private sequence returns every fenced close/transition/EOF Item untouched at
frontier zero before layout, recovery or header dispatch. Fence reaches
statement/operator/root-recovery paths and `my`/`lazy` lookahead. Source header
reconciliation remains concrete; fenced state starts with it disabled and
ambient `None`. Compiler/recovery and regression review were clean after two
test-only closure repairs. Full lib passed 1049 with one existing ignored
manual harness, package check, format and diff passed; no benchmark samples.

The private `YmYulangCodeCell` wrapper is now a test-only construction proof:
it drives the real stream through the boundary-capable sequence, emits terminal
body-leading exactly once while the cell remains open, and returns unchanged
facts. It is deliberately not production code: no outer Yumark document owner
exists to reach it, and exposing an unused crate-private wrapper would add
dead-code warnings. The historical injected-item witness remains separate.

The direct Rowan construction phase is active under
`2026-09-09-successor-rowan-cst-only-amendment-draft.md`: AST products,
materializers, event tapes and second output trees are excluded, and
`CstOutput` is removed rather than renamed. The first direct-builder migration
is complete. The next schema/API migration is governed by the Authoritative
`2026-09-09-successor-cst-derived-diagnostics-amendment-draft.md`: parsing
will return only the lossless direct Rowan tree and its selected syntax inputs;
structural `Missing`/`Error`/`Invalid` diagnostics and environment conflicts
will be derived during a frontend CST walk. No parser recovery ledger, frozen
reconciliation, diagnostic array or synthetic Expected node remains after that
migration. Raw malformed source becomes an `Error` token, while an
`Invalid` node appears only for recovery that actually retains nested grammar,
Missing or nested Error children. Expected syntax is specified by the
documented grammar slot.

The Authoritative Error/Invalid topology-ordering addendum selects the bounded
topology-only migration now: ordinary raw fragments are Error tokens and the
two structured owners are Invalid nodes, while recovery records, frozen
reconciliation and public diagnostics remain temporarily unchanged. This M2
construction is complete: focused owner/output controls and the final
single-threaded library run passed 1,070 tests with one existing manual harness
ignored. The sole then-observed failure was the pre-existing `SyntaxKind::Unknown`
discriminant assertion (`231` actual, `229` expected) in an unmodified test.
The full per-slot schema still blocks removal of that temporary machinery. Its
two-layer scaffolding now exists: the Draft internal catalog at
`notes/design/2026-09-10-successor-cst-slot-schema-catalog.md` and the separate
non-authoritative source coverage manifest at
`notes/progress/successor-cst-slot-schema-coverage.md`. Full semantic mapping,
ordered schemas and independent audit remain open; this record-only step made
no parser, API, test or benchmark change.
The first bounded catalog row, TypeCall's terminal close phase, is now mapped
and independently audited from its existing Authoritative close-node and
residual-policy amendments. Its TypeCallClose Error/Missing grouping, leading
and boundary ownership, and direct source links are complete only for that
slot; argument, separator and other TypeCall rows remain open.
The user approved a bounded transition-vocabulary convention for catalog
documentation: every mapped row records its owner transition or handoff from
entry/priority through consumed CST extent to continuation and diagnostic-slot
witness. It is explanatory notation only, not parser state/API, a generic
recovery library, or a token-global `)`/`@` policy; Error spelling is never
read or relexed, and no generic wrapper or Invalid expansion follows. TypeCall
demonstrates that identical token spelling must be classified by the owning
slot and continuation. The catalog itself remains Draft and globally open.
RecordPattern's structured separator Invalid now has a user-selected
CST-visible discriminator under
`notes/design/2026-09-10-successor-record-pattern-separator-slot.md`:
`RecordPatternSeparator` wraps only the separator-phase Invalid, while the
item-phase Invalid remains direct. Private construction and M2 review are
complete. Both bounded phase rows are now catalog-mapped and independently
audited: the direct item Invalid projects `Identifier`, while the transparent
separator wrapper selects `DelimitedSequenceSeparator`. The preceding raw Error
and every other RecordPattern sequence/Pattern row remain unresolved; only
separator-phase CST topology changed, with parser diagnostic/API migration
still pending.
The direct-Rowan schema audit exposed a raw-Error collision for RecordPattern:
a foreign close and an Item error can have the same old tree shape but require
distinct expected slots. The user-approved
`2026-09-10-successor-record-pattern-foreign-close-slot-draft.md` authorizes
the bounded repair: append `RecordPatternForeignClose`, wrapping only the
Error leaves emitted for one consumed RecordPattern foreign close. Direct raw
Item and Separator groups retain their existing phase-selected slots. M2
construction, focused proof and closure review are complete. The recovery
ledger remains blocked on the complete global schema.
Direct Rowan evidence now also proves the expression-delimiter
collision: `(@)`, `(;)` and `(])` each have direct
`ParenthesizedExpression(LParen, Error-token, RParen)` at the same ranges but
retain respectively Expression, Separator and Close expectations. This is a
schema gap, not a parser defect. The user-approved Authoritative
`2026-09-10-successor-expression-delimited-raw-slot-draft.md` selects shared
`ExpressionDelimitedSeparator` and `ExpressionDelimitedForeignClose` wrappers
for the five expression-delimited owners only. Direct Item Error and
ProjectionRecord spread-RHS Error remain direct. The 15-case current-contract
matrix proves every owner × Item/Separator/foreign-close role before topology
construction. M2 implementation is the immediate action; do not inspect Error
spelling, collapse expectations, or alter current records.

That observed failure was subsequently traced to `f14d9a0a` inserting
`AssignmentTail` and `TypeAnnotationTail` before established kinds. The
2026-09-10 repair restores the pre-insertion values through
`RuleLiteralColon = 267`, retains the already-committed `Invalid = 270` and
`TypeCallClose = 271`, and assigns the two tails `272` and `273`; unused raw
values `268` and `269` remain unknown. The earlier result is historical
evidence, not proof that the `229` contract was stale.

The direct-Rowan design is independently reviewed. Its bounded first migration
removes `CstOutput` while preserving the current tree topology, so direct
builder/recovery ownership, frozen reconciliation and effect-free lexical
probes have an isolated regression boundary. The following schema migration
makes `Error` token-only and adds node-only `Invalid`: all raw-recovery Item
fragments, including its interior trivia and quote-prefix fragments, become
adjacent `Error` leaves; already-emitted and retry/boundary leading remain with
their owner. `Invalid` is limited to the two reviewed structured recovery
owners. The reviewed supersession and notation are user-approved;
direct-builder construction has passed its focused implementation controls and
independent delta review. The sealed cursor removes the generic-input
reconstruction route: `Recover` has no `Recoverable` implementation, production
construction/finalization is cursor-private. Header reconciliation is a
temporary direct-builder control and is retired by the amendment. The
final focused cursor/recovery/header/root/
lexical/literal/slot set passed 175 tests. Full-package behavior certification
ran once after the topology migration: 1,070 tests passed and the only failure
was the pre-existing `SyntaxKind::Unknown` discriminant assertion (`231`
actual, `229` expected) in an unmodified file. Its fix is outside this
direct-Rowan gate. The complete per-slot diagnostic schema and parser-ledger
retirement remain open.
`syntax-reference` is rebuilt around
the same XML-like Rowan node notation, grammar and recovery placement; parser
internals, commits, fixtures and AST/direct parity leave that public reference.
The reviewed first English/Japanese vertical slice now defines Rowan notation
and Root/header/diagnostic ownership. It distinguishes implemented direct
Rowan construction from the pending Error-token, Invalid-node and CST-derived
diagnostic migration, and labels unconverted construct pages as legacy
implementation material. Exact reversible escaping for XML-like `text`
attributes is defined by the text-attribute escaping addendum: canonical
backslash/control escapes preserve CRLF, and the notation uses no XML entities.
The paired recovery-topology pages now specify the implemented direct `Error`
leaf and restricted `Invalid` node shape, raw-fragment/leading ownership and
the two structured owners. They intentionally defer construct slot schemas and
the later CST-derived public diagnostic result. Both language books build with
`mdbook v0.5.4`.
The first construct-level slot Draft, AssignmentTail's direct inline RHS, now
has direct Rowan evidence for child order, leading, Missing, Error grouping,
retry and nested ownership. The user approved this direct-inline slice as
Authoritative, and its paired EN/JA public reference pages are reconstructed
from it. The indented RHS and complete inventory stay open.
The dedicated FieldTail/PathTail name-slot Draft is preflighted against the
existing recovery authority and has direct CST proof; user promotion remains
open.
The outer StringLiteral terminator has a preflighted Draft. Its isolated
interpolation-EOF evidence retains trailing spaces in the pending EOF Item;
SourceRoot is the terminal-leading owner. Full-Root losslessness evidence is
complete; user promotion remains required before public reconstruction.
Its bounded catalog row now records only the final outer terminator phase,
with opener-selected normal/heredoc mode. The CST Missing for the isolated
interpolation-EOF witness is `3..3`; its temporary shifted recovery record at
`105..105` is evidence only, never a schema or ledger fact. The catalog row is
evidence-complete Draft and is not promoted.
The dedicated Rule-slot Draft is preflighted and its direct CST proof is
complete; user promotion remains open. Its six bounded catalog rows now
cover only RuleBody close, opener-selected RuleItem parenthesis close,
RuleCapture RHS, RuleField name, RulePath name, and repeated RuleSequence Item
Error. They retain Error-to-valid versus terminal Error-to-Missing Capture
facts and direct Rule publisher links. The three Rule ExpressionList caller
phases now have a bounded Draft with direct non-fence evidence: its
caller-owned delimiters, content-only Item/Separator phases,
terminal/missing-close paths, and LF/CRLF insertion ranges are directly
witnessed in Rowan. The current protected-fence harness ends the Green tree
before the pending Item, so completed caller fence CST/range proof, diagnostic
projection, and catalog mapping remain open. The newline callback remains
outside the publisher census as source-navigation evidence rather than a
ledger substitute.
Interpolation/lazy/RuleLiteral children, String, and Virtual remain delegated
or unmapped.
The bounded StringInterpolationBody root-style statement-sequence row is now
mapped as Draft: nested `Statement(Missing)` owns a required starter, while
direct body Missing and raw Error own separator and starter expectations
respectively. Comma and semicolon end leading absorption but do not terminate
the sequence, so a repeated separator first produces the next statement's
Missing. Nested Statement contexts, interpolation close and string terminator
remain delegated; user promotion remains open.
The TypePathTail segment Draft and direct CST evidence are complete; its
post-Error fence boundary repair is reviewed. Its bounded catalog row is now
mapped: it distinguishes Type continuation from expression PathTail, including
continuation-qualified newline trivia versus outer TypeApply horizontal handoff.
User promotion and every other Type context remain open.
The LeadingEffectTypeHead row is likewise mapped as a bounded Draft: its direct
head Missing is ordered after a nested BracketRow close Missing even at the
same offset, while terminal Error EOF trivia remains native TypeExpression
content outside Error. BracketRow, primary children, and all other Type slots
remain separate.
The BracketRow required-arrow continuation is mapped separately: an incomplete
row emits its Arrow Missing unconditionally and returns its existing Item
unchanged, while a completed row alone proceeds to Arrow/RHS classification.
Actual-arrow RHS and BracketRow internals remain delegated.
The actual-arrow RHS itself is now mapped as its own Draft suffix. Its
diagnostic range is always the direct Rowan Missing/Error range, not a pending
fence coordinate; post-Error retry admits same-line and deeper-newline RHS
primaries, while shallow/equal newline and protected boundaries hand off.
Expression FieldTail and PathTail are now mapped as separate bounded Draft rows:
their introducer trivia remains direct tail content, Path's conditional leading
does not consume protected Item leading, and an Error ends its tail rather than
retrying a later name. They remain distinct from TypePathTail.
The Authoritative AssignmentTail direct-inline RHS is mapped separately; its
indented Statement branch remains delegated and open.
The bounded ProjectionRecordSpreadItem RHS is mapped as Draft: the direct
spread node distinguishes its Missing and raw Error leaves from parent record
items, separators and close slots. A lexical Error run is not reconstructed as
one parser record: CST adjacency determines its future Error groups, while
native initial/retry/boundary leading remains in its documented direct owner.
Every other record-projection phase and nested expression row remains open.
The actual-arrow TypeArrowTail RHS Draft is preflighted and has direct CST
proof. Its post-Error shallow-newline admission now follows the existing
authority; user promotion remains open.
The BracketRow-selected required-arrow continuation Draft is preflighted and
has direct CST proof; user promotion remains open.
The LeadingEffectTypeHead Draft is preflighted and has direct CST proof; user
promotion remains open.
The user selected the TypeCall close-slot structural boundary under
`2026-09-10-successor-typecall-close-slot-node.md`: terminal Call close
construction will use `TypeCallClose`, separating close Error from direct
CallArgument Error without relexing or a ledger. Its required generic-fallback
proof found a reachable `T(A@)` contradiction: Call currently returns an
unclassified post-argument Item without any close publication. The direct CST/
pending-Item witness is committed. The user selected policy A under
`2026-09-10-successor-typecall-close-residual-policy.md`: the residual enters
terminal close recovery after all existing Call dispatch declines it. The
private TypeCallClose construction is complete with direct Rowan evidence;
public reference reconstruction and CST diagnostic interpretation remain open.

The Cast PatternIntroducer gate is complete under
`2026-09-09-successor-cast-pattern-introducer-current-item-recovery.md`.
Its Missing/Error sites now publish the existing Cast role with the required
open-parenthesis expectation; malformed retry to a bare Pattern no longer
duplicates Missing after Error. The sealed Error capability keeps nonempty
same-line EOF leading in the Error and extends its record/fact extent with it;
empty/newline EOF leading remains outside. Pattern value/close, target and
body remain separate open Cast owners. Cast: 12; direct Pattern/required-Type/
recovery-output: 84; package/format/diff passed. Benchmark use: zero.

The immediately following Cast Pattern absence gate is complete under
`2026-09-09-successor-cast-pattern-current-item-recovery.md`; local close and
colon/form handoff use the existing transition, while malformed Pattern input
remains Pattern-owned. Cast 13; direct cone 162; package/format/diff passed.

Cast Pattern's local closing-parenthesis gate is complete under
`2026-09-09-successor-cast-pattern-close-current-item-recovery.md`. Its two
Missing paths and bounded malformed run publish `CastPattern` closing-delimiter
records; local close keeps priority, outer boundaries remain unread, and Error
does not add a second Missing. Nonempty same-line EOF leading extends the Error
node, record, and fact together. Cast 14; direct cone 162; package/format/diff
passed. Benchmark use: zero.

Cast TargetIntroducer is complete under
`2026-09-09-successor-cast-target-introducer-current-item-recovery.md`. Its
four Missing paths and bounded malformed run publish the existing typed role
with a colon expectation. Colon and reusable Type retries remain distinct;
form and protected boundaries remain unread; Error does not add a second
TargetIntroducer Missing. Cast 16; direct cone 358; package/format/diff passed.
Benchmark use: zero.

Cast BodyIntroducer is complete under
`2026-09-09-successor-cast-body-introducer-current-item-recovery.md`. Its
Missing/Error sites now publish the existing typed role with a semicolon
expectation. The lexical-only form-punctuation scan keeps exact `;` and `=`
outside Error for the existing bodyless/body form owners; malformed `==` stays
rejected. Protected boundaries remain unread, Error does not cascade a Body
Missing, and same-line EOF leading has the selected Cast-owned extent. Cast
19; direct Pattern/Type/normalized/recovery-output 358; package/format/diff
passed. Benchmark use: zero.

Post-equals Cast Body is complete under
`2026-09-09-successor-cast-body-current-item-recovery.md`. Its three raw
publishers now use `Declaration(Cast(Body))` with an Expression expectation;
the deeper indented path remains the existing `Cast(IndentedStatement)` child.
Inline Error is lexical-only and does not cascade a Body Missing. Same-line EOF
leading stays Cast-owned, while LF/CRLF and protected boundary leading remain
pending. The now-unreferenced generic raw Missing helper was removed. Cast 22;
expression recovery 6; normalized 83; recovery-output 25; package/format/diff
passed. A later owner-contract audit corrected the stale Role/Impl statement
dispatch assertion that had exposed the unrelated failure. Benchmark use: zero.

The complete Cast owner is now audited: PatternIntroducer, Pattern, its local
close, TargetIntroducer, delegated TargetType, BodyIntroducer, Body, and
delegated IndentedStatement have typed publication or their established child
owner. No raw Cast Missing/Error publisher remains, and the stale
`CastRole::Pattern` dead-code exemption is gone. The typed-recovery ledger now
marks the whole Cast phase C; next recovery work requires a refreshed raw-site
inventory rather than a guessed nearby declaration gate.

A strict production publisher inventory now finds no untyped Missing/Error
publisher. The remaining manual Rule ExpressionList newline callback commits
its exact `ExpressionList(Item)` record in the same callback, so it is not a
raw recovery escape. This M0 cleanup removed stale dead-code exemptions from
the live For, If, and CaseLike recovery roles only; deliberately deferred role
vocabulary remains annotated. Package check, format, and diff passed.

The ordinary statement dispatch control now separately follows the approved
Role and Impl required-Type recovery contracts: neither owner claims `=` as a
head boundary, so its malformed head recovery remains lossless rather than
returning Equals pending. Only the stale test expectation changed; focused
statement dispatch, format, and diff checks passed.

The shared Call/Parenthesized/EffectRow ordinary-horizontal correction is
complete under the recovery authority amendment §4 and the retained P/E
addenda. Selected P/E/numeric-Call structured Error controls cover exact
records, fresh/frozen reconciliation, shifted origins, native outer closes,
prefix/recursive reservations and outer path continuation. Type tests: 124
passed; output: 4 passed; recovery output: 25 passed; package check passed.

The follow-up contextual-Type correction is complete. Same-line contextual
names remain accepted PathSegments and fresh Call arguments suspend the outer
declaration boundary; physical-newline contextual Items remain outer-owned.
Stale malformed controls now follow the approved horizontal owner and selected
streaming-boundary rules rather than old-parser recovery output. Type tests:
126 passed; TypeDeclaration: 39 passed; output: 4 passed; recovery output: 25
passed; package check passed.

The PV-owned typed migration is also complete under
`2026-09-08-successor-pv-current-item-recovery.md`. Every PV-owned recovery
node publishes its typed record; malformed tag/payload runs share one forward
operation and preserve explicit caller Items. Wrong-kind heads retain tight
Type tails inside one structured Error. Type tests: 134 passed; declaration,
output/RB and package checks remain green.

Parenthesized/EffectRow-owned construction is complete under
`2026-09-08-successor-pe-current-item-recovery.md`. Item, separator and close
sites now publish typed records; Error retries emit leading at the P/E owner,
preserve complete caller/fence Items, and recover unclaimed closes locally.
EffectRow activates only the approved OuterTypeApply provenance. Type tests:
141 passed; declaration: 39; output: 4; recovery output: 25; package check
passed. Call and structured PV contracts remain green.

BracketRow-owned Item/Separator/Close construction is complete under
`2026-09-08-successor-bracket-row-current-item-recovery.md`. The shared
delimiter module has no raw Error/Missing constructors; P/E/B share the total
Item-error scan, B preserves its close-only retry and protects full caller/outer
Items. Type tests: 147; declaration: 39; output: 4; recovery output: 25; package
check passed.

BracketRowArrow construction is complete under
`2026-09-08-successor-bracket-arrow-current-item-recovery.md`. Its missing
and malformed sites are typed, malformed content retries an arrow/RHS without
a same-slot Missing cascade, and incomplete-row handoff preserves the separate
arrow slot. Type tests: 152; declaration: 39; output: 4; recovery output: 25;
package check passed.

LeadingEffectTypeHead construction is complete under
`2026-09-08-successor-leading-row-head-current-item-recovery.md`. One total
nested-Item Error run replaces the ordinary speculative and dedicated fenced
balanced-suffix scanners. Every head slot is typed; complete caller/newline/
fence Items remain pending. Type tests: 159; normalized Type/unmatched head:
27; declaration: 39; output: 4; recovery output: 25; package check passed.
The matrix's T7a/T7b EffectRow/leading-row spelling error has a recorded narrow
correction, not an embedded-certification claim.

Named-record field-internal construction is complete under
`2026-09-08-successor-record-field-current-item-recovery.md`: Name, Colon and
Type records, shared forward colon/RHS recovery and exact field-colon ownership.
The accepted empty-trivia nested record `{a:{b:B}}` now parses correctly;
actual PV RHS remains distinct. Type tests: 167; normalized Type/unmatched head:
27; declaration: 39; output: 4; recovery output: 25; package check passed.

Named-record whole-field, separator and close construction is complete under
`2026-09-08-successor-record-sequence-current-item-recovery.md`. A phase-aware
owner loop and one typed kind-matching run replace the raw recovery loops.
The malformed-name probe and immediate handoff preserve nested caller Items;
all record-owned recovery nodes are typed. Nine sequence tests pass, full
Type: 176; normalized Type/unmatched head: 27; declaration: 39; output: 4;
recovery output: 25; package check passed. The T5f EOF witness transcription
contradiction is corrected in the design without claiming embedded proof.

Forall-owned construction is complete under
`2026-09-08-successor-forall-current-item-recovery.md`: phase-owned forward
Errors replace the role lookahead, with typed Binder/Boundary/Colon/Body and
exact mandatory-colon ownership. Ten new typed tests passed; full Type: 186;
normalized Type/unmatched head: 27; declaration: 39; output: 4; recovery
output: 25; package check passed. No repair round was needed.

The shared required-Type Missing helper is implemented under
`2026-09-08-successor-required-type-missing-roles.md`. Production callers
explicitly select their own missing-slot role; malformed and nested Type
records remain unchanged. Type: 191 passed; package/format/diff checks passed.
The Type/PV implementation now has no raw recovery constructors; the remaining
SCC/global RB ledger and calling owners' bypass sites are still open.

Wider caller controls are now green under
`2026-09-08-successor-type-caller-conformance.md`: all five failures were traced
to stale expectations against the already-approved T3, inherited Type-ML, P/E
horizontal and record-field rules. Every original literal remains covered;
accepted tight-arrow/Call and nonhorizontal caller controls were added. The
expanded serial owner/output filters pass 432, with no failures or skips.

The tuple-field nonprogress path is fixed under
`2026-09-08-successor-required-type-equals-ownership.md`. An exact `=` is a Type
boundary only when the caller owns it; Pattern now forwards that ownership
explicitly. No field-loop workaround or new context API was needed. A bounded
single-callee test failed before and passed after the fix; capped tuple tests
and all 470 expanded owner/output tests pass. Package/format/diff checks pass.

The Type/PV callsite inventory is complete in
`notes/progress/successor-typed-recovery-ledger.md`: every publication helper,
all 28 TypeRole names (including the ApplyArgument non-recovery proof), close
owners and local RB controls are mapped. Matrix D4e now has an explicit
SD-T role correction without an embedded-certification claim. T3's stale
construction-suspension header is synchronized with its approved successor.

Pattern primary/symbol/alias/alternation typed construction is complete under
`2026-09-08-successor-pattern-primary-current-item-recovery.md`. Retry-leading
now belongs outside Error, malformed alias retry respects the layout/IN
boundary, and the RHS slot is explicitly AlternationRhs. No raw recovery
constructor remains in `pattern.rs`. All 33 Pattern tests and 477 expanded
owner/output tests and package/format/diff checks pass; the same accumulating
ledger includes its sites/RB controls. This is an O3b substep, not an
independently completed Pattern owner.

Pattern delimiter Missing/child-role publication is also complete under
`2026-09-08-successor-pattern-delimited-slot-publication.md`: five explicit
element/spread/nested roles, separator Missing, three close-Missing owners
and one guarded RecordFieldName non-recovery proof. Existing CST expectations
are unchanged. Pattern 40 and expanded owner/output 484 pass, along with
package/format/diff checks.

Pattern sequence/close Error construction is complete under
`2026-09-08-successor-pattern-sequence-current-item-recovery.md`: maximal
lexical runs, native wrong-close records and two scoped Record structured
roles. Invalid nested literals retain their own closes; accepted layout
literal elements now share canonical admission and maximal opener Items.
No raw Pattern Error remains. Pattern 48, expanded owner/output/literal/
normalized-Pattern 533, package/format/diff checks pass; one repair bundle.

Pattern default-Expression Missing construction is complete under
`2026-09-08-successor-pattern-default-expression-publication.md`: typed
RecordDefaultExpression, the required OperatorChain wrapper, and explicit
caller-close preservation in both field forms. There are now zero raw
Pattern-owned recovery constructors. Pattern 54, expanded related set 539,
package/format/diff checks pass. The exact-Equals lexical contract is unchanged;
rejected quote-adjacent sources remain covered separately from accepted defaults.

Current gate: O3b SCC construction. The required-operand role/boundary gate in
`2026-09-08-successor-expression-operand-current-item-recovery.md` is now
implemented: the saved ` ]` witness is back in the build, the kernel publishes
typed Missing/Error records through its explicit caller role, and For's bypass
uses the same helper. Ordinary and sealed Error paths share one total lexical
Item scan. The focused expression-recovery, operator, If, CaseLike and For
filters plus `cargo check -p yu-syntax` pass; joint certification is still open.

The shared Expression delimiter gate in
`2026-09-08-successor-expression-delimited-current-item-recovery.md` is also
implemented. Parenthesized, Call, Index and Projection owners now select typed
Item/Separator/close roles through one finite descriptor. Close-only inherited
capabilities preserve nested caller closes without leaking ordinary caller
stops. The phase loop publishes maximal lexical Errors, records record-spread
RHS recovery, and makes Parenthesized semicolon a local Separator Error. New
fresh/frozen tests: 9; owners 23; tails 14; normalized 83; recovery output 25;
package check/format/diff pass. Specification and delta-regression audits found
no blocker. Colon/With remains a separate owner.

The Field/Path fixed-tail gate in
`2026-09-08-successor-expression-fixed-tail-current-item-recovery.md` is
implemented. FieldName/PathSegment now publish typed Identifier records; Error
runs are sealed lexical-only, Path preserves sigil retry Items and active
caller stops, and lone colon remains outer-owned. Focused recovery tests: 9;
tails 14; normalized 83; recovery output 25; package check/format/diff pass.
Specification and regression review found one frozen-cursor test-evidence gap,
closed by one bounded repair and delta review. No public dispatch changed.

The Colon/With inline gate in
`2026-09-08-successor-expression-colon-with-inline-current-item-recovery.md`
is implemented. Inline Rhs/InlineArgument and Introducer/Body slots publish
typed records; With now shares canonical literal-first Statement scanning with
its sealed retry. The focused filter passes 9; tails 14; normalized 83;
recovery output 25; package/format/diff pass. Spec/regression reviews found no
scoped defect. The pre-existing `my role = value` Statement assertion still
fails identically at baseline `de8e77f3`, so it remains unchanged.

The shared indented Statement recovery-role transport in
`2026-09-08-successor-expression-indented-statement-role-transport.md` is
implemented. Every direct indented caller now passes its finite existing role;
block-entry/child-slot Missing and sealed lexical Error records are typed, and
close/abstract-boundary handoff is protected. Focused recovery: 7; direct
caller/owner/output set: 227 (with the recorded baseline visibility-collision
test excluded); actual For: 12; package/format/diff pass. Specification/recovery
and regression audits passed. No benchmark process was used.

The current-depth Colon layout outer-sequence correction in
`2026-09-08-successor-expression-colon-layout-sequence-context.md` is
implemented. A private by-value owner context replaces comma-stop inference;
it covers the finite Expression/Statement, Virtual, RecordPattern-default and
Rule-list bridges. Ownerless Colon owns comma/qualifying newline arguments;
outer-owned Colon returns the whole boundary. Focused Colon: 12; Rule: 1;
literal/Yumark/Yumark-cell: 35/14/5; package/format/diff pass. The related
cone then had a separately reproduced `(a +\nb)` operator mismatch; its stale
delimiter expectation was later corrected under the approved owner contract.
Spec/recovery and regression delta audits passed. No benchmark process was used.

The non-Rule StringLiteral gate in
`2026-09-08-successor-string-literal-current-item-recovery.md` is implemented.
Terminator, escape and interpolation boundary sites publish six existing typed
Literal roles; UnicodeHex uses one sealed lexical Error and Virtual child
recovery remains separate. Focused: 8; literal/Pattern/Rule/Virtual/normalized/
recovery-output: 35/54/26/9/83/25; package/format/diff pass. Specification and
regression reviews passed. No benchmark process was used.

The VirtualStatementBlock gate in
`2026-09-08-successor-virtual-statement-current-item-recovery.md` is
implemented. Its three raw sites now publish existing Statement Starter /
Separator records: required Statement, missing inter-Statement separator and
one maximal lexical Statement Error. Initial/internal Error leading remains
owned by that Error; retry/boundary leading and borrowed `}` remain pending for
the existing sequence/Literal owners. Fresh/shifted/frozen/seeded, UTF-8,
foreign-prefix, protected boundary and caller controls pass. The exact `"%{,`
literal record order is now Virtual child, interpolation close, terminator;
the pre-write specification audit derives that addition without changing CST
topology. M2 compiler/recovery and regression review found no production defect;
one caller-evidence repair adds actual Expression/Pattern/Rule string paths.
Yumark production convergence and its AST-product decision remain separate.

The If arm gate in `2026-09-08-successor-if-current-item-recovery.md` is
implemented. BodyIntroducer Missing now expects Colon; If/Elsif and Else inline
slots retain distinct Body/ElseBody Missing/Error records through a finite role
transport. The Error scan is sealed lexical-only and preserves existing leading,
boundary and retry handoff. A missing Condition suppresses only the absent
introducer path; after an actual colon, a separate Body slot remains required,
so `if :` and `if : @` publish Condition before Body recovery. The current
Condition boundary flag and indented Statement role remain unchanged. M2
compiler/recovery review found and closed that exact scope clarification;
regression review added actual delimiter-close and nested-dedent caller
evidence. Focused checks, package check, format and diff pass with zero
benchmark samples/processes. CaseLike remains a separate open owner.

The CaseLike structural gate in
`2026-09-08-successor-case-like-structural-current-item-recovery.md` is
implemented. Block and same-or-shallower Arm publish typed records; first arm
Pattern and Catch handler Pattern enter the existing Pattern kernel once with
their finite CaseLike role. Protected newline/close/fence Items now remain
pending at missing Block, while EOF leading remains Block-owned. Nested Pattern
and Type roles remain native. E12b/c/d/k exact fresh/shifted/frozen/seeded,
UTF-8/CRLF/fence, outer delimiter and following-statement controls pass.
Compiler/recovery and regression reviews found no defect. Arrow/Body, arm
Separator and Catch-close recovery remain separate open CaseLike owners.

The Rule DSL literal gate in
`2026-09-08-successor-rule-literal-current-item-recovery.md` is implemented.
Ten Literal roles now publish typed records; Body/Paren newline stops precede
admission, and EOF-leading Missing anchors at successor. Rule: 35; literal:
35; normalized/recovery-output: 83/25; package/format/diff pass. Specification
and regression delta audits passed. No benchmark process was used.

The Rule ExpressionList gate in
`2026-09-08-successor-rule-expression-list-current-item-recovery.md` is
implemented. Dedicated Item/Separator and exact Parenthesis/Bracket close roles
now cover Rule bracket atoms, calls and indexes, while one-Item lexical Errors
and protected terminal Items remain unchanged. Repeated newline Item Missing
anchors use one coordinate-aware leading-prefix emission; the static audit
proved linear leading/fragment work without a benchmark. Rule: 40; focused
records: 5; recovery-output: 25; package/format/diff pass. Independent
specification/recovery and regression audits passed.

The braced canonical Statement sequence gate in
`2026-09-08-successor-braced-statement-sequence-current-item-recovery.md` is
implemented. Existing Statement/Separator/local-brace-close roles now publish
typed records; nonlocal closes stay protected. One repair makes newline-leading
comma/semicolon advance into the separator phase, and the old local-`]` test now
asserts the authorized handoff. Braced: 7; tails: 14; Act/For/Impl/Mod/Role:
15/12/11/9/15; package/format/diff pass. Specification/recovery and regression
delta audits passed; no benchmark process was used.

The Derives gate in `2026-09-08-successor-derives-current-item-recovery.md`
is implemented. Existing RoleReference/ViaTarget records now publish typed
output, and ViaTarget recovery returns protected contextual/newline Items before
identifier retry. Derives: 52; Type: 196; package/format/diff pass; M1
specification review passed. No benchmark process was used.

The declaration Variant gate in
`2026-09-08-successor-declaration-variant-current-item-recovery.md` is
implemented. Existing Item/Name/Separator/close roles now publish typed output;
retry leading is outside Error and terminal roles follow the lexical exit. One
repair added child ownership/effect-free evidence and aligned the authorized
trailing `| with` missing count. Variant/Enum/Error: 23/17/12; package/format/
diff pass; specification/regression delta audits passed.

The Binding gate in `2026-09-08-successor-binding-current-item-recovery.md`
is implemented. Binding now transports its initial Target role through Pattern
only for that required slot; Body publishes typed Missing/Error with lexical
retry and protected handoff. Binding/Pattern/indented/recovery-output:
11/54/7/25; package/format/diff pass; independent audits passed.

The declaration Companion gate in
`2026-09-08-successor-declaration-companion-current-item-recovery.md` is
implemented. All shared introducer/body/item/separator/close records are typed;
the selected colon-only Introducer expectation and protected retry leading are
covered across Struct/Type/Enum/Error/Act callers. Companion: 28; package/
format/diff and specification/regression audits passed.

The Struct header gate in
`2026-09-08-successor-struct-header-current-item-recovery.md` is implemented.
Name and BodyIntroducer now publish typed records with the existing ordered
starter union; header EOF/protected boundary ownership is explicit. Struct 28,
normalized Struct 4, package/format/diff and independent delta audits passed.

The Mod gate in `2026-09-08-successor-mod-current-item-recovery.md` is
implemented. Name/TestName/BodyIntroducer/Body now publish typed records with
sealed lexical retry and protected current-Item handoff. Only the first `test`
is a marker; the second name remains an Identifier. Mod: 13; indented: 7;
normalized: 83; package/format/diff and independent specification/regression
audits passed. The accepted test-only repair pins fresh/frozen boundary
payload, leading, line entry, suffix and fence coordinates.

The Role gate in `2026-09-08-successor-role-current-item-recovery.md` is
implemented. BodyIntroducer and inline Body now publish typed records with the
full ordered body-starter union and protected current-Item handoff; existing
Head Type and braced/indented/canonical Statement child ownership remains
unchanged. Role: 18; output: 4; package/format/diff and independent
specification/regression audits passed. The recorded `my role = value`
Statement baseline remains unrelated.

The Impl gate in `2026-09-08-successor-impl-current-item-recovery.md` is
implemented. BodyIntroducer and inline Body now publish typed recovery while
the first colon remains Description and the second colon is the Body phase.
Impl: 16; required Type: 5; indented/braced/normalized/output: 7/7/83/4;
package/format/diff and independent audits passed. The CRLF boundary repair
preserves shallow-newline current-Item handoff in fresh/frozen output.

The Act gate in `2026-09-08-successor-act-current-item-recovery.md` is
implemented. BodyIntroducer Error and inline Body now publish typed records;
bodyless terminal success remains recovery-free and attachment phases remain
unchanged. Act: 21; companion/indented/virtual/output: 23/7/9/4; package/
format/diff and independent audits passed. D9c's close-boundary zero-recovery
contract is pinned fresh/frozen.

Public-cutover foundations are implemented under
`2026-09-08-successor-public-cutover-priority-amendment.md`. HeaderInfo retains
private source identity and `parse_file` rejects a distinct source before
construction; scoped header reconciliation prevents full-only records from
consuming later frozen header IDs. The public syntax entry, public integration
and atomic legacy removal are complete.

The private Header/Root entry is implemented. Header discovery shares
Use and OperatorHeader construction, projects imports atomically, preserves
exact opaque-region boundaries and retains records for later reconciliation.
Root owns direct top-level topology, separators, pending/End handoff, scoped
header publication, and lexical delimiter-aware recovery. The root construction
review found and repaired binding-vs-operator prefix precedence and initial
indentation admission before closure. Header/Use/OperatorHeader/Root focused
filters pass 9/11/5/11; specification and regression review passed. At that
private checkpoint, HeaderInfo record transport, public adapter,
package/workspace validation and legacy deletion remained open.

The public adapter is now connected without fallback: `scan_header` constructs
syntax facts/records and `parse_file` passes the retained frozen header record
slice into `source_file` before diagnostics and conflict construction. Public
pair tests cover UTF-8/CRLF, header/full interleaving, imported/local conflict
provenance and fence recovery/continuation. A public fence fixture exposed and
repaired raw rejected-operator emission in Root Error. The accepted Yumark NUD
owner remains open; its current public proof is recovery/continuation only.
Final `yu-syntax`/workspace validation and atomic legacy implementation removal are
complete.

The first full successor-only lib run after removing the legacy tree passed
1057 tests with 3 failures and 1 ignored. At that checkpoint, two were the
recorded `my role = value` and `(a +\nb)` baselines. The Role assertion was
later corrected as stale by the approved owner contract, and the operator
assertion was later corrected by the approved delimiter contract. The third,
`virtual_colon_errors_keep_close_eof_and_quoted_fence_records_frozen`, was
reproduced unchanged on detached pre-deletion `62e77291` (3 records versus
its stale expected 1); its exact parent-record assertion was later corrected.
It was an unrelated pre-cutover control mismatch, not a deletion regression.
Syntax-reference paths were historicalized and the final deletion review passed
before `dfa481c4`.

Next, continue deferred Statement/declaration typed-recovery dependencies and
the accepted Yumark NUD/frame-pop owner. Those remain separate from the
completed public cutover; retain the current acceptance contracts and
effect-free optional entry. No benchmark sample/process has been used.
The old eighth-terminal proposal is not a required prerequisite. Public
dispatch is successor-only; the legacy implementation tree has been removed.

Post-cutover cleanup is complete. The inactive chasa cursor/scanner/CST stack
(`input.rs`, `sink.rs`, and `scan/**`) is gone; `recovery_record.rs` now owns
the typed recovery vocabulary; and the unchanged dynamic-operator judge is in
`lexical/operator_scan.rs`. The removed bridge had no public consumer. Test-only
seams live under `tests/`, about 1,400 further inactive private lines
are removed, and no module-wide `dead_code` suppression remains. The residual
annotations are variant/field/method-local contracts for retained Deferred,
ambient, pending-boundary, Rule and fence vocabulary. Production/test checks,
public pairs, focused recovery controls and the unrelated workspace check pass
with zero warnings; known unrelated full-lib baselines remain untouched.

## Syntax responsibility reconstitution

The user has directed a role-based reconstruction of the private syntax
implementation, not a cosmetic `rewrite` rename. This is a behavior-preserving topology
gate: preserve public `scan_header`/`parse_file`, accepted and malformed CST,
committed-recovery order and frozen reconciliation, exact Item/leading/source
handoff, and all existing source literals and semantic assertions.

The target separates lexical input (Item/current-Item/scanning/stops/fence),
committed output and emission, cursor state, expression policy, statement
admission, declaration families, and family-owned test suites. Extract shared
handoff, coordinate and lexical-stop operations from the Expression owner;
retain required-operand policy, NUD admission and tail control under
Expression. Do not add a generic `core`, `common`, `utils`, aggregate context,
or widened recovery capability. Item retains once-only leading emission and
the sealed Error-run/output protocol remains private.

The review also found a distinct existing contract defect: the For inline-body
caller selects `ForStatement(Body)`, but the common required-operand draft
hardcodes `ExpectedSyntax::Expression`. The authoritative operand contract
requires `ExpectedSyntax::Statement` for that finite role. Repair it as a
separate behavioral correction with Missing, Error and frozen-reconciliation
controls; do not preserve the existing assertion as a topology oracle.

Work in bounded stages: first establish these shared boundaries and declaration
and test-family topology, then split the remaining large family owners only
after their body-level responsibility review. Stop any extraction that changes
recovery ownership/order, Item emission, lexical-only observation, or a sealed
capability; such a change needs its own authority rather than an expectation
update.

Gate A is complete. `input`, `context`, `output`, `handoff`, `expression` and
`declaration` now express their actual ownership; `driver` no longer exists,
and `tests/mod.rs` is a catalogue with explicit support and declaration suites.
The For Body publication now maps only that role to `Statement`; direct and
actual-caller Missing/Error fresh/frozen controls preserve exact CST, Item
extents and `InLine` handoff. M2 conformance and regression review closed after
two test-only evidence repairs. Its then-known unrelated `(a +\nb)` operator
test expectation was later corrected by the approved delimiter contract. Next:
body-level responsibility review before splitting the still-large Expression,
TypeExpression and Pattern owners.

Gate B1 is the reviewed Expression split. `expression/operator_chain.rs` owns
admitted NUD dispatch, prefix/infix/suffix recursion, ML application, tail
dispatch and the three-result continuation protocol. `expression/required_operand.rs`
owns the explicit-role mandatory-operand kernel, its boundary predicate, typed
Missing/Error mapping and sealed lexical Error retry. `expression/mod.rs` is
only their narrow façade. Do not split NUD from tail, reintroduce literal
scanning, or move the For Body mapping: those would sever established owner
cycles or contracts. TypeExpression and Pattern boundaries are deferred until
their full body reviews are converted to bounded gates.

Gate B1 is complete. The façade now declares only the two coherent owners;
all executable bodies are equivalent to the pre-split Expression implementation
apart from private child visibility and formatting. Focused handoff, operand,
tail, delimiter, normalized, output and frozen controls passed. Independent
regression review also confirmed the unchanged If/Case/For caller roles and
the retained For Body `Statement` mapping. The then-known operator baseline
was later corrected as a stale delimiter expectation.

Gate B2 is complete. The former mixed tail body is now a narrow
`expression/tails/mod.rs` façade over `colon.rs`, `with_body.rs`,
`delimited_tail.rs`, `fixed_access.rs`, and the only shared `inline_slot.rs`.
Colon owns its RHS/comma/outer-sequence recursion; With owns its introducer,
body and terminal; delimiter wrappers own their open-loop-finish-continuation
sequence; fixed access owns dot dispatch and Field/Path recovery. The shared
boundary predicate is accurately named `is_inline_slot_boundary`; the
misleading Colon-only name and wrapper are gone. Function bodies remain
equivalent apart from owner paths, visibility and that approved rename. M1
regression review found one duplicate lint attribute only; the one-line repair
is complete. Tails/delimiter/fixed-tail/Colon-With controls pass, while the
pre-existing `virtual_colon_errors_keep_close_eof_and_quoted_fence_records_frozen`
expectation was later corrected to the approved Literal parent-record order.
Package check, format and diff checks pass; no benchmark sample/process was
used. Next: prepare the scoped successor Yumark document/fence construction
gate; do not promote its test-only cell witness directly.

## Crate-root syntax topology replacement

The user has rejected the generic `parser/` umbrella. Supersede the Gate A
private-tree placement without changing observable behavior: the generic
umbrella is removed rather than renamed or replaced with another
generic container. The `yu-syntax` crate root is the syntax-phase boundary;
its direct private children must name their own responsibility.

`operator.rs` becomes `operator_table.rs` for immutable declarations, fixities,
tries and table construction. Its separate lexical consumer becomes
`lexical/operator_scan.rs`; `lexical/stops.rs` owns finite stop masks and
`lexical/trivia.rs` owns source-only trivia observation. The remaining lexical
Item/current/scan/fence/position owners stay under `lexical/`. `cursor.rs`
owns live syntax/lex cursors and recovery state; grammar owners emit directly
into Rowan, while `cursor::recovery` owns committed diagnostic publication and
recovery reconciliation; `recovery_record.rs` owns the typed
recovery vocabulary. `ambient_claim.rs`, `sequence.rs` and `handoff.rs` are
direct narrowly named shared owners.

Grammar owners are direct siblings: `expression/`, `declaration/`,
`type_expr/`, `pattern/`, `literal/`, `rule/`, `statement.rs`, and
`virtual_statement_block.rs`. `header.rs` owns source-leading discovery and
`source_file.rs` owns top-level source progression/reconciliation. Internal
tests move to `tests/` with their existing role-named subtrees. `lib.rs` owns
only the public syntax boundary and direct private module declarations.

The move preserves public exports and all accepted/malformed CST, recovery,
frozen-record, current-Item, lexical-only and cost contracts. Do not merge the
operator table and lexical scanner, create a replacement umbrella, widen sealed
fields/capabilities, or change expectations to make paths compile. Root-level
sibling interfaces may become `pub(crate)` only where the former umbrella
ancestor supplied the same effective private-crate visibility; retain stricter
owner-local visibility everywhere else.

This topology replacement is complete. The independent regression review found
no Rust, visibility, public-boundary or owner-split defect; it found stale
current task/ledger locators only, which are corrected here and in the ledger.
Focused lexical/output/recovery/header/root/public-boundary controls, package
and workspace checks, dependency-graph, format and diff checks pass. The
documented `(a +\nb)` operator expectation was later corrected under the
approved delimiter contract. Benchmark use is zero samples/processes.

The pre-Item scalar-frontier evidence plan and reverted primary-completion
proposal are superseded. Their historical evidence does not create a remaining
recovery-equality prerequisite.

## Following work and residuals

1. Migrate the remaining mutually recursive Expression/Pattern/Statement/
   declaration/literal owners. Local Type construction does not certify raw
   recovery still emitted by another owner. CaseLike structural, Arrow/Body,
   Separator and Catch-close slots are complete; continue with a distinct
   remaining owner rather than reopening that family wholesale. For Pattern,
   `in`, body-introducer and shallow Body slots are also complete.
   TypeDeclaration Name and equality DefinitionIntroducer are complete; its
   typed RHS remains a separate existing owner.
   Enum/Error Name and BodyIntroducer are complete owner-locally; Variant and
   companion/derives owners remain distinct.
   The shared declaration field owner is complete: it transports finite
   Struct/Enum/Error roles; publishes Field, FieldName, FieldColon,
   FieldSeparator, and construct-close records; and owns the neutral sequence
   in `declaration/fields.rs`. Its field lexical acquisition and boundaries no
   longer depend on the Struct owner. Continue with a distinct remaining
   declaration/companion or typed-output owner rather than reopening this gate.
2. Complete the typed-output owner ledger, actual embedded/header-full proof,
   and remaining public integration gates. T2/T3/T4 local evidence does not
   close aggregate O6 rows. Production Yumark and virtual-context adoption
   remain separate obligations.
3. The former six TypeDeclaration failures are resolved at the Type ownership
   boundary. Do not reopen their old malformed-output expectations as Yulang2
   compatibility requirements.

## Verification and environment

Use `cargo test -p yu-syntax --lib tests::type_expr:: -- --test-threads=1`
for Type construction. The leading-row gate also ran the known-small
`tests::normalized::normalized_type` and
`tests::normalized::ordinary_type_unmatched` filters. Use the focused
`tests::output::` and
`tests::recovery_output::` filters for output/RB invariants, then one
`cargo check -p yu-syntax`. Check inventory before broadening. Benchmark budget
for these bounded owner-local gates is zero samples/processes unless material
cost uncertainty requires a separately justified measurement.

The record-sequence gate's initial test build took 2m24s, with one sampled
rustc process around 1.8 GiB RSS and available memory; later focused rebuilds
took 38s and 31s. Test execution remained sub-second. Treat an active rebuild
separately from a running test suite; preserve the focused serial test budget.

`cargo xtask check-graph` is the available dependency-direction check, not a
syntax test runner. The workspace-local `crates/chasa-recover` already provides
`token`, `maybe`, and `with_str`; do not add generic API for owner-specific CST
or recovery policy. An API addition needs a concrete reusable operation across
independent callers, not just shorter syntax at one site.

## Navigation and history

- Design entry: `notes/design/INDEX.md`.
- Replacement gates: `notes/design/2026-09-02-yu-syntax-recursive-descent-rewrite-plan.md`.
- Typed output: `notes/design/2026-09-06-successor-typed-output-recovery-amendment.md`.
- Callsite/RB ledger: `notes/progress/successor-typed-recovery-ledger.md`.
- Current progress: `notes/progress/daily/2026-09-10.md`.
- The former 2,710-line task log is preserved at
  `notes/progress/rewrite-state-before-recovery-authority-2026-09-08.md`.
  Consult it for completed gates, older residual context, and syntax-reference
  site history; it is not an active queue or a source of new authority.
