# Successor CST slot-schema catalog

Status: Draft

Date: 2026-09-10

Scope: a non-normative catalog scaffold for the complete successor Rowan CST
slot schema required before CST-derived diagnostic/API migration. It records
where authoritative or evidence-complete slices can be located and where
mapping remains to be done. It does not select a new grammar, recovery,
diagnostic, API, or implementation policy.

Supersedes: none

## Relationship and authority

The governing authority is
`2026-09-09-successor-cst-derived-diagnostics-amendment-draft.md`. Its complete
per-slot schema gate remains a prerequisite to removing parser recovery-record
state, reservations, frozen reconciliation, diagnostic IDs, or public
diagnostic storage. This catalog is an organizing artifact for that prerequisite;
it is not the schema and is not authority for a missing row.

`2026-09-09-successor-error-invalid-topology-ordering-addendum.md` remains
Authoritative for the completed topology-only Error-token/Invalid-node gate.
`2026-09-09-successor-error-admission-schema-clarification.md` remains Draft,
except for its AssignmentTail direct-inline slice, which is Authoritative. Its
bounded catalog row faithfully maps that slice without extending it. Existing accepted
syntax, recovery continuation, current-Item and fence handoff, lossless-source,
and direct-Rowan contracts retain their governing authorities.

This is internal schema work. The public `syntax-reference` remains
reader-facing XML-like Rowan grammar and explanation; it must not contain this
catalog's source/callsite coverage.

## Catalog identity and required row facts

A semantic slot identity is:

```text
(production, ordered child phase, necessary ancestor context)
```

Neither a source helper/caller nor a parent `SyntaxKind` alone identifies a
slot. `necessary ancestor context` is present only when it is required to
distinguish otherwise identical child placement, such as an opener-selected
close, a parent sequence phase, or a caller-selected boundary.

Each completed catalog row must state all of the following:

| Fact | Required content |
| --- | --- |
| identity | production, ordered child phase, and necessary ancestor context |
| ordered Rowan grammar | valid children, punctuation, optionality, repetition, and trivia placement |
| malformed admission | exact Missing, raw Error-group, retry, terminal, and structured-child alternatives |
| nested ownership | child productions which retain their own slot schemas |
| transition/handoff | owner transition form; ordinary, malformed-run, retry, and protected-boundary leading; consumed/returned Item facts |
| diagnostic projection | recovery category, expected alternatives, primary alternative, range/grouping, and occurrence order |
| proof/status | governing authority, direct CST evidence, review/promotion state, and any excluded dependency |

An omitted row grants no malformed admission. This catalog does not infer one
from a sibling, common helper, or matching source spelling.

## User-approved transition vocabulary convention

The user approved the following bounded convention for catalog documentation.
It is explanatory schema notation for assigning ownership and continuation in a
row. It is not parser state, an API, a generic recovery library, or a
token-global policy.

An owner may document only the transition form that its governing behavior
already establishes:

| Transition form | Catalog meaning |
| --- | --- |
| consume foreign close + preserve sequence position | consume the foreign close required by the owner while returning to the same ordered sequence phase, rather than treating it as a successful local close |
| recover failed slot + retry without duplicate Missing | publish the failed-slot recovery once, then retry the same slot without emitting another Missing for that occurrence |
| commit terminal close recovery | enter an irreversible terminal-close recovery owned by the close slot; later content is not reconsidered as an argument or separator |
| complete locally | consume the recognized local completion and advance to the owner's next ordered phase |
| hand off protected boundary | return the protected boundary Item unchanged, with its pending leading and continuation facts, to the caller that owns it |
| retain nested syntax in wrong slot via existing Invalid | retain the admitted nested production beneath an already-authorized structured `Invalid`; the child keeps its own schema |

Every completed row uses this format:

```text
entry slot → recognized condition and priority → consumed extent/CST output
→ continuation position or handoff → diagnostic slot witness
```

The row records the selected transition or handoff explicitly. Expected
alternatives remain separately derived from the ordered CST grammar; they are
not inferred from a transition label, a token spelling, or a source helper.
`Error` spelling is never read or relexed for this convention. The convention
does not create a generic wrapper or expand `Invalid` beyond its existing
authorized owners. TypeCall proves why a token-global `)` versus `@` policy is
invalid: the same spelling participates in different owner phases and must be
classified by the documented slot, priority, and continuation.

## Source-family catalog map

The map is a planning index, not a claim that a family is complete or that a
file/call count equals a semantic-slot count. The non-authoritative source
coverage manifest names the corresponding evidence files.

| Catalog family | Row scope to map | Current catalog state |
| --- | --- | --- |
| expression tails and required operands | assignment, annotation, colon/with, fixed access, required operands, delimited expression phases | partial: the authoritative AssignmentTail direct-inline RHS row and dedicated Field/Path evidence-complete Draft slices are mapped; all other rows remain open |
| expression forms and statement/layout containers | case/if/for, source-root, statement and virtual-statement sequences | unmapped except for delegated evidence links |
| pattern and structured delimiters | Pattern entries, delimited sequences, RecordPattern Item/Separator structured recovery | unmapped; preserve the designated Invalid row below |
| type entries, tails and delimiters | type expression, paths, rows, variants, forall, delimited closes and TypeCall close | partial: the bounded LeadingEffectTypeHead, `TypePathTail` segment, and TypeCall-close rows are mapped below; all other Type production contexts remain open |
| literal, interpolation and rule | String terminator, interpolation sequence, Rule-owned slots, ExpressionList delegation | partial: listed evidence-complete Draft slices; ExpressionList newline exception remains unlinked/unmapped |
| declarations and headers | declaration heads, fields, variants, companions, imports, operator headers and payloads | unmapped |

## Fixed topology references

### The two and only two current structured `Invalid` rows

These are topology references, not new admissions. The Error/Invalid ordering
addendum permits only these two structured owners. Their nested syntax remains
child-owned and must be cataloged in its own row before ledger retirement.

| Semantic slot identity | Exact structural nesting | Status |
| --- | --- | --- |
| `(PolymorphicVariantTag, wrong-kind TagName head before payload children, direct tag in PolymorphicVariantType)` | see the bounded PV row below | fixed existing structured owner; mapped |
| `(RecordPattern, Item or Separator in its record sequence phase, RecordPattern sequence context)` | item phase: `RecordPattern(Invalid(Pattern(...)))`; separator phase: see the bounded separator row below | fixed existing structured owner; item schema unmapped; separator row pending audit |

No other row may obtain `Invalid` by analogy. The nested `TypeExpression` or
`Pattern` can itself contain its own documented Missing/Error/Invalid topology;
the enclosing `Invalid` remains a distinct structured occurrence and precedes
its children in future interpretation.

### Polymorphic-variant wrong-kind TagName-head map

This is one bounded Draft row for the already-Authoritative wrong-kind
TagName recovery. It expands the fixed PV topology reference above; it adds no
admission or recovery semantics. `RecordPattern` remains a separate discovered
ambiguity and is not mapped by this row.

| Fact | Draft catalog row |
| --- | --- |
| identity | `(PolymorphicVariantTag, wrong-kind TagName head before payload children, direct tag in PolymorphicVariantType)` |
| ordered Rowan grammar | `PolymorphicVariantType > PolymorphicVariantTag > Invalid > TypeExpression`, with exactly one direct `TypeExpression` child of this `Invalid`. The PV list keeps its outer introducer, commas, and closing brace; they are not children of this slot. |
| malformed admission and completion | Only a non-Identifier Type NUD admitted by the existing Type-ML scope enters this row. It parses one full Type expression in non-`TypeApply` Type-ML scope; adjacent internal continuation remains Type-owned. The completed head then returns to the existing PV payload judge. |
| nested ownership | The `TypeExpression` owns its internal continuation and all of its nested Missing/Error/Invalid topology. This row neither maps nor changes malformed prefix recovery, payload/list-tag recovery, separators, the PV close, or nested Type rows. |
| source and boundary ownership | Fresh outer-list leading is emitted before entry to the direct tag. A retry after a malformed tag prefix is inside that `PolymorphicVariantTag`, before this `Invalid`; a protected outer-list boundary Item keeps its leading pending and unemitted. The row does not claim ownership of outer-list leading, introducer, comma, brace, or a returned boundary Item. |
| transition/handoff | `wrong-kind TagName head entry → the existing Type-ML scope admits one non-Identifier Type NUD, before the PV payload judge → consume that full Type expression as the single direct `Invalid > TypeExpression` output, with no outer-list punctuation or leading → complete locally to the existing payload judge; a protected outer-list boundary remains unchanged with pending leading → the `Invalid` witnesses singleton `Identifier`, primary zero, before its nested Type occurrences (and after any earlier tag-prefix Error)`. |
| diagnostic projection | Project singleton `Identifier` with primary alternative zero. Its range is the `Invalid` text range in UTF-8 bytes. Occurrence order is pre-order: a preceding tag-prefix `Error`, when present, precedes this TagName occurrence; nested Type occurrences follow it. |
| proof and status | Governing behavior: [PV current-Item recovery](2026-09-08-successor-pv-current-item-recovery.md) §§Acceptance and supersession, Typed PV sites, and Pre-write controls. Direct proof locators: `tests/type_expr/pv_recovery.rs:263–303`; `tests/type_expr.rs:6735–6832, 7085–7176, 8173–8254`; `tests/type_expr/bracket_arrow_recovery.rs:216–221`; `tests/type_expr/forall_recovery.rs:496–502`; `tests/type_expr/record_field_recovery.rs:368–374`. Status: `mapped`; temporary recovery records are proof only, never row identity or a future ledger. |

### TypeCall close-slot map

This is one bounded Draft row. It records the already-Authoritative terminal
close semantic slot from the [close-node amendment](2026-09-10-successor-typecall-close-slot-node.md)
and [residual-policy amendment](2026-09-10-successor-typecall-close-residual-policy.md),
for the later CST-derived diagnostic interpreter described by the
[diagnostics amendment](2026-09-09-successor-cst-derived-diagnostics-amendment-draft.md). It neither
maps nor changes TypeCall argument, separator, caller/boundary, or nested-child
slots.

| Fact | Draft catalog row |
| --- | --- |
| identity | `(TypeCallTail, terminal close after all argument/separator children, TypeCall context)` |
| ordered Rowan grammar | `TypeCallTail := LParen <argument/separator children delegated to their own rows> TypeCallClose`; `TypeCallClose := NativeTrivia* (Error NativeTrivia*)* (RParen \| Missing)`. It contains native trivia, zero or more raw `Error` leaves, and exactly one terminal native `RParen` or zero-width `Missing`. It admits no `Invalid`, structured child, separator, argument, or further-argument retry. |
| malformed admission and completion | A matching close completes normally. An unprotected mismatched close enters existing irreversible close recovery. Separately, only after every recognized Call dispatch declines it, a residual post-argument Item enters that same recovery. Subsequent nonboundary Items are close `Error` content until, but not including, matching close, EOF, or a protected exit. EOF or protected exit emits exactly one close `Missing`. |
| nested ownership | The parent delegates argument and separator grammar; their Missing/Error and all nested production schemas remain child-owned. Argument `Error` leaves remain direct `TypeCallTail` children, distinct from close Error leaves beneath the immediate `TypeCallClose` parent. |
| source and boundary ownership | Leading already emitted by opening, argument, or separator ownership remains outside `TypeCallClose`; after close construction begins, remaining leading is native inside it. Ordinary horizontal raw caller/outer-boundary leading may be emitted outside the node by `emit_horizontal_delimited_boundary`, which completes its terminal Missing and hands the boundary out before close-recovery entry. Protected leading encountered during close retry remains pending; a matching close consumes its leading, a protected Item returns with its leading, origin, line, and remainder, and ordinary EOF completion emits remaining leading. |
| transition/handoff | `terminal TypeCall close entry → matching close completes first; an unprotected mismatched close, or only after every recognized Call dispatch declines a post-argument residual, commits terminal close recovery → consume the matching RParen or raw nonboundary Error contents under one `TypeCallClose`, or emit its one terminal Missing at EOF/protected exit → complete locally after matching close; EOF completes the Missing, while a protected boundary returns unchanged with pending leading/origin/line/remainder → the immediate `TypeCallClose` child witnesses singleton Close(Parenthesis), primary zero, with only its maximal adjacent Error group projected`. |
| diagnostic projection | Project singleton `Close(Parenthesis)` with primary alternative zero. A Missing is zero-width. A diagnostic's one maximal adjacent `Error` group under the immediate `TypeCallClose` parent has its combined UTF-8 range; native trivia or final Missing ends the group. Occurrence order includes a preceding argument Missing at the same range. `TypeCallClose` itself has no diagnostic. |
| proof and status | Direct proofs: `tests/type_expr/type_call_fallback.rs:33,62,120,154,170,208,226`; `tests/type_expr.rs:3361,4503,4588,5062,5179`. Governing amendments above are Authoritative; retained recovery records are temporary evidence only, not catalog identity or a future ledger. Status: `mapped`; the independently audited catalog row and its governing behavior remain Draft and Authoritative respectively. |

### TypePathTail required-segment map

This bounded Draft row records only the required segment immediately after an
accepted Type `ColonColon`. It is governed by the
[T2b PathSegment recovery amendment](2026-09-07-successor-t2b-pathsegment-recovery-amendment.md),
the [Type contextual-boundary correction](2026-09-08-successor-type-contextual-boundary-correction.md),
and the TypePathTail slice in the
[error-admission clarification](2026-09-09-successor-error-admission-schema-clarification.md#proposed-schema-slice-typepathtail-segment).
It does not merge this Type owner with expression `PathTail`, infer an owner
from `::` spelling, map another Type production context, or promote the open
global interpreter or recovery-ledger-retirement gate.

| Fact | Draft catalog row |
| --- | --- |
| identity | `(TypePathTail, required segment immediately after ColonColon, enclosing Type continuation context)` |
| ordered Rowan grammar | `TypePathTail := ColonColon NativeTrivia* (Identifier \| SigilIdentifier \| Missing \| Error+ (Identifier \| SigilIdentifier \| ContinuationTrivia (Identifier \| SigilIdentifier)) \| Error+)`; `NativeTrivia*` is the owned initial leading, and `ContinuationTrivia` is the owned continuation-qualified deeper LF/CRLF-plus-indent leading between `Error+` and its same-tail retry; both may be elided in compact grammar notation. The `ColonColon`, owned initial/retry trivia, direct Error leaves, and accepted segment are direct `TypePathTail` content in source order. `Error+ Identifier`, `Error+ SigilIdentifier`, and their `ContinuationTrivia` forms are same-slot retries; a repeated `::` completes this tail and begins a sibling `TypePathTail`. No `Invalid` is admitted. |
| malformed admission and completion | Initial valid Identifier/SigilIdentifier completes the required segment. Abstract pending boundary, caller/outer boundary, path boundary, shallow layout, EOF, fence, close, or active stop selects the one direct zero-width Missing according to the phase-specific ownership below. A nonempty malformed Item starts direct `Error+`; an adjacent Identifier/SigilIdentifier, or an Identifier/SigilIdentifier after owned continuation-qualified deeper LF/CRLF-plus-indent trivia, retries this same slot without a duplicate Missing. Integers are malformed. After Error, every protected boundary ends the run and is handed out; a repeated `::` is a boundary, never Error content. |
| nested ownership | This row owns no nested production. Its accepted Identifier/SigilIdentifier is a token child, while the enclosing Type continuation owns TypeApply, later Type tails, caller punctuation, closes, and any sibling repeated tail. The outer TypeApply owns the horizontally separated next Type after an incomplete path. All other Type primaries, calls, rows, variants, forall, delimiters, and their recovery slots remain delegated or unmapped. |
| source and boundary ownership | Before initial admission, `TypePathTail` owns initial leading: ordinary EOF/path-boundary or shallow-layout leading is emitted before its Missing, while abstract, caller, and outer boundaries retain their Item and leading pending. Same-line contextual name-shaped Items win initial segment admission; newline-bearing contextual Items remain protected. After a malformed payload, protected boundary leading remains pending. Only continuation-qualified deeper LF/CRLF-plus-indent leading before a retry name is emitted as native direct `TypePathTail` content, outside the Error group: `A::@\n  B` retries `B` in this tail. `A::@B` likewise retries directly, whereas `A::@ B` leaves the horizontal space and `B` unchanged, closes the incomplete tail, and hands them to outer TypeApply. An immediately adjacent block-comment prefix may join the Error before either outcome, but neither continuation trivia nor an ordinary horizontal gap does. |
| transition/handoff | `required TypePathTail segment entry → protected boundary/path-boundary and initial leading rules select Missing before payload admission; otherwise Identifier/SigilIdentifier wins, and another payload starts the direct Error group → consume the accepted segment, emit one zero-width Missing, or consume contiguous malformed direct Error leaves → after Error retry the same slot only for an adjacent name-shaped Item or a name after owned continuation-qualified deeper LF/CRLF-plus-indent trivia, without duplicate Missing; emit that retry trivia as direct TypePathTail content, never Error → otherwise complete the incomplete tail and hand the protected Item unchanged (including pending leading, origin, line, and remainder) to the enclosing Type continuation/TypeApply → the direct Missing or maximal direct Error group witnesses TypePathSegment, primary zero`. |
| diagnostic projection | A direct Missing projects singleton `TypePathSegment`, primary alternative zero, at its zero-width UTF-8 range. One maximal adjacent direct Error group under this immediate `TypePathTail` parent projects one `TypePathSegment` occurrence over the group’s combined UTF-8 range. Native initial or continuation retry trivia, an accepted sibling segment, a nested/sibling tail, or a source/leading/boundary handoff splits groups. Source slot order applies: an Error group precedes its same-tail retry trivia/segment, while a Missing is ordered at its direct slot occurrence. Accepted `ColonColon`, Identifier, and SigilIdentifier project none. |
| proof and status | Governing behavior: T2b §§1–2.4 and the contextual-boundary correction; bounded direct-CST/admission evidence: error-admission clarification, **Proposed schema slice: TypePathTail segment**. Concrete publishers are `crates/yu-syntax/src/type_expr/mod.rs:2109`, `2137`, and `2161` (the three Missing branches), plus `2294` (the direct Error-run); `2261` emits the accepted continuation retry segment. Existing focused Rowan controls cited by that slice cover accepted/sigil/integer, comment-prefix, contextual/close priority, retry versus TypeApply, repeated tails, UTF-8/CRLF/fence, and Root conservation. Status: `mapped` for this evidence-complete Draft row only. Expression PathTail, every excluded Type context, the global CST interpreter, and recovery-ledger retirement remain open. |

### LeadingEffectTypeHead required-head map

This bounded Draft row records only the required head phase immediately after a
direct leading `BracketRow` in one existing `TypeExpression`. It is grounded in
the [LeadingEffectTypeHead proposed schema slice](2026-09-09-successor-error-admission-schema-clarification.md#proposed-schema-slice-leadingeffecttypehead)
and its direct Rowan/recovery controls. `LeadingEffectTypeHead` is a semantic
slot name, not a Rowan node or wrapper. This row does not map the `BracketRow`,
arrow RHS, structured-primary internals, or any other Type context.

| Fact | Draft catalog row |
| --- | --- |
| identity | `(TypeExpression, required LeadingEffectTypeHead phase immediately after a direct leading BracketRow)` |
| ordered Rowan grammar | `TypeExpression := BracketRow NativeTrivia* LeadingEffectTypeHead`; `LeadingEffectTypeHead := Missing \| PrimaryAndContinuation \| Error+ NativeTrivia* PrimaryAndContinuation \| Error+ NativeEofTrivia* EOF \| Error+`. Here `EOF` is a non-emitting terminal condition, not a Rowan child. `NativeEofTrivia*` denotes the continuation-compatible ordinary EOF trailing trivia after a direct Error group; it is direct `TypeExpression` content, never Error content. Thus `[e] @ ` and `[e][f ` end with the Error group followed by their native trailing space, not an Error that absorbs that space. `Missing` is a direct zero-width child of this `TypeExpression`; every `Error` is a direct raw token child. `PrimaryAndContinuation` is shorthand for the existing direct scalar/sigil/integer token or existing structured primary with its already-selected continuation; it creates no wrapper or generic primary/tail node. No `Invalid` is admitted by this row. |
| malformed admission and completion | A normal Type primary completes this required head and retains its existing continuation. A protected or ordinary boundary before primary admission selects one direct Missing under the leading rules below. A non-primary begins one maximal adjacent direct `Error+` run; it may retry only when an empty recovery-local close stack reaches an admitted Type primary. A disabled second bare row is Error content, not a second `BracketRow`, synthetic nested `TypeExpression`, or second head slot. Matching local closes can be consumed while recovering; mismatched close, caller/outer boundary, and non-continuation newline remain pending at every nesting depth. At empty nesting depth comma and semicolon terminate recovery; within nesting they are consumed only unless an active caller stop claims them. At ordinary EOF, compatible trailing trivia after the direct Error group is native direct `TypeExpression` content; the terminal Error path adds no same-slot Missing. |
| nested ownership | `BracketRow` owns its rows, delimiters, and its own close recovery. Any admitted structured primary owns all of its internal grammar and Missing/Error/Invalid topology; in particular its row, group, forall, record, variant, path, call, and tail slots stay separate. A leading-row `ForallType` is terminal for this enclosing TypeExpression, so its selected arrow/path/call/application remains inside `ForallType`; an incomplete leading-row `PolymorphicVariantType` likewise returns its boundary rather than resuming this head slot. The row deliberately excludes BracketRow rows, arrow RHS, structured-primary internals, and every other Type context. |
| source and boundary ownership | Initial malformed leading and admitted/retry leading are native direct `TypeExpression` children; internal malformed leading belongs to adjacent direct Error tokens. Fresh protected-boundary leading remains pending and produces the direct head Missing without consuming that Item. Only continuation-compatible ordinary EOF leading is native before its Missing. After a direct Error group, continuation-compatible ordinary EOF trailing trivia is likewise native direct `TypeExpression` content outside that group; protected-boundary leading remains pending on the unchanged returned Item, and this terminal Error path produces no same-slot Missing. No Error spelling is relexed. |
| transition/handoff | `direct BracketRow completion → classify the immediately following Item as protected boundary, admitted Type primary, or malformed head → emit the one direct Missing, consume the primary and its existing continuation, or consume the maximal direct Error group → with an empty recovery-local close stack, retry only an admitted primary; at compatible ordinary EOF, emit its trailing native trivia directly and complete the terminal Error path without Missing; otherwise hand the protected boundary Item unchanged (including its pending leading, origin, line, and remainder) to the enclosing caller → the direct Missing or maximal adjacent direct Error group witnesses singleton TypeExpression, primary zero`. |
| diagnostic projection | The direct Missing projects singleton `TypeExpression`, primary alternative zero, at its Rowan zero-width range. One maximal adjacent direct Error-token group under this immediate `TypeExpression` parent projects the same singleton over the combined UTF-8 group range; native leading or post-Error EOF trailing trivia is outside that range, and an admitted retry primary, sibling/nested syntax, or a handoff splits groups. Projection order is preorder: an enclosing existing `Invalid`, when any, precedes this descendant head occurrence, and this occurrence precedes recovery projected by its descendants. For explicit `[e`, the nested BracketRow close Missing occurs first, then the direct sibling head Missing at the same offset; they are not merged. |
| proof and status | Governing Draft evidence: error-admission clarification, **Proposed schema slice: LeadingEffectTypeHead**. Direct CST/recovery controls: `crates/yu-syntax/src/tests/type_expr/leading_row_cst.rs:347` (protected boundaries), `:410` (layout), `:469` (quoted-fence pending ownership), and `:536–580` (outer `Invalid` nesting and public Root conservation); `crates/yu-syntax/src/tests/type_expr/leading_row_recovery.rs:20–100, 244–257`; and `crates/yu-syntax/src/tests/type_expr.rs:9076–9164, 7923–7928`. Concrete publishers are limited to `crates/yu-syntax/src/type_expr/mod.rs:1518` (incomplete-row exit Missing), `1667` (direct malformed Error-run), and `1678` (boundary/ordinary leading head Missing). Status: `mapped` for this bounded evidence-complete Draft row only; the interpreter, recovery ledger, promotions, and global Type rows remain open. |

### BracketRow-selected required-arrow continuation map

This bounded Draft row records the required-arrow continuation immediately
after its direct `BracketRow` in an existing `TypeArrowTail`, from the
[error-admission clarification](2026-09-09-successor-error-admission-schema-clarification.md),
**Proposed schema slice: BracketRow-selected required-arrow continuation**.
It does not map `BracketRow` internals or the distinct actual-arrow RHS slot.

| Fact | Draft catalog row |
| --- | --- |
| identity | `(TypeArrowTail, required-arrow continuation immediately after its direct BracketRow)` |
| ordered Rowan grammar | `TypeArrowTail := BracketRow RequiredArrowContinuation`; `RequiredArrowContinuation := ActualArrowRhsSuffix \| Missing TypeExpression \| Missing \| Error+ ActualArrowRhsSuffix \| Error+ TypeExpression \| Error+`. Native initial malformed, retry, and ordinary-EOF continuation trivia are direct `TypeArrowTail` children in source order; rejected payload and internal malformed leading are adjacent direct `Error` tokens. `ActualArrowRhsSuffix` begins with the direct accepted `Arrow` and delegates its RHS grammar; it is a distinct child phase, not a wrapper introduced by this row. No `Invalid` is admitted. |
| malformed admission and completion | An actual `Arrow` completes this required-arrow continuation and selects the delegated actual-arrow suffix. An arrowless admitted Type primary emits one direct `Missing` then its direct `TypeExpression`. A protected boundary first emits one direct `Missing` and returns the complete Item. An incomplete `BracketRow` exit unconditionally emits its separate direct required-arrow Missing, then returns that existing exit unchanged; its returned Item is never classified as an Arrow or RHS, even when valid. A non-primary begins one maximal direct `Error+` group; it retries only to an actual Arrow or Type primary, without a duplicate Missing. At ordinary EOF, continuation-compatible leading is native direct tail content before the initial Missing or after a terminal Error group; non-continuation EOF leading remains pending. An Error group reaching a boundary produces neither another required-arrow Missing nor an ArrowRhs Missing. |
| nested ownership | `BracketRow` retains its rows, delimiters, close recovery, and all internal slots. An arrowless retry's `TypeExpression` retains its full Type grammar and recovery. An admitted actual Arrow selects the separate `TypeArrowTail` actual-arrow RHS slot, whose RHS `TypeExpression`, recursive arrows, and Missing/Error topology remain outside this row. |
| transition/handoff | `incomplete BracketRow exit → unconditionally emit its separate direct Arrow Missing → return the existing exit/handoff unchanged, without Arrow/RHS classification even for a valid returned Item; direct completed BracketRow → protected boundary wins, otherwise actual Arrow, admitted Type primary, or malformed run is classified → consume the actual Arrow suffix, emit one direct Missing before the arrowless TypeExpression, emit one direct Missing and hand off the protected Item unchanged, or consume the maximal direct Error group → after Error retry only actual Arrow or Type primary without duplicate Missing; ordinary compatible EOF emits native tail trivia, while protected boundary leading/origin/line/remainder stays pending on the returned Item → the direct Missing or maximal adjacent Error group witnesses singleton Arrow, primary zero`. |
| diagnostic projection | A direct Missing or one maximal adjacent direct Error-token group under this immediate `TypeArrowTail` parent projects singleton punctuation `Arrow`, primary alternative zero. Missing uses its direct zero-width Rowan range; Error uses the combined UTF-8 range of that group, excluding native initial/retry/EOF trivia. Projection is preorder: nested `BracketRow` close recovery precedes this continuation occurrence, including an incomplete row's close Missing and direct arrow Missing at the same range; a recovered actual Arrow's distinct nested ArrowRhs occurrence follows this continuation occurrence and is not merged with it. |
| proof and status | Governing behavior: [BracketRowArrow current-Item recovery](2026-09-08-successor-bracket-arrow-current-item-recovery.md) and the Draft slice above. Direct CST/recovery controls: `crates/yu-syntax/src/tests/type_expr/bracket_arrow_cst.rs:17–147,151–185,189–408`; `crates/yu-syntax/src/tests/type_expr/bracket_arrow_recovery.rs:35–100,104–222,226–244`. Concrete publishers are limited to `crates/yu-syntax/src/type_expr/mod.rs:1683` (row owner and incomplete-exit Arrow Missing), `1780` (completed-row classification), and `1850–1854` (arrowless leading, direct required-arrow Missing, and `TypeExpression` continuation). Status: `mapped` for this bounded evidence-complete Draft row only; `BracketRow` internals, actual-arrow RHS, the interpreter, recovery ledger, promotions, and all other Type rows remain open. |

### TypeArrowTail actual-arrow RHS map

This bounded Draft row records the RHS suffix only after a direct accepted
`Arrow` in an existing `TypeArrowTail`, from the
[error-admission clarification](2026-09-09-successor-error-admission-schema-clarification.md#proposed-schema-slice-typearrowtail-actual-arrow-rhs).
It is distinct from the preceding `BracketRowArrow` required-arrow slot:
that pre-arrow owner may recover an omitted Arrow, whereas this row starts
only after an actual Arrow has been accepted. It neither maps that pre-arrow
slot nor the recursive/nested RHS slots selected below.

| Fact | Draft catalog row |
| --- | --- |
| identity | `(TypeArrowTail, required RHS suffix after a direct accepted Arrow)` |
| ordered Rowan grammar | `TypeArrowTail := Arrow (TypeExpression \| Missing \| Error+ TypeExpression \| Error+)`; this is the actual-arrow suffix only, not the complete parent production. The accepted `Arrow` is a direct `TypeArrowTail` token child. Initial accepted-RHS leading and retry leading belong to the admitted direct `TypeExpression`; initially rejected Item leading and internal rejected fragments are adjacent direct `Error` tokens. No `Invalid` is admitted. |
| malformed admission and completion | An admitted Type primary enters one direct `TypeExpression`, whose full continuation and recursive arrows remain nested. A boundary before admission emits one direct zero-width `Missing` and returns the protected Item; ordinary EOF, close/separator, caller stop, and non-continuation indentation first emit the RHS Item's owned leading, while abstract fence and outer contextual boundaries retain their Item and leading pending. A nonempty malformed run is one maximal direct `Error+` group. It retries to an admitted same-line Type primary (including `A ->@ B`) or a deeper-continuation physical-newline Type primary, without a duplicate Missing; only a shallow-or-equal physical newline or a boundary terminates the run, returns the Item with its pending leading, and adds no second Missing. |
| nested ownership | The admitted RHS `TypeExpression` owns all Type grammar, continuation, recursive arrows, and nested Missing/Error topology. Its recursive Arrow RHS is a later nested `Type(ArrowRhs)` occurrence, not this direct suffix occurrence. `BracketRowArrow` owns the distinct pre-arrow required-arrow phase; `BracketRow` internals remain separately delegated. |
| transition/handoff | `direct accepted Arrow → protected boundary/ordinary EOF leading rule selects the RHS Missing before primary admission; otherwise an admitted Type primary wins, and another payload begins the direct Error group → consume Arrow plus the nested TypeExpression, emit the direct zero-width Missing, or consume contiguous direct Error leaves → after Error retry with an admitted same-line Type primary (including A ->@ B) or a deeper-continuation physical-newline Type primary; only shallow-or-equal physical newline or a boundary hands off the protected Item unchanged, including pending leading, origin, line, and remainder → the direct Missing or maximal direct Error group witnesses TypeExpression, primary zero`. |
| diagnostic projection | A direct Missing projects singleton `TypeExpression`, primary alternative zero, at its direct zero-width Rowan range. A maximal adjacent direct Error-token group under this immediate `TypeArrowTail` parent projects one `TypeExpression` occurrence over the group's combined UTF-8 range; leading, accepted Arrow, nested RHS content, and a protected boundary handoff split groups. Projection is preorder: the pre-arrow `BracketRowArrow` occurrence, when present, precedes this RHS occurrence; recovery projected by the nested RHS follows it. The inspected pending-boundary coordinate is temporary record/handoff evidence only: at a fence the direct Rowan Missing range may precede that coordinate. |
| proof and status | Governing Draft evidence: [error-admission clarification](2026-09-09-successor-error-admission-schema-clarification.md#proposed-schema-slice-typearrowtail-actual-arrow-rhs). Direct source evidence is limited to `crates/yu-syntax/src/type_expr/mod.rs:2430` (actual-arrow tail wrapper, support), `2466` (actual RHS publication/hand-off owner), and `1832` (accepted Arrow selection from the separate BracketRowArrow phase). Status: `mapped` for this bounded evidence-complete Draft row only; pre-arrow BracketRowArrow, BracketRow internals, nested RHS, the interpreter, recovery ledger, promotion, and all other Type rows remain open. |

### StringLiteral final outer-terminator map

This bounded Draft row records the evidence-complete outer terminator slice
from the [error-admission clarification](2026-09-09-successor-error-admission-schema-clarification.md),
**Proposed schema slice: StringLiteral terminator**. It neither promotes that
slice nor maps StringPiece, escape, interpolation, Rule-literal, caller, or
Root terminal-leading slots.

| Fact | Draft catalog row |
| --- | --- |
| identity | `(StringLiteral, final outer terminator phase, opener-selected normal/heredoc mode)` |
| ordered Rowan grammar | `StringLiteral := opener-leading native trivia StringStart StringPiece* (StringEnd \| Missing)`. Opener-leading native trivia is direct `StringLiteral` content before `StringStart`; the final direct child is exactly one accepted `StringEnd` or zero-width `Missing`. `StringPiece` covers accepted text, escape/interpolation children, and ordinary-scanning physical Yumark quote-prefix leaves. `StringStart` selects normal versus heredoc close width. There is no direct outer raw `Error` or `Invalid` alternative. |
| malformed admission and completion | Only EOF or a protected fence boundary admits this slot's one zero-width `Missing`; it admits neither retry nor an outer raw Error group. A normal close, or only the opener-selected matching heredoc quote width, is `StringEnd`; a mismatched heredoc quote run remains `StringText`. Accepted quote-prefix leaves before an actual close remain native direct children. |
| nested ownership | `StringPiece` children retain their own schemas: escape recovery, interpolation format/open/close recovery, interpolation body statements, Unicode malformed Error, and FormatText stay child-owned. Their occurrences precede this final outer terminator; equal-offset nested Missing is distinguished by its child path. Rule literals, caller recovery, and Root terminal-leading ownership are outside this row. |
| transition/handoff | `final outer terminator entry → matching opener-selected normal/heredoc close has priority; otherwise EOF or a protected fence boundary selects the existing Literal(StringTerminator) Missing → consume the matching StringEnd, or emit one zero-width final Missing with no outer Error/Invalid → complete locally after StringEnd; at EOF/fence hand off the protected pending Item unchanged, including its pending leading and continuation facts → the final direct StringEnd/Missing child witnesses Literal(StringTerminator), primary zero, after all nested StringPiece occurrences`. |
| diagnostic projection | A final `Missing` projects exactly one `Literal(StringTerminator)` expectation, primary alternative zero, at its zero-width direct CST range. `StringEnd` projects none. The normal/heredoc spelling is derived from `StringStart`, not source quote search. This row has no outer Error grouping or Invalid projection. The isolated interpolation-EOF CST Missing is `3..3`; a temporary shifted recovery record at `105..105` is coordinate/reconciliation evidence only, never a schema fact or future ledger identity. |
| proof and status | Governing Draft: [error-admission clarification](2026-09-09-successor-error-admission-schema-clarification.md), StringLiteral terminator slice; existing recovery authority: [StringLiteral current-Item recovery](2026-09-08-successor-string-literal-current-item-recovery.md). Direct source evidence is limited to `crates/yu-syntax/src/literal/mod.rs:849` and `crates/yu-syntax/src/literal/mod.rs:855`: boundary Missing publication then unchanged pending-Item return. Status: `evidence-complete Draft`; direct CST and Root-losslessness proof is complete, but user promotion and every excluded child/outer row remain open. Temporary recovery records are proof only, never row identity or a future ledger. |

### RecordPattern separator-phase structured Invalid map

This bounded referenced row records only the existing separator-phase
discriminator authorized by the
[RecordPattern separator-slot amendment](2026-09-10-successor-record-pattern-separator-slot.md).
It does not map the direct item-phase `Invalid`, the preceding raw `Error`
group, ordinary sequence recovery, accepted separators/items, local close, or
nested Pattern rows. In particular, the preceding raw `Error` is not resolved
by this wrapper.

| Fact | Referenced catalog row |
| --- | --- |
| identity | `(RecordPattern, separator phase, RecordPattern sequence context)` |
| ordered Rowan grammar | The separator phase is `RecordPatternSeparator(Invalid(Pattern(...)))`. `RecordPatternSeparator` has this existing `Invalid` as its only child in scope; the direct item phase remains separately unmapped as `RecordPattern(Invalid(Pattern(...)))`. |
| malformed admission and completion | Only the existing RecordPattern separator-phase structured-recovery path enters this row, after matching local close and accepted comma priorities. It preserves the existing nested Pattern parse and does not wrap a raw Error, accepted comma, accepted item, item-phase Invalid, local close, or nested Pattern output. A recovered nested Pattern retries the sequence without an invented separator Missing; a returned comma is consumed by the existing sequence phase, while a protected caller/fence Item remains pending. |
| nested ownership | `Invalid` retains its direct range, preorder structured diagnostic, Pattern child, and nested recovery traversal. The nested Pattern retains its own schema. The wrapper adds neither a new Invalid owner nor an expectation of its own. |
| transition/handoff | `RecordPattern separator slot entry → after matching-close/comma priority, existing separator-phase structured recovery selects a wrong-kind Pattern → consume the existing Invalid and nested Pattern beneath one transparent RecordPatternSeparator, without independently consuming or emitting source; initial leading has already been emitted by RecordPattern and stays outside the wrapper → retry the sequence without a duplicate separator Missing, consuming a returned comma in the outer sequence; a returned close stays outside, while a protected caller/fence Item and its leading remain pending → the nested Invalid witnesses DelimitedSequenceSeparator, primary zero, over its unchanged text range before nested Pattern traversal`. |
| diagnostic projection | The transparent wrapper has no diagnostic, range, or expectation metadata. The enclosed `Invalid` projects `DelimitedSequenceSeparator`, primary zero, over `Invalid.text_range()` before recursively visiting its Pattern child. By contrast, the direct item-phase Invalid remains its unmapped `(RecordPattern, item phase, RecordPattern sequence context)` slot with `Identifier`, primary zero. |
| proof and status | Governing authority: [RecordPattern separator-slot amendment](2026-09-10-successor-record-pattern-separator-slot.md), including its `{a)1}` separator versus `{a@1}` item collision witnesses; private construction: `8f99e18d`. Status: `mapped`. This is a referenced/mapped discriminator only, not a complete RecordPattern schema or a claim that the preceding raw Error is resolved. |

### Dedicated Rule-owned slot map

This bounded Draft/evidence-complete section instantiates only the six
Rule-owned slots in the [dedicated Rule literal slice](2026-09-09-successor-error-admission-schema-clarification.md#proposed-schema-slice-dedicated-rule-literal-slots).
It preserves that slice's opener discriminator, direct-parent leading and
Error ownership, explicit caller stops, and terminal-owner boundary handoff.
It does not promote the slice or map RuleLiteral terminator/interpolation/lazy
children, String or Virtual children, or `ExpressionList` and any of its
caller-specific Item/Separator/close phases. In particular, bracket RuleItem
interiors and RuleCall/RuleIndex continue to delegate all such slots to
`ExpressionList`; no `Invalid` is admitted by any row here.

| Fact | RuleBody close row |
| --- | --- |
| identity | `(RuleBody, final close phase, LBrace-selected Rule body context)` |
| ordered Rowan grammar | `RuleBody := LBrace RuleAlternation (RBrace | Missing)`. Native trivia is elided; opener-leading, alternation content, and matching-close leading are direct RuleBody content. |
| malformed admission and completion | A matching `RBrace` completes. EOF, fence, or any Body stop other than the matching close emits exactly one zero-width close `Missing`; it admits no raw Error, retry, `Invalid`, or nested child in this close phase. |
| nested ownership | `RuleAlternation` and its sequences/items retain their own schemas. The enclosing RuleLiteral, callers, and terminal leading owner remain outside this row. |
| transition/handoff | `RuleBody close entry → matching RBrace has priority; otherwise the Body frame has already selected a stop → consume the matching RBrace as the final direct child, or emit the direct close Missing without consuming the pending Item → complete locally after RBrace; on EOF/fence/other protected stop hand off the pending Item with its leading, origin, line, and remainder unchanged → the final RBrace/Missing witnesses Close(Brace), primary zero`. |
| diagnostic projection | `Missing` projects singleton `Close(Brace)`, primary zero, at its direct zero-width CST range; `RBrace` projects none. A same-offset nested Missing remains distinct by its parent path. |
| proof and status | Governing slice above; direct publisher: `crates/yu-syntax/src/rule/mod.rs:250–261`. Status: `evidence-complete Draft`; only this close phase is recorded. |

| Fact | opener-selected RuleItem parenthesis-close row |
| --- | --- |
| identity | `(RuleItem, final parenthesis close phase, RuleItem whose first atom is LParen)` |
| ordered Rowan grammar | `RuleItem[LParen] := LParen RuleAlternation (RParen | Missing)`; only after a real `RParen` may the existing `RuleNonCapturePostfix* RuleCapture?` follow. A Missing parenthesis close terminates this RuleItem. |
| malformed admission and completion | The matching `RParen` completes before postfix selection. Any other parenthesis-frame stop, including EOF/fence, emits one close `Missing`; it admits no close Error, retry, `Invalid`, postfix, or Capture after that Missing. |
| nested ownership | The nested `RuleAlternation` owns sequence/item recovery. Non-capture postfixes and a later Capture are separate RuleItem phases; bracket interiors are delegated to `ExpressionList`. |
| transition/handoff | `LParen-selected RuleItem close entry → matching RParen has priority in the Parenthesis frame → consume RParen, then enter the existing postfix/Capture continuation; or emit one direct Missing → complete locally to postfix/Capture only after RParen; otherwise return the pending stop unchanged with pending leading/origin/line/remainder and terminate this RuleItem → the RParen/Missing witnesses Close(Parenthesis), primary zero`. |
| diagnostic projection | `Missing` projects singleton `Close(Parenthesis)`, primary zero, at its direct CST insertion range; `RParen` projects none. Nested same-offset Missing occurrences remain identified by parent path. |
| proof and status | Governing slice above; direct publisher: `crates/yu-syntax/src/rule/mod.rs:474–490`. Status: `evidence-complete Draft`; Body-close, bracket-list, and postfix schemas are excluded. |

| Fact | RuleCapture required-RHS row |
| --- | --- |
| identity | `(RuleCapture, required RHS after Equals, enclosing RuleItem after non-capture postfixes)` |
| ordered Rowan grammar | `RuleCapture := Equals (Error* RuleItem | Error* Missing)`, terminal. Adjacent direct `Error` leaves belong to this parent and one RHS occurrence while contiguous. |
| malformed admission and completion | An atom-start after zero or more rejected lexical Items enters one RHS RuleItem: Error-to-valid retries the required RHS without a duplicate Missing. Newline, matching frame stop, EOF, or fence after zero or more Errors emits the final required RHS Missing: Error-to-Missing is terminal and no later postfix/sequence admission is reconsidered by Capture. |
| nested ownership | The admitted RHS RuleItem owns all of its own children and recovery. RuleCapture owns only its direct Error group and RHS Missing; RuleSequence, bracket ExpressionList, String, Virtual, interpolation, lazy, and RuleLiteral child slots stay delegated or outside scope. |
| transition/handoff | `RuleCapture RHS entry → newline/frame stop has priority for Missing; otherwise an atom starts the RHS and rejected lexical Items form the immediate Capture Error group → consume Errors and then one nested RuleItem, or consume Errors and emit the one final RHS Missing → after Error-to-valid complete locally by terminating Capture/its enclosing item; after Error-to-Missing also terminate, returning the stop unchanged with pending leading/origin/line/remainder → the direct Error group and/or RHS Missing witnesses Literal(RuleItem), primary zero`. |
| diagnostic projection | Each maximal adjacent direct Capture Error group is one `Literal(RuleItem)` occurrence over its combined UTF-8 range; the final Missing is a separate singleton occurrence at its zero-width range. In source order the Error occurrence precedes the later valid child or final Missing. |
| proof and status | Governing slice above; direct publishers: `crates/yu-syntax/src/rule/mod.rs:545–568, 653–679, 864–878, 891–894`. Status: `evidence-complete Draft`; capture remains terminal and is not a general retry policy. |

| Fact | RuleField name row |
| --- | --- |
| identity | `(RuleField, required name after Dot, RuleItem named-postfix phase)` |
| ordered Rowan grammar | `RuleField := Dot (Identifier | Error+ | Missing)`. The direct name owner closes after exactly one accepted Identifier, one malformed lexical Item/Error group, or Missing. |
| malformed admission and completion | A non-stop Identifier completes. Newline, frame stop, EOF, or fence emits one Missing. One rejected lexical Item becomes direct Error and closes RuleField; a following valid name or postfix belongs to the outer RuleItem, never a name-slot retry. |
| nested ownership | There is no nested child production in this row. RuleItem owns following postfixes/Capture and any later sequence handling; ExpressionList caller phases remain delegated. |
| transition/handoff | `RuleField name entry → newline/frame stop selects Missing; otherwise non-stop Identifier has priority, with one other lexical Item admitted as Error → consume Identifier, one Error, or direct Missing → complete locally to the outer RuleItem in all three cases, returning its next/pending Item and its leading/origin/line/remainder unchanged → Identifier projects none; Error or Missing witnesses Identifier, primary zero`. |
| diagnostic projection | A maximal direct Field Error group (one lexical Item in this bounded owner) projects one `Identifier` occurrence over its UTF-8 range; Missing projects singleton `Identifier` at its direct zero-width range. The Dot has no occurrence. |
| proof and status | Governing slice above; direct publishers: `crates/yu-syntax/src/rule/mod.rs:691–720, 864–878, 891–894`. Status: `evidence-complete Draft`; no following-name retry is implied. |

| Fact | RulePath name row |
| --- | --- |
| identity | `(RulePath, required name after ColonColon, RuleItem named-postfix phase)` |
| ordered Rowan grammar | `RulePath := ColonColon (Identifier | Error+ | Missing)`. The direct name owner closes after exactly one accepted Identifier, one malformed lexical Item/Error group, or Missing. |
| malformed admission and completion | A non-stop Identifier completes. Newline, frame stop, EOF, or fence emits one Missing. One rejected lexical Item becomes direct Error and closes RulePath; a following valid name or postfix belongs to the outer RuleItem, never a name-slot retry. |
| nested ownership | There is no nested child production in this row. RuleItem owns following postfixes/Capture and any later sequence handling; ExpressionList caller phases remain delegated. |
| transition/handoff | `RulePath name entry → newline/frame stop selects Missing; otherwise non-stop Identifier has priority, with one other lexical Item admitted as Error → consume Identifier, one Error, or direct Missing → complete locally to the outer RuleItem in all three cases, returning its next/pending Item and its leading/origin/line/remainder unchanged → Identifier projects none; Error or Missing witnesses Identifier, primary zero`. |
| diagnostic projection | A maximal direct Path Error group (one lexical Item in this bounded owner) projects one `Identifier` occurrence over its UTF-8 range; Missing projects singleton `Identifier` at its direct zero-width range. The ColonColon has no occurrence. |
| proof and status | Governing slice above; direct publishers: `crates/yu-syntax/src/rule/mod.rs:691–720, 864–878, 891–894`. Status: `evidence-complete Draft`; no following-name retry is implied. |

| Fact | RuleSequence repeated-Item Error row |
| --- | --- |
| identity | `(RuleSequence, repeated RuleItem phase, RuleAlternation Body or Parenthesis frame)` |
| ordered Rowan grammar | `RuleSequence := (RuleItem | Error+)*`; adjacent direct raw Error leaves are one occurrence only while their immediate RuleSequence parent and repeated-Item slot agree. Separators and newline split/continue sequence structure outside an Error group. |
| malformed admission and completion | A Rule atom admits one RuleItem. A rejected lexical Item, including its leading, is direct sequence Error; consecutive rejected Items extend its group until an admitted item or frame stop. Matching close, separator, newline, EOF, fence, and inherited outer RuleLiteral quote context stop before name/RHS admission; this row emits no Missing and no Invalid. |
| nested ownership | Each admitted RuleItem owns its close, Capture, names, postfixes, and delegated bracket ExpressionList phases. RuleBody/parenthesis frame owns matching close and stop interpretation; RuleLiteral quote context remains outer-owned. |
| transition/handoff | `RuleSequence repeated-Item entry → explicit frame close/separator/newline/protected boundary stops have priority; otherwise atom admits RuleItem and other lexical Item selects the sequence Error group → consume each rejected Item and its leading as adjacent direct Error leaves, or consume one nested RuleItem → retry the same repeated sequence phase after Error without Missing; matching close/separator/newline stops return unchanged, and EOF/fence/protected boundaries hand off with pending leading/origin/line/remainder → each maximal direct Error group witnesses Literal(RuleItem), primary zero, before the next admitted child`. |
| diagnostic projection | One maximal adjacent direct RuleSequence Error group projects one `Literal(RuleItem)` occurrence over its combined UTF-8 range; each admitted nested RuleItem projects only through its own slots. No diagnostic is inferred from separator/newline/close handoff. |
| proof and status | Governing slice above; enclosing alternation context and direct sequence publisher: `crates/yu-syntax/src/rule/mod.rs:334–375, 412–447, 864–878`. Status: `evidence-complete Draft`; no separator/newline or caller-specific `ExpressionList` phase is mapped. |

### FieldTail required-name map

This bounded Draft row records only the required name after an accepted
expression dot. It is governed by the fixed-tail current-Item recovery
authority and the fixed-tail proposed schema slice in the
[error-admission clarification](2026-09-09-successor-error-admission-schema-clarification.md#proposed-schema-slice-fixed-fieldtail-and-pathtail-names).
It neither changes the higher-priority projection judges nor maps a later
outer continuation.

| Fact | Draft catalog row |
| --- | --- |
| identity | `(FieldTail, required Name immediately after Dot, expression fixed-postfix continuation context)` |
| ordered Rowan grammar | `FieldTail := NativeTrivia* Dot (Identifier \| Missing \| Error+)`. The initial native trivia and `Dot` are direct `FieldTail` content in source order. There is no name-leading trivia: an accepted `Identifier` is immediately adjacent to `Dot`; `Missing` is zero-width; and every raw `Error` leaf is a direct child. It admits no `SigilIdentifier`, `Invalid`, or nested production. |
| malformed admission and completion | After the already-admitted FieldTail, an adjacent Identifier completes its Name. A protected boundary, stop, separator, close, accepted dynamic LED, `(`, `[`, later fixed/dynamic tail introducer, colon boundary, or any candidate with leading trivia selects its one direct Missing. Any other non-name Item starts the maximal direct `Error+` group. `.{` and `.(` remain projection dispatches before this tail exists. |
| nested ownership | This row owns no nested syntax. The enclosing expression tail loop owns every retained Item after this tail, including its later fixed/dynamic or ML continuation; the projection owners retain their own rows. |
| source and boundary ownership | The FieldTail owns native trivia before its `Dot` only. It owns no candidate-name leading: both protected leading and retry leading stay attached to the retained Item and remain unemitted by this tail. |
| transition/handoff | `required FieldTail Name entry → projection priority has already declined and the FieldTail boundary judge selects adjacent Identifier, Missing, or raw non-name Error → consume the direct Identifier, emit one zero-width Missing, or consume one maximal direct Error group → complete locally after an accepted name; after Missing or Error finish this tail and hand off the retained Item unchanged, including protected/retry leading, threshold, ML mode, stops, baseline, line/fence, and ambient context → the direct Missing or maximal direct Error group witnesses FieldName, primary zero`. No post-Error same-tail name retry occurs. |
| diagnostic projection | A direct Missing or one maximal adjacent direct Error group under the immediate `FieldTail` parent projects singleton `Identifier`, primary alternative zero, at its direct CST range (zero-width for Missing; combined UTF-8 range for Error). Native trivia, the accepted Identifier, a retained Item/leading handoff, and sibling tails split groups. Source order places the Error occurrence before all later outer-tail occurrences. |
| proof and status | Governing behavior: [fixed-tail current-Item recovery](2026-09-08-successor-expression-fixed-tail-current-item-recovery.md) and the proposed fixed-tail schema slice above. Direct CST evidence covers accepted/Missing/Error alternatives, no name-leading, projection priority, protected/retry handoff, sibling continuation, UTF-8/CRLF/fence range, and threshold/ML handoff. Status: `mapped` for this evidence-complete Draft row only; promotion, the global interpreter, and ledger retirement remain open. |

### PathTail required-segment map

This bounded Draft row records only the required segment after an accepted
expression `ColonColon`. It is distinct from `TypePathTail`: shared spelling
does not merge their slot identities, leading rules, retry behavior, or
continuations.

| Fact | Draft catalog row |
| --- | --- |
| identity | `(PathTail, required Segment immediately after ColonColon, expression fixed-postfix continuation context)` |
| ordered Rowan grammar | `PathTail := NativeTrivia* ColonColon [NativeTrivia*] (Identifier \| SigilIdentifier \| Missing \| Error+)`. Initial native trivia and `ColonColon` are direct content; native trivia between `ColonColon` and the selected direct alternative is conditional on the existing path-leading rules. An accepted `Identifier` or `SigilIdentifier`, zero-width `Missing`, and raw `Error` leaves are direct `PathTail` children in source order. It admits no `Invalid` or nested production. |
| malformed admission and completion | Initial Identifier or SigilIdentifier completes the Segment. The fixed-tail boundary/stops select one direct Missing; ordinary Path EOF may first emit its owned leading. A non-name, including `::{`, starts maximal direct `Error+`. A lone `:` remains the terminal outer-tail continuation. |
| nested ownership | This row owns no nested syntax. The outer expression tail loop owns all retained Items, later fixed/dynamic or ML continuations, and sibling `PathTail` nodes. In particular, a repeated `::` is a later sibling tail, not a nested segment or retry. |
| source and boundary ownership | Path owns its existing conditional native leading before initial segment admission, including a physical newline when no line stop applies. Protected boundary leading remains pending. After an Error group, retry leading remains attached to the retained Item; it is neither native PathTail trivia nor Error content. |
| transition/handoff | `required PathTail Segment entry → fixed-tail boundary judge selects Missing before payload admission; otherwise Identifier/SigilIdentifier completes, and another payload starts direct Error → consume the accepted segment, emit one zero-width Missing, or consume one maximal direct Error group → complete locally after an accepted segment; after Missing or Error finish this tail and hand off the retained Item unchanged, including protected/retry leading, threshold, ML mode, stops, baseline, line/fence, and ambient context → the direct Missing or maximal direct Error group witnesses PathSegment, primary zero`. No post-Error same-tail segment retry occurs. |
| diagnostic projection | A direct Missing or one maximal adjacent direct Error group under the immediate `PathTail` parent projects singleton `Identifier`, primary alternative zero, at its direct CST range (zero-width for Missing; combined UTF-8 range for Error). Conditional native leading, accepted Identifier/SigilIdentifier, retained leading/Item handoff, and a sibling PathTail split groups. Source order places an Error occurrence before later outer-tail occurrences. |
| proof and status | Governing behavior: [fixed-tail current-Item recovery](2026-09-08-successor-expression-fixed-tail-current-item-recovery.md) and the proposed fixed-tail schema slice above. Direct CST evidence covers accepted normal/sigil/Missing/Error alternatives, conditional native leading, `::{` raw recovery, protected/retry handoff, outer-tail siblings, UTF-8/CRLF/fence range, and threshold/ML handoff. Status: `mapped` for this evidence-complete Draft row only; `TypePathTail`, promotion, the global interpreter, and ledger retirement remain open. |

### AssignmentTail direct-inline RHS map

This bounded row records the externally Authoritative direct-inline slice from
the [error-admission clarification](2026-09-09-successor-error-admission-schema-clarification.md#representative-schema-slice-assignmenttail-inline-rhs).
It maps neither the left expression nor the separately delegated
`Assignment(IndentedStatement)` alternative.

| Fact | Authoritative catalog row |
| --- | --- |
| identity | `(AssignmentTail, direct inline required Rhs immediately after Equals, enabled outer non-ML expression-tail continuation)` |
| ordered Rowan grammar | `AssignmentTail := Equals NativeTrivia* (Missing \| Error+ \| Error+ OperatorChain \| OperatorChain)` for this direct-inline position. `Equals := "="`; it is a direct child and is acquired as the one-character assignment tail only after an admitted dynamic LED declines. `OperatorChain` is the concrete direct RHS child; there is no `InlineRhs` node. Initial leading before an accepted or initially rejected direct RHS is native `AssignmentTail` trivia after `Equals` and before that child or raw Error group. No `Invalid` is admitted. |
| malformed admission and completion | An admitted inline expression completes with one direct `OperatorChain`. An admitted stop, boundary, separator, close, non-NUD bracket opener, non-continuing layout, or EOF emits exactly one zero-width direct `Missing`. A non-boundary non-NUD run emits one nonempty maximal direct `Error+` group; it either retries this same Rhs position to an admitted inline `OperatorChain`, or terminates on a protected boundary. The terminal Error group returns that boundary unchanged and adds no duplicate Missing. |
| nested ownership | The direct RHS `OperatorChain` owns the full expression grammar and every nested recovery slot, including recovery reached after an Error retry. The raw Error group contains only direct Error tokens; it does not retain nested grammar. The left expression, dynamic-LED selection, and all later outer-tail processing are not children of this row. |
| transition/handoff | `enabled outer non-ML tail sees Equals after dynamic LED declines → consume direct Equals and classify the direct Rhs as admitted OperatorChain, one Missing, or one maximal Error group → consume the RHS child, emit the zero-width Missing, or consume direct Error leaves → Assignment is terminal and returns its resulting Item/exit without same-chain continuation; Error retry admits a new direct OperatorChain, whose retry leading is native inside that child, while protected-boundary leading remains pending on the returned Item → the direct Missing or maximal direct Error group witnesses Assignment(Rhs), Expression, primary zero`. Initial rejected-Item leading stays outside its Error group under `AssignmentTail`; Error interior leading belongs to that group. Ordinary EOF may emit selected owner-leading before Missing and anchors at physical EOF. |
| diagnostic projection | A direct Missing or one maximal adjacent direct Error-token group under the immediate `AssignmentTail` parent projects one `Assignment(Rhs)` occurrence with expected `Expression`, primary alternative zero. Missing uses its direct zero-width Rowan range; Error uses the combined UTF-8 range of that maximal group. Initial/retry/protected-boundary leading, Equals, and the direct `OperatorChain` split the group. Projection is preorder: this direct Rhs occurrence precedes recovery projected by a nested RHS `OperatorChain`; no parser-record coordinate relocates the Rowan range. |
| proof and status | Governing slice: [error-admission clarification](2026-09-09-successor-error-admission-schema-clarification.md#representative-schema-slice-assignmenttail-inline-rhs), Authoritative for this direct-inline slice only. Verified source links: `crates/yu-syntax/src/expression/tails/assignment.rs:29` (AssignmentTail/Equals and terminal exit), `:90` (inline Rhs classification, Missing/Error/retry and handoff), `crates/yu-syntax/src/expression/tails/inline_slot.rs:34` (shared inline protected-boundary and leading rule), and `crates/yu-syntax/src/expression/operator_chain.rs:579` (Equals admission after enabled continuation/LED priority). Status: `mapped` for this Authoritative direct-inline RHS row only; `Assignment(IndentedStatement)`, the left expression, all other AssignmentTail contexts, the CST interpreter, recovery-ledger retirement, and API migration remain open. |

## Existing evidence-complete Draft slices

The following references report Draft evidence complete, not promotion to
Authoritative status. They remain bounded slices and do not complete their
families or the global catalog.

| Slice | Reference | Promotion |
| --- | --- | --- |
| FieldTail Name / PathTail Segment | error-admission clarification, **Proposed schema slice: fixed FieldTail and PathTail names** | user promotion open |
| StringLiteral terminator | error-admission clarification, **Proposed schema slice: StringLiteral terminator** | user promotion open |
| Rule-owned closes/capture/names/sequence | error-admission clarification, **Proposed schema slice: dedicated Rule literal slots** | user promotion open |
| StringInterpolationBody statement sequence | error-admission clarification, **Proposed schema slice: StringInterpolationBody statement sequence** | user promotion open |
| TypePathTail segment | bounded mapped row above; error-admission clarification, **Proposed schema slice: TypePathTail segment** | user promotion open; all other Type contexts remain open |
| LeadingEffectTypeHead | error-admission clarification, **Proposed schema slice: LeadingEffectTypeHead** | user promotion open |
| BracketRow required-arrow continuation | error-admission clarification, **Proposed schema slice: BracketRow-selected required-arrow continuation** | user promotion open |
| actual-arrow TypeArrowTail RHS | error-admission clarification, **Proposed schema slice: TypeArrowTail actual-arrow RHS** | user promotion open |

The AssignmentTail direct-inline RHS slice is intentionally absent from this
table because its mapped row above is externally Authoritative, rather than an
evidence-complete Draft.

## Open, delegated, and unmapped policy

Use these statuses for catalog rows:

| Status | Meaning |
| --- | --- |
| `unmapped` | no semantic-slot row has yet been written |
| `delegated` | the parent row intentionally relies on a separately named child slot; that child is not thereby complete |
| `referenced` | a governing authority or bounded slice exists elsewhere; the catalog has not duplicated it |
| `evidence-complete Draft` | direct CST proof is reported complete, but promotion remains open |
| `Authoritative slice` | user-approved bounded schema authority; surrounding rows remain independent |
| `mapped` | all mandatory row facts have been recorded and independently audited; this never implies global catalog completion |

Source sites are evidence links only. Map a helper/caller to a semantic slot
only after its produced direct-child phase and all necessary parent/caller
context are identified. A shared helper may evidence multiple rows; a single
row may require multiple source sites. The coverage manifest is neither a
future parser diagnostic ledger nor a substitute identity field.

Stop the affected mapping and return to the owning schema/design gate if any
required diagnostic cannot be selected from CST plus documented slot context;
two distinct expected roles have indistinguishable topology; a row would need
opaque Error relexing, hidden recovery provenance, or a parallel ledger; a
new `Invalid` owner would be needed; or an authority/continuation/boundary
contract conflicts. Do not manufacture a Missing, collapse alternatives, or
promote the catalog to resolve such a contradiction.

## Completion boundary

This catalog scaffold is not the complete per-slot schema. Full mapping,
ordered schemas, direct evidence where required, independent audit, and any
later CST interpreter/parser-ledger/API migration remain open. It authorizes no
parser, API, test, benchmark, or public-reference change.
