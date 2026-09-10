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
| expression tails and required operands | assignment, annotation, colon/with, fixed access, required operands, delimited expression phases | partial: the authoritative AssignmentTail direct-inline RHS row, the dedicated Field/Path evidence-complete Draft slices, bounded ProjectionRecordSpreadItem RHS row, and bounded expression-delimited raw Item/Separator/foreign-close rows are mapped; all other rows remain open |
| expression forms and statement/layout containers | case/if/for, source-root, statement and virtual-statement sequences | partial: Root direct raw-Error ordered-context matrix is recorded as candidate evidence only; all source-root, statement and virtual-statement schema rows remain open except listed delegated links |
| pattern and structured delimiters | Pattern entries, delimited sequences, RecordPattern Item/Separator structured recovery | partial: the bounded item/separator structured Invalid rows and foreign-close raw Error row are mapped; every other Pattern row remains open |
| type entries, tails and delimiters | type expression, paths, rows, variants, forall, delimited closes and TypeCall close | partial: the bounded LeadingEffectTypeHead, `TypePathTail` segment, TypeCall-close, CallArgument, separator and Forall first-binder rows are mapped; all other Type production contexts remain open |
| literal, interpolation and rule | String terminator, escape/interpolation braces, interpolation sequence, Rule-owned slots, ExpressionList delegation | partial: listed evidence-complete Draft slices, including audited StringEscape/interpolation-brace and Rule ExpressionList caller slots; direct-caller fence evidence remains open |
| declarations and headers | declaration heads, fields, variants, companions, imports, operator headers and payloads | partial: the catalog-audited bounded OperatorHeader and DerivesClause ViaTarget evidence-complete Drafts are mapped; every other declaration/header row remains open |

## Fixed topology references

### The two and only two current structured `Invalid` rows

These are topology references, not new admissions. The Error/Invalid ordering
addendum permits only these two structured owners. Their nested syntax remains
child-owned and must be cataloged in its own row before ledger retirement.

| Semantic slot identity | Exact structural nesting | Status |
| --- | --- | --- |
| `(PolymorphicVariantTag, wrong-kind TagName head before payload children, direct tag in PolymorphicVariantType)` | see the bounded PV row below | fixed existing structured owner; mapped |
| `(RecordPattern, Item or Separator in its record sequence phase, RecordPattern sequence context)` | item phase: `RecordPattern(Invalid(Pattern(...)))`; separator phase: see the bounded separator row below | fixed existing structured owner; both bounded phase rows are mapped, while the full sequence remains open |

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
| proof and status | Governing behavior: [PV current-Item recovery](2026-09-08-successor-pv-current-item-recovery.md) §§Acceptance and supersession, Typed PV sites, and Pre-write controls. Direct proof locators: `tests/type_expr/pv_recovery.rs:263–303`; `tests/type_expr.rs:6735–6832, 7085–7176, 8173–8254`; `tests/type_expr/bracket_arrow_recovery.rs:216–221`; `tests/type_expr/forall_recovery.rs:829–865`; `tests/type_expr/record_field_recovery.rs:368–374`. Status: `mapped`; temporary recovery records are proof only, never row identity or a future ledger. |

### ForallType first required-binder candidate

This bounded candidate maps only the first required binder immediately after
`ForKw`, before any accepted binder. It excludes later binder-boundary recovery,
colon/body, nested Type, caller continuation and close/stop ownership. It adds
no node: the existing `ForallTypeBinder` wrapper is the CST-visible first-slot
context.

| Fact | Candidate catalog row |
| --- | --- |
| identity | `(ForallType, first required binder immediately after ForKw and before any accepted binder, direct forall head context)` |
| ordered Rowan grammar | `ForallType := ForKw FirstBinderPhase …`. The bounded `FirstBinderPhase` is either an empty direct `ForallTypeBinder(Missing)`, or one incomplete direct `ForallTypeBinder(NativeInitialTrivia* Error+)`, before the head resumes. A locally admitted colon appears as a later direct `Colon` sibling; its leading stays direct ForallType content before the empty wrapper. An accepted/retried binder is a later direct `ForallTypeBinder` child and is excluded. Raw Error leaves are token leaves; no Error node or Invalid is admitted. |
| malformed admission and completion | Before an accepted apostrophe/SigilIdentifier binder, a fresh local literal colon admits the direct Missing then delegates to colon/body. Protected abstract/caller/outer/separator/close boundaries, non-continuation layout, EOF and fence admit one Binder Missing and preserve their existing handoff, except only for non-continuation layout where a matching local close already opened inside the malformed run (and its newline) remains raw Error content. Any other nonempty local content forms one maximal first-binder Error run in the incomplete wrapper with its matching-kind stack. Only a top-level actual binder or local colon retries the head; a nested binder/colon stays raw only after protected boundary checks, so a nested caller/contextual stop remains unchanged for handoff. Error-to-binder/colon retry adds no duplicate Missing and this phase never independently admits a body. |
| nested ownership | This row owns no nested grammar. The existing raw scanner's matched opener/close fragments remain Error leaves only; accepted/retried binder, colon/body, recursive Type and their recovery stay child-owned. Unmatched close, caller stop and outer separator remain protected. Later BinderBoundary belongs to the excluded accepted-binder phase. |
| source and boundary ownership | Initial malformed leading emitted by first-binder entry is native inside its `ForallTypeBinder` and outside Error. Fresh colon leading is native direct ForallType content before the Missing. After Error, binder leading belongs to the accepted binder and colon leading belongs to direct ForallType before its retried colon; neither is Error-wrapper content. Protected caller/newline/fence/EOF attempts retain existing pending Item/leading ownership; ordinary terminal leading remains outside the slot. Do not generalize this placement to actual binders: their required trivia and BinderBoundary Missing belong to the excluded later phase. |
| transition/handoff | `ForKw → classify before any accepted binder (protected boundary > fresh local colon > binder > malformed) → emit direct Binder Missing, consume one maximal incomplete-binder Error group with matching-close stack, or defer to accepted binder → fresh local colon emits native leading then Missing and delegates to existing colon/body; after Error only top-level classified binder/colon retries without Missing, otherwise return the classified protected Item unchanged with leading/origin/line/remainder → direct Missing or maximal wrapper Error group witnesses singleton ForallTypeBinder, primary zero`. |
| diagnostic projection | Direct wrapper Missing projects singleton ForallTypeBinder at its zero-width range. A maximal raw Error-token group under the immediate incomplete ForallTypeBinder projects the same singleton over its combined UTF-8 range. ForKw, native leading, colon/body, later accepted binder and handoff project none here. Rowan order puts this occurrence before its admitted colon/body or accepted binder; no Error spelling or temporary record payload is classification input. |
| proof and status | Governing authority: [Forall current-Item recovery](2026-09-08-successor-forall-current-item-recovery.md). Publishers: `crates/yu-syntax/src/type_expr/forall.rs:56–74,142–258,269–315,319–381,498–542`. Direct ordered CST proof: `crates/yu-syntax/src/tests/type_expr/forall_recovery.rs:71–183`; existing exact record/frozen/boundary/nested proof: `:412–592,594–827,829–908`. Status: catalog-audited evidence-complete Draft for this bounded first-binder row only; no parser/API/SyntaxKind or ledger-retirement claim. |

### ForallType later BinderBoundary candidate

This bounded candidate maps the `BinderBoundary` phase only after at least one
accepted binder. It covers the omitted boundary immediately before an actual
next binder and the one-item separator error that represents a failed attempt
to continue that binder sequence. It does not map the following colon/body
phase, any other malformed Forall head content, nested Type, caller
continuation, or close/stop ownership. It adds no node: the existing ordered
`ForallTypeBinder` siblings are the CST-visible context.

| Fact | Candidate catalog row |
| --- | --- |
| identity | `(ForallType, later BinderBoundary phase after one or more accepted ForallTypeBinder siblings, direct forall head context)` |
| ordered Rowan grammar | `ForallType := ForKw AcceptedBinder+ LaterBinderBoundaryPhase …`. In the omitted-boundary alternative, `LaterBinderBoundaryPhase := ForallTypeBinder(Missing SigilIdentifier)`: the `Missing` is the first direct child of the next actual binder. In the separator alternative it is `ForallTypeBinder(Error)`, followed either by a retried `ForallTypeBinder((Missing)? NativeLeading* SigilIdentifier)` or by the separately owned direct colon/body sequence. Raw `Error` is a token leaf and `Missing` is zero-width; neither is an Error node or Invalid. The preceding accepted binder and following sibling order distinguish this phase from the first-binder wrapper and from the direct ForallType colon Missing. |
| malformed admission and completion | An immediately adjacent actual binder with grammar-empty leading publishes one BinderBoundary Missing inside that binder, then emits its SigilIdentifier. A local sequence separator emits exactly that separator as a one-item raw Error in its own placeholder binder and advances once. Its following actual binder has its normal leading-sensitive behavior: grammar-empty leading produces a distinct BinderBoundary Missing; nonempty permitted leading does not. An admitted literal colon delegates directly to body parsing with no colon Missing; a missing colon/body after the placeholder is separately owned by the direct ForallType phase and excluded. Other malformed head material follows its separately owned phase behavior; this row does not absorb or relabel it. |
| nested ownership | The row owns neither the content of an admitted binder nor any nested grammar. A retried binder, its leading and identifier remain its own `ForallTypeBinder` child; colon/body, recursive Type and their recovery remain child-owned. The one-item separator placeholder has no structured child. |
| source and boundary ownership | The omitted-boundary Missing is emitted before the next binder's leading and token only when that binder's leading is grammar-empty. The separator's leading, if any, is native content of its placeholder binder before the raw Error token. After the placeholder, successor leading belongs to the retried binder or to the excluded direct colon/body phase. A returned caller boundary, close, fence, EOF or layout item is not claimed by this row. |
| transition/handoff | `accepted binder → inspect next Item → actual adjacent binder: emit BinderBoundary Missing then binder when its leading is grammar-empty; local separator: emit one placeholder Error then inspect successor; otherwise defer to the existing later head phase → a retried binder applies its own leading-sensitive Missing rule, while an actual colon or colon/body/boundary is handed to its existing owner → each immediate ordered binder wrapper witnesses its singleton BinderBoundary, primary zero`. |
| diagnostic projection | `ForallTypeBinder(Missing, SigilIdentifier)` projects singleton `TypeBinderBoundary` when it follows an accepted binder in this direct head sequence, including after a separator placeholder. An immediate placeholder `ForallTypeBinder(Error)` in the same ordered context projects its own BinderBoundary occurrence over its Error-token range, whether its successor is a later binder or the separately owned colon/body phase. The direct ForallType Missing after that placeholder projects no BinderBoundary occurrence, and an admitted literal colon projects none in this row. The interpreter uses wrapper/child/sibling context and Rowan order only; Error spelling and temporary recovery records are not inputs. |
| proof and status | Governing authority: [Forall current-Item recovery](2026-09-08-successor-forall-current-item-recovery.md). Publishers: `crates/yu-syntax/src/type_expr/forall.rs:142–258,326–357,379–381,498–542`. Direct ordered CST proof: `crates/yu-syntax/src/tests/type_expr/forall_recovery.rs:288–410`; existing role/range/frozen/boundary controls: `:412–543,594–650,652–827,867–908`. Status: catalog-audited evidence-complete Draft for this bounded later BinderBoundary row only; no parser/API/SyntaxKind or ledger-retirement claim. |

### ForallType terminal emitted-colon/body candidate

This bounded candidate maps the direct terminal colon/body phase after one or
more accepted binder siblings, for the emitted `Colon` token. Ordinary colon
and lexical `PolymorphicVariantColon` both emit that same Rowan token here, so
they have one shared CST row rather than unrecoverable lexical subrows. It
excludes a recovered binder after malformed colon content, first/later binder
phases, nested Type, caller continuation and close/stop ownership. It adds no
node: `Missing`, raw `Error` tokens, `Colon` and `TypeExpression` remain direct
ordered children of `ForallType`.

| Fact | Candidate catalog row |
| --- | --- |
| identity | `(ForallType, terminal emitted Colon then canonical Type body after accepted ForallTypeBinder+, direct forall head context)` |
| ordered Rowan grammar | The bounded direct sequence is `ForallType := ForKw AcceptedBinder+ NativeLeading* TerminalColonBody`. Its admitted alternatives are `Colon NativeLeading* TypeExpression`, `NativeLeading* Missing TypeExpression` for an absent colon retried by an admitted body, and `Colon Missing` for an absent body. A maximal raw Error-token group can be direct ForallType content before a retrying `Colon` or after an admitted `Colon` before a retrying `TypeExpression`; native retry leading remains a direct sibling outside that Error group. `Missing` is zero-width and every Error is a token leaf; no Error node or Invalid is admitted. |
| malformed admission and completion | A present emitted colon delegates directly to canonical Type admission. An admitted canonical body before colon emits one colon Missing and retries that body. A boundary after an admitted colon emits one body Missing and preserves the boundary handoff. A non-body after colon forms a raw body Error group and may retry a canonical body without another body Missing; a non-colon before colon similarly forms a raw colon Error group before a retrying colon. Recovered-binder and protected-boundary paths are deliberately excluded rather than relabeled. |
| nested ownership | `TypeExpression` owns every body primary, continuation and nested Missing/Error/Invalid topology. The row owns no binder internals, no recovered binder, and no content under a structured body. Raw colon/body Error tokens have no wrapper or structured child in this row. |
| source and boundary ownership | Leading before a present colon or the canonical body retried after a colon Missing is native direct ForallType content. A raw colon/body Error group owns only its malformed run; retry leading remains direct ForallType content. For a missing body, caller/close/fence/EOF/layout Item and its protected leading retain the existing pending handoff; this row neither consumes nor reconstructs it. |
| transition/handoff | `accepted binders → inspect terminal Item → emitted Colon: admit body; canonical body before Colon: emit colon Missing then retry body; malformed colon/body: consume one raw direct Error group then retry its locally admitted successor; body boundary: emit body Missing and return the unchanged boundary Item → direct Missing or direct Error group witnesses the ordered terminal slot, primary zero`. |
| diagnostic projection | A direct Missing before an admitted `TypeExpression`, with no preceding direct `Colon` in this terminal sequence, projects singleton colon punctuation. A direct Missing immediately after `Colon` projects singleton TypeExpression. A direct raw Error group before the terminal `Colon` projects the colon slot; one after it projects the body slot. This distinction is ancestor/sibling order and token ranges only: Error spelling, recovery records, body text and erased lexical colon provenance are not inputs. |
| proof and status | Governing authority: [Forall current-Item recovery](2026-09-08-successor-forall-current-item-recovery.md). Publishers: `crates/yu-syntax/src/type_expr/forall.rs:142–258,269–315,407–496,498–542`. Direct ordered CST proof: `crates/yu-syntax/src/tests/type_expr/forall_recovery.rs:186–286`; existing exact record/boundary/frozen controls: `:412–592,594–827`. Status: catalog-audited evidence-complete Draft for this bounded terminal emitted-colon/body row only; no parser/API/SyntaxKind or ledger-retirement claim. |

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

### TypeCall CallArgument item-phase candidate

This bounded candidate records only one required Type item after accepted
`LParen` or `Comma`, before the separately mapped terminal `TypeCallClose`.
It excludes separator recovery, close recovery, caller boundaries and every
nested Type slot. It selects no new CST topology: ordinary malformed argument
fragments remain direct `Error` token leaves.

| Fact | Candidate catalog row |
| --- | --- |
| identity | `(TypeCallTail, one required CallArgument after LParen or Comma and before TypeCallClose, TypeCall context)` |
| ordered Rowan grammar | This is a bounded item grammar, not a complete `TypeCallTail` production: `left item predecessor (LParen \| Comma) → owner-native leading? → (TypeExpression \| Missing \| Error+ (TypeExpression \| ContinuationTrivia TypeExpression)?) → delegated separator or TypeCallClose`. Eligible same-line retry prefixes are part of `Error+`; only the T3 continuation trivia is direct native TypeCallTail content between Error and its retried TypeExpression. The surrounding tail independently owns repeated punctuation, semicolon/comma separator phases and their Missing routes. Initial and post-comma item Missing are direct `TypeCallTail` children; raw argument Error leaves are also direct children. An admitted argument is one direct `TypeExpression`; its full Type continuation remains nested. `TypeCallClose` is separately mapped. No Error node or Invalid is admitted for ordinary argument recovery. |
| malformed admission and completion | At an item position, an admitted Type primary creates one `TypeExpression`; a required absence creates one direct zero-width Missing. A nonempty malformed run is contiguous direct `Error+`. An adjacent admitted Type retry, including its T3-authorized continuation leading, follows the same Error group without duplicate Missing; the Error leaves precede its direct TypeExpression. Matching close, separator, ordinary EOF, caller/outer boundary, active stop and fence terminate the item according to the existing T3 handoff; this row does not consume or classify their separate owner slots. |
| nested ownership | The direct nested `TypeExpression` owns all Type grammar, its continuations and its own Missing/Error topology. The parent TypeCallTail separately owns punctuation/order; `TypeCallClose` owns terminal close Missing/Error. A direct CallArgument Error group cannot be a close group because the latter has immediate parent `TypeCallClose`. |
| source and boundary ownership | Leading already emitted by initial/post-separator item entry remains native `TypeCallTail` content outside Error; Error-internal leading remains direct raw Error leaves. The observed eligible retry-leading space in `T(@ A)` is a direct Error token, not native trivia or a wrapper child. Accepted/retried Type leading, comma-leading and terminal-close leading retain their existing owners. At a fresh initial or post-separator caller/outer boundary with ordinary horizontal leading, the owner emits that gap natively, publishes item Missing at the advanced frontier, and returns the remaining Item; other protected leading remains pending with its origin, line and remainder unchanged. Direct Missing uses its Rowan zero-width range. |
| transition/handoff | `accepted LParen/Comma item entry → existing absence/boundary priority selects direct Missing or returns protected Item; otherwise admitted Type primary wins and creates TypeExpression, while malformed payload starts direct Error leaves → retry only an admitted Type in the same item position; otherwise let existing separator, terminal close or caller/boundary path take the unchanged successor → the direct Missing or maximal adjacent Error group witnesses singleton TypeExpression, primary zero`. |
| diagnostic projection | A direct item Missing projects singleton TypeExpression at its zero-width range. One maximal adjacent direct Error-token group under TypeCallTail at the selected item position projects the same singleton over the combined UTF-8 range. Ordered punctuation and the immediate `TypeCallClose` child distinguish initial/post-comma item occurrences from close recovery, including same-offset `T(` argument/close Missing. Error spelling and temporary record payloads are not classification input; nested Type diagnostics follow this direct occurrence in preorder. |
| proof and status | Governing behavior: [T3 TypeCall recovery](2026-09-07-successor-t3-typecall-recovery-amendment.md) §§2.1, 3.1–3.3, [shared delimited boundary-priority correction](2026-09-07-successor-delimited-boundary-priority-correction.md) §2 and [TypeCall close slot](2026-09-10-successor-typecall-close-slot-node.md). Direct phase proof: `crates/yu-syntax/src/tests/type_expr/type_call_fallback.rs:120–206`; existing Missing/retry/fresh/frozen/shifted/caller/fence/close controls: `crates/yu-syntax/src/tests/type_expr.rs:3361,4503,4588,4731,4820,4868,5002,5027,5062,5179` and `type_call_fallback.rs:5–104,154–284`. Publishers: `crates/yu-syntax/src/type_expr/delimited.rs:108–130,568–609,814–931,1164–1176`. Status: catalog-audited evidence-complete Draft for this bounded item row only; no parser/API/SyntaxKind change and no ledger retirement claim. |

### TypeCall separator-phase candidate

This bounded candidate covers the separator position after a completed
CallArgument and before its next CallArgument or separately mapped
TypeCallClose. It does not turn every physical newline into a separator, map
the next required item, or classify residual close recovery.

| Fact | Candidate catalog row |
| --- | --- |
| identity | `(TypeCallTail, separator after completed CallArgument before next item or TypeCallClose, TypeCall context)` |
| ordered Rowan grammar | The bounded phase is `completed TypeExpression → (native Comma \| native Semicolon \| inherited-ML native eligible leading + Missing)? → delegated next CallArgument or TypeCallClose`. Ordinary layout continuation may instead be native newline between two direct TypeExpression siblings with no separator recovery. The optional punctuation is accepted only when actually present. An inferred separator is only the direct zero-width Missing after inherited-ML eligible nonempty leading and before an admitted next Type; it is not a general whitespace rule. No separator Error, Error node or Invalid exists. |
| malformed admission and completion | An explicit comma or semicolon completes the separator phase and enters a fresh CallArgument; trailing explicit punctuation may enter terminal close without a new item Missing. Only inherited-ML omission followed by an admitted next Type emits the direct separator Missing, then retries that next Type. Matching close and protected caller/outer/fence boundaries outrank inference. `T(A,,B)` is not separator recovery: after the first accepted comma it is the next item Missing before a second native comma. `T(@, A)` retains direct CallArgument Error before native comma, while `T(A@,B)` enters residual terminal close recovery under TypeCallClose. |
| nested ownership | Completed/next TypeExpression children retain all Type grammar and their nested diagnostics. CallArgument owns its direct Error/Missing; TypeCallClose owns terminal Missing/Error. The separator phase owns only its direct punctuation or inferred Missing and eligible leading. Its direct order separates these siblings without Error spelling or parser provenance. |
| source and boundary ownership | Leading before an explicit comma/semicolon is native TypeCallTail content. Leading after explicit punctuation belongs to the fresh CallArgument phase. In the inherited-ML inference branch, eligible horizontal or deeper LF/CRLF leading is emitted natively before direct separator Missing; it is outside Missing and the next TypeExpression. Ordinary layout newline is native between accepted TypeExpression siblings without Missing. After a completed item, ordinary horizontal caller/outer boundary gap is emitted directly by TypeCallTail before close publication and the remaining payload Item returns at its advanced frontier; an already-classified abstract boundary instead retains its entire gap pending. Matching terminal leading remains terminal-owner content. |
| transition/handoff | `completed CallArgument → matching close/protected boundary priority with the phase-specific gap disposition above; otherwise explicit Comma/Semicolon wins and opens fresh item; otherwise inherited-ML eligible leading plus admitted next Type emits direct separator Missing then retries it; otherwise ordinary layout continuation stays native/no-Missing → delegate the fresh item, terminal close or the appropriately advanced/pending protected successor to its owner → direct Missing witnesses singleton DelimitedSequenceSeparator, primary zero`. |
| diagnostic projection | The direct inferred Missing projects singleton DelimitedSequenceSeparator at its zero-width range. Accepted punctuation and ordinary-layout native newline project none. It is ordered after recovery from the completed TypeExpression and before recovery inside the next TypeExpression; TypeCallClose's nested Missing/Error has its separate parent/path. No raw Error group projects this row. |
| proof and status | Governing behavior: [T3 TypeCall recovery](2026-09-07-successor-t3-typecall-recovery-amendment.md) §§2.1–2.2, 3.3, [shared delimited boundary-priority correction](2026-09-07-successor-delimited-boundary-priority-correction.md) §2 and [TypeCall close residual policy](2026-09-10-successor-typecall-close-residual-policy.md), Selected policy. Direct phase/frozen proof: `crates/yu-syntax/src/tests/type_expr/type_call_fallback.rs:52–218`; existing inherited-ML/boundary controls: `crates/yu-syntax/src/tests/type_expr.rs:3355–3532,7457–7555,7817–7875`. Publishers: `crates/yu-syntax/src/type_expr/delimited.rs:73–79,360–507,1140–1210,1299–1330`; separator recognition: `crates/yu-syntax/src/type_expr/mod.rs:2883–2888`. Status: catalog-audited evidence-complete Draft for this bounded separator row only; no parser/API/SyntaxKind change or ledger-retirement claim. |

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

### StringEscape and StringInterpolation brace slots map

This bounded existing-grammar map covers only direct recovery-bearing children
of StringEscape and StringInterpolation. It delegates StringInterpolationBody
to its separately mapped row and StringLiteral termination to its preceding
row; it does not alter literal scanning, prefixes, StringPiece or outer source
ownership.

| Fact | Draft catalog row |
| --- | --- |
| identity | `(StringEscape, simple target / Unicode hex / Unicode end, direct StringLiteral piece context)` and `(StringInterpolation, required open brace / final close brace, direct StringLiteral piece context)` |
| ordered Rowan grammar | `StringEscape := YmQuotePrefix? StringEscapeLead (StringEscapeSimple \| Missing(SimpleTarget) \| StringEscapeUnicodeStart (StringEscapeUnicodeHex Error+? \| Error+ \| Missing(UnicodeHex)) (YmQuotePrefix? StringEscapeUnicodeEnd \| Missing(UnicodeEnd)))`. `StringInterpolation := YmQuotePrefix? StringInterpolationPercent (StringInterpolationFormatText \| YmQuotePrefix)* (StringInterpolationOpenBrace StringInterpolationBody (CloseLeading* StringInterpolationCloseBrace \| Missing(CloseBrace)) \| Missing(OpenBrace))`. Empty format is legal; quote prefixes can split it. The two consecutive Unicode Missing children have distinct ordered slots; the nested body and final StringLiteral Missing are distinct child paths. |
| malformed admission and completion | A simple target Missing occurs only after StringEscapeLead without UnicodeStart at a string close/EOF. Unicode Error+ occupies the direct hex position after UnicodeStart, whether or not a preceding accepted UnicodeHex exists; hex Missing occupies that same slot only when no hex/Error was admitted. The following end token/Missing is the direct Unicode-end position. Interpolation OpenBrace Missing completes the interpolation and returns the unchanged pending boundary; CloseBrace Missing follows the completed Body on its boundary exit. Neither branch creates Invalid, relexes Error spelling or emits a second owner-local recovery node. |
| source and boundary ownership | Escape Error physical fragments remain inside the direct StringEscape hex group; direct quote prefixes can precede StringEscapeLead or an accepted Unicode end. Interpolation format/prefix fragments remain before its open slot. After Body finishes with an accepted close, its returned close Item emits existing close-leading native trivia directly under StringInterpolation before CloseBrace; that leading is not Body content. A Body boundary emits direct CloseBrace Missing without that close-leading. The outer StringLiteral owns its separate final terminator and its pending boundary. |
| diagnostic projection | Direct Missing/Error+ after StringEscapeLead selects StringEscapeSimpleTarget / StringEscapeUnicodeHex by its preceding structural child; the final direct Unicode end Missing selects StringEscapeUnicodeEnd. Direct StringInterpolation Missing before Body selects OpenBrace; direct Missing after Body selects CloseBrace. Each uses its direct Rowan range, primary zero and preorder. Equal offsets never merge roles because immediate child order/path differs. |
| proof and status | Existing authority: [StringLiteral current-Item recovery](2026-09-08-successor-string-literal-current-item-recovery.md). Direct publishers: `crates/yu-syntax/src/literal/mod.rs:420–490, 627–794`; direct CST/record/frozen/shifted proof: `crates/yu-syntax/src/tests/literal.rs:819–1063, 1094–1200, 1387–1396` and `crates/yu-syntax/src/tests/string_literal_recovery.rs:450–503, 570–620`. Status: `catalog-audited evidence-complete Draft` for these five literal slots only; StringPiece scanning, all body contents, prefixes, outer terminator, interpreter, ledger and API migration remain open. |

### RecordPattern item-phase structured Invalid map

This bounded Draft row maps only the existing direct structured recovery that
admits one canonical Pattern while a RecordPattern sequence expects its next
item. It is deliberately distinct from the separator phase's
`RecordPatternSeparator` wrapper. It neither maps preceding raw Error groups,
fresh-comma Missing, close recovery, accepted fields/defaults/spreads, or any
nested Pattern slot.

| Fact | Draft catalog row |
| --- | --- |
| identity | `(RecordPattern, item phase wrong-kind Pattern, RecordPattern sequence context)` |
| ordered Rowan grammar | `RecordPattern := ... Invalid(Pattern(...)) ...` for this direct item phase. `Invalid` is a direct `RecordPattern` child with exactly one direct canonical `Pattern` child in scope; it has no `RecordPatternSeparator` parent, Error token, punctuation, leading, or sibling recovery child. Leading already emitted by the RecordPattern sequence stays before this direct Invalid. |
| malformed admission and completion | Matching local close and carried caller close win before this slot. A fresh comma follows its separate sequence Missing rule. Only an Item which is not a record name/spread start but is admitted by the existing canonical Pattern NUD selects this structured item recovery. The full nested Pattern is consumed under existing stops/baseline/line/fence/ambient context. A returned comma is consumed by the existing record sequence without an invented item Missing; returned local close remains outside Invalid, while protected caller/fence Items and their leading remain pending. |
| nested ownership | The direct `Pattern` child owns its own literals, delimiters, tails, Missing, Error and any nested Invalid topology. This outer Invalid retains that child as wrong-slot structure but does not claim a Pattern-internal diagnostic. The enclosing RecordPattern keeps all accepted items, comma handling, close recovery and raw-error grouping. |
| source and boundary ownership | RecordPattern owns fresh sequence leading and emits it before entry. Invalid covers the full nested Pattern extent, never merely the wrong-kind head token; same-line EOF trivia that the nested Pattern consumes remains nested source. A returned comma/close is neither consumed nor emitted by Invalid. Protected caller/fence leading stays with the pending returned Item. |
| transition/handoff | `record Item phase → local/caller close and comma priority, then name/spread admission; a remaining canonical Pattern NUD selects structured item recovery → consume one direct Invalid(Pattern(...)) → complete the nested Pattern and resume the existing item phase; consume a returned comma outside Invalid without duplicate item Missing, or hand off a protected boundary unchanged → the direct Invalid witnesses singleton Identifier, primary zero.` |
| diagnostic projection | Entering the direct Invalid projects one structured wrong-slot occurrence with expected `Identifier`, primary alternative zero, and the UTF-8 `Invalid.text_range()`. It is emitted before recursively visiting the nested Pattern's own occurrences. Its occurrence identity derives from this direct item slot, not Error spelling, parser origin, reservation, record ID, unexpected category, expectation-source flag, or a boundary coordinate. |
| proof and status | Governing authority: [RecordPattern separator-slot amendment](2026-09-10-successor-record-pattern-separator-slot.md) §§Problem and selected representation, CST and diagnostic contract; existing sequence behavior: [Pattern sequence current-Item recovery](2026-09-08-successor-pattern-sequence-current-item-recovery.md) and [Pattern delimited slot publication](2026-09-08-successor-pattern-delimited-slot-publication.md). Direct publisher links: `crates/yu-syntax/src/pattern/delimited.rs:239–324, 477–538, 972–985`. Direct CST proof: `crates/yu-syntax/src/tests/pattern/recovery/sequence.rs:239–364, 408–458, 460–529, 624–695, 697–795, 859–961, 964–1052`. Status: `mapped` after independent audit for this bounded Draft row only; the separator row, foreign-close raw Error row, all remaining sequence/Pattern rows, interpreter, recovery ledger and API migration remain open. |

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
| ordered Rowan grammar | The separator phase is `RecordPatternSeparator(Invalid(Pattern(...)))`. `RecordPatternSeparator` has this existing `Invalid` as its only child in scope; the separately mapped direct item phase is `RecordPattern(Invalid(Pattern(...)))`. |
| malformed admission and completion | Only the existing RecordPattern separator-phase structured-recovery path enters this row, after matching local close and accepted comma priorities. It preserves the existing nested Pattern parse and does not wrap a raw Error, accepted comma, accepted item, item-phase Invalid, local close, or nested Pattern output. A recovered nested Pattern retries the sequence without an invented separator Missing; a returned comma is consumed by the existing sequence phase, while a protected caller/fence Item remains pending. |
| nested ownership | `Invalid` retains its direct range, preorder structured diagnostic, Pattern child, and nested recovery traversal. The nested Pattern retains its own schema. The wrapper adds neither a new Invalid owner nor an expectation of its own. |
| transition/handoff | `RecordPattern separator slot entry → after matching-close/comma priority, existing separator-phase structured recovery selects a wrong-kind Pattern → consume the existing Invalid and nested Pattern beneath one transparent RecordPatternSeparator, without independently consuming or emitting source; initial leading has already been emitted by RecordPattern and stays outside the wrapper → retry the sequence without a duplicate separator Missing, consuming a returned comma in the outer sequence; a returned close stays outside, while a protected caller/fence Item and its leading remain pending → the nested Invalid witnesses DelimitedSequenceSeparator, primary zero, over its unchanged text range before nested Pattern traversal`. |
| diagnostic projection | The transparent wrapper has no diagnostic, range, or expectation metadata. The enclosed `Invalid` projects `DelimitedSequenceSeparator`, primary zero, over `Invalid.text_range()` before recursively visiting its Pattern child. By contrast, the separately mapped direct item-phase Invalid is `(RecordPattern, item phase, RecordPattern sequence context)` with `Identifier`, primary zero. |
| proof and status | Governing authority: [RecordPattern separator-slot amendment](2026-09-10-successor-record-pattern-separator-slot.md), including its `{a)1}` separator versus `{a@1}` item collision witnesses; private construction: `8f99e18d`. Status: `mapped`. This is a referenced/mapped discriminator only, not a complete RecordPattern schema or a claim that the preceding raw Error is resolved. |

### RecordPattern foreign-close raw Error map

This bounded Authoritative row maps only a foreign close consumed while a
RecordPattern sequence remains open. It does not map direct lexical Item or
Separator Error groups, fresh-comma Missing, accepted fields/defaults/spreads,
local close, carried caller close, or nested Pattern recovery.

| Fact | Authoritative catalog row |
| --- | --- |
| identity | `(RecordPattern, one consumed foreign close, RecordPattern sequence context)` |
| ordered Rowan grammar | `RecordPatternForeignClose := Error+`. Each occurrence is a direct RecordPattern child containing one nonempty adjacent Error-token group and no node, Missing, Invalid, punctuation, accepted child or recovery sibling. It is emitted once per consumed foreign-close Item. Direct lexical Error groups remain direct RecordPattern children and retain their separately phase-selected Item or Separator identity. |
| malformed admission and completion | Matching local close, carried caller close and boundary paths win before this slot. An unclaimed `RParen`, `RBracket` or foreign `RBrace` is consumed exactly once by the existing wrong-close path without changing the sequence Item/Separator phase; the successor Item is read once under the unchanged local stops, baseline, line/fence and ambient context. No lexical run is merged into this slot. |
| nested ownership | The wrapper owns no nested grammar: all of its children are Error tokens. A following direct/transparent `Invalid(Pattern(...))` retains its own item or separator schema, and an accepted/retried Pattern remains child-owned. RecordPattern retains comma handling, local close, direct lexical Error groups and every remaining sequence phase. |
| source and boundary ownership | The wrapper range is its Error-token group's combined UTF-8 range. Leading already emitted by RecordPattern remains outside; leading still attached to the consumed foreign close is Error content inside. Matching local close, Missing, retry leading, protected caller/fence Item and its leading remain outside. Source flattening is unchanged. |
| transition/handoff | `RecordPattern sequence entry → boundary/local/caller-close priority, then foreign-close classification → consume exactly one foreign close as RecordPatternForeignClose(Error+) → preserve the current sequence phase and scan one successor → continue existing item/separator recovery, consume a local comma/close, or hand off a protected boundary unchanged → this wrapper's Error group witnesses Close(Brace), primary zero.` |
| diagnostic projection | The transparent wrapper projects no occurrence. Its one maximal direct Error-token group projects slot `ClosingDelimiter(RecordPattern, Brace)` with singleton expected punctuation `Close(Brace)`, primary zero, over the combined UTF-8 group range. The group precedes later direct/structured children in Rowan preorder. A repeated foreign close is a new wrapper and a new occurrence; direct raw Item/Separator groups are neither merged with it nor classified by Error spelling. |
| proof and status | Governing authority: [RecordPattern foreign-close CST slot](2026-09-10-successor-record-pattern-foreign-close-slot-draft.md); existing continuation/record authority: [Pattern sequence current-Item recovery](2026-09-08-successor-pattern-sequence-current-item-recovery.md). Direct owner: `crates/yu-syntax/src/pattern/delimited.rs:239–324, 553–577`; append-only kind: `crates/yu-syntax/src/syntax_kind.rs:275–280, 492–497, 736–760`. Direct Rowan proof: `crates/yu-syntax/src/tests/pattern/recovery/sequence.rs:5–202, 239–364, 798–856, 859–1052`. Status: `mapped` after independent closure audit for this bounded Authoritative row only; direct lexical Item/Separator Error groups, all remaining RecordPattern rows, interpreter, recovery ledger and API migration remain open. |

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

### Rule ExpressionList caller-specific slots map

This bounded Draft map records the existing direct Item, Separator and Close
occurrences delegated to `rule::expression_list`. `ExpressionList` is phase
notation only, never a Rowan node. The three caller rows are distinct and may
not be merged merely because two use brackets:

| Caller identity | Direct parent and necessary context | Delimiters |
| --- | --- | --- |
| `ExpressionList[RuleItem[LBracket]]` | direct RuleItem whose first atom is LBracket, within RuleSequence/RuleAlternation | LBracket … RBracket |
| `ExpressionList[RuleCall]` | direct RuleCall in a postfix RuleItem | LParen … RParen |
| `ExpressionList[RuleIndex]` | direct RuleIndex in a postfix RuleItem | LBracket … RBracket |

For a delimited completion, the ordered grammar is
`C := OpenC PhaseContents (CloseC | Missing(Close))`; a Deferred exit is the
same existing prefix of `PhaseContents` without either terminal child. The
phase table, rather than a node, restricts contents: Item phase admits direct
Expression, Error+ retry or Missing(Item); Separator phase admits direct Comma,
direct physical Newline, Error+, or its existing transition to Close. No Invalid
or Separator Missing is emitted by this owner. A matching close is caller-owned
after `ExpressionListExit::Close`; a foreign close is not consumed as Error.

| Fact | Draft catalog row |
| --- | --- |
| identity | `(one named ExpressionList caller above, required Item / Separator / final Close, direct caller context)` |
| malformed admission and completion | Required Item Error is a maximal adjacent direct Error group before the first completed Expression or after a direct Comma/Newline reset; it can retry one direct Expression. Separator Error is a maximal adjacent direct Error group after a completed Expression and before accepted comma/newline/close. Item Missing occurs at the existing required-item positions, including immediately before a direct physical LF/whole-CRLF Newline. At EOF, fence, boundary or foreign close, the list emits its caller Close Missing and returns the pending Item unchanged. A terminal Item Error followed by a matching close is ordered `Error+, Missing(Item), CloseC`; only boundary termination is `Error+, Missing(Item), Missing(Close)`. Equal ranges remain distinct by direct child ordinal and phase path. Empty and accepted trailing comma/newline contents introduce no Item Missing. |
| source and boundary ownership | Rejected Item leading is Error content. Retry leading belongs to its admitted Expression; protected/boundary leading stays pending on the returned Item. Matching-close leading and accepted native trivia are direct caller content. The newline helper emits Item Missing before its direct newline token at the physical LF/CRLF start. Foreign close, fence and Deferred exits preserve their Item/leading without local close emission. |
| diagnostic projection | A direct maximal Item Error/Missing projects singleton `Expression`; a direct maximal Separator Error projects `DelimitedSequenceSeparator`; the final direct Close Missing projects the caller's matching close punctuation. Projection is preorder. Adjacent Error leaves form one group only within the same direct parent and phase; no Error spelling or parser record is consulted. |
| proof and status | Governing authority: [Rule ExpressionList current-Item recovery](2026-09-08-successor-rule-expression-list-current-item-recovery.md) and [error-admission clarification](2026-09-09-successor-error-admission-schema-clarification.md), Rule ExpressionList phases. Direct owner/caller links: `crates/yu-syntax/src/rule/expression_list.rs:54–223`, `crates/yu-syntax/src/rule/mod.rs:513–538, 590–635`. Direct CST evidence: `crates/yu-syntax/src/tests/rule_expression_list_recovery.rs:139–209, 624–839, 895–932`. Status: `catalog-audited evidence-complete Draft`. The direct-caller fence CST/range proof remains open at `:842–893`; it does not create a slot collision or authorize a synthetic row. |

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

### ProjectionRecordSpreadItem required-RHS map

This bounded Draft row records only the required RHS after an already accepted
record-projection `DotDot`. It does not map ordinary record items, separators,
the local close, another spread marker, the enclosing projection tail, or the
nested RHS expression.

| Fact | Draft catalog row |
| --- | --- |
| identity | `(ProjectionRecordSpreadItem, required RHS immediately after direct DotDot, direct ProjectionRecordTail spread-item context)` |
| ordered Rowan grammar | `ProjectionRecordSpreadItem := MarkerLeading* DotDot (OperatorChain \| EofLeading* Missing \| InitialMalformedLeading* Error+ (OperatorChain)?)`. `MarkerLeading*` belongs before its direct `DotDot`; an ordinary EOF's remaining leading is native before the direct Missing. Initial malformed leading is native direct content before the adjacent raw Error leaves; internal malformed leading remains inside that Error group. A successfully admitted or retried RHS, including its retry leading, is the direct `OperatorChain` child. Protected-boundary leading is absent from this node because its pending Item returns unchanged. No direct `Invalid`, separator, close, or second Missing alternative is admitted. |
| malformed admission and completion | A directly admitted RHS becomes `OperatorChain`. Separator, close, an exact following spread marker, EOF, abstract boundary, or protected boundary before admission produces exactly one direct Missing, except that ordinary EOF emits its remaining leading first. A non-boundary non-NUD starts one maximal direct raw Error group. It stops before an admitted NUD, separator, close, exact spread marker, qualifying newline, EOF, or abstract boundary. An admitted NUD retries as this node's direct RHS; a returned newline-bearing non-NUD leaves this node for the parent sequence. Error ending at a boundary never adds an RHS Missing. |
| nested ownership | A direct RHS `OperatorChain` owns every accepted expression child and its nested recovery slots. Parent ProjectionRecord Item, Separator and Close slots remain outside this node, even where their later Missing has the same zero-width range. The direct Error group retains no nested grammar. |
| source and boundary ownership | The spread owner emits marker leading and `DotDot` before RHS classification. Its initial malformed leading is native direct node content; Error-internal leading belongs to the Error group. Retry leading belongs to the nested `OperatorChain`. Separator, close, subsequent exact spread-marker and protected-boundary Items retain their own leading and return unchanged to the parent sequence; the parent retains its own recovery ownership. |
| transition/handoff | `direct DotDot RHS entry → boundary/NUD/malformed classification after the marker → consume one direct OperatorChain, one zero-width Missing, or a maximal direct Error group → retry an admitted NUD locally without a duplicate Missing; otherwise hand off the unconsumed separator, close, exact next marker, EOF, newline or protected boundary to the record sequence → the direct Missing or maximal Error group witnesses singleton Expression, primary zero.` |
| diagnostic projection | The direct Missing projects `Expression` with primary alternative zero at its zero-width Rowan range. Each maximal adjacent direct Error-token group projects the same singleton expectation over its combined UTF-8 range. Direct RHS Error precedes diagnostics of a retried nested RHS; a direct RHS Missing precedes any later parent separator/close occurrence, including at an equal offset. Neither Error spelling nor parser-record provenance is consulted. |
| proof and status | Governing behavior: [expression delimited current-Item recovery](2026-09-08-successor-expression-delimited-current-item-recovery.md) §§Owner descriptor and exact records, Boundary capability, phases and continuation. Direct publisher links: `crates/yu-syntax/src/expression/delimited.rs:396–462`, `:476–496`, and `:519–590`. Direct Rowan proof: `crates/yu-syntax/src/tests/owners.rs:553–906`; retained record controls: `crates/yu-syntax/src/tests/delimited_recovery.rs:304–335, 517–555`. Status: `mapped` for this bounded Draft row only after independent closure audit; all excluded parent/nested slots, the interpreter, recovery ledger and API migration remain open. |

### Expression-delimited raw Item, Separator and foreign-close map

This bounded Authoritative map covers only raw `Error` token groups in the
existing ParenthesizedExpression, CallTail, IndexTail, ProjectionTupleTail and
ProjectionRecordTail sequences. It does not map their accepted items,
punctuation, Missing slots, local matching closes, protected inherited closes,
fence handoff, nested OperatorChain recovery, or ProjectionRecordSpreadItem.

| Fact | Authoritative catalog row |
| --- | --- |
| identity | `(one of five expression-delimited owners, raw Item / raw Separator / one consumed foreign close, direct delimited-sequence context)` |
| ordered Rowan grammar | For each owner, its direct sequence children retain native opening/punctuation/trivia and accepted children. A raw Item group is direct `Error+`. A raw Separator group is `ExpressionDelimitedSeparator(Error+)`; Parenthesized rejected semicolon has the same wrapper. One consumed foreign close is `ExpressionDelimitedForeignClose(Error+)`. Each wrapper has one nonempty adjacent Error-token group, no native trivia, Missing, Invalid, accepted child, punctuation or nested grammar. Direct Item Error and ProjectionRecordSpreadItem RHS Error remain unwrapped. |
| malformed admission and completion | Matching local close and inherited protected close win before foreign-close classification. A consumed unprotected foreign close creates one ForeignClose wrapper, preserves Item/Separator phase and scans the unchanged successor. A Parenthesized semicolon creates one Separator wrapper then resets to Item without a Missing. After existing initial leading has been emitted outside, a separator-phase lexical run creates one Separator wrapper, stops at the existing retry/boundary limit and continues as the unchanged Recovered phase. Item-phase lexical runs remain direct. |
| source and boundary ownership | A wrapper range is the combined UTF-8 range of its Error tokens. Leading attached to a consumed foreign close remains Error content inside its wrapper. Initial separator-run leading is emitted by the owner outside the wrapper; Error-internal leading remains inside; retry leading stays with the retried accepted child. Missing, matching/protected close, fence, accepted separator and spread RHS retain their existing owners and ranges. Source flattening is unchanged. |
| transition/handoff | `owner sequence entry → existing close/item/separator priority → consume direct Item Error, transparent Separator Error, or one transparent ForeignClose Error → preserve the existing loop phase/next Item/line/fence/ambient context → retry an admitted child, consume local punctuation, or hand off protected boundary unchanged`. No wrapper has independent recovery state or diagnostic. |
| diagnostic projection | A direct raw Item Error group projects its owner-specific Item expectation (`Expression`). An Error group under `ExpressionDelimitedSeparator` projects that owner's existing separator expectation (`DelimitedSequenceSeparator`). An Error group under `ExpressionDelimitedForeignClose` projects its immediate parent's existing matching close expectation. Each is one maximal adjacent group over its combined UTF-8 range, primary zero, in Rowan preorder. Neither Error spelling nor parser provenance is consulted. |
| proof and status | Governing authority: [expression-delimited raw-slot topology](2026-09-10-successor-expression-delimited-raw-slot-draft.md) and [expression delimited current-Item recovery](2026-09-08-successor-expression-delimited-current-item-recovery.md). Direct owner/emission source: `crates/yu-syntax/src/expression/delimited.rs:154–258`; append-only kinds: `crates/yu-syntax/src/syntax_kind.rs:281–282, 500–504, 745–767`; direct Rowan proof: `crates/yu-syntax/src/tests/delimited_recovery.rs:433–1258`. Status: `mapped` after M2 pre-write and closure audits. All non-raw delimited slots, global interpreter, recovery ledger and API migration remain open. |

### Root direct raw Error ordered-context evidence

This is partial candidate evidence, not a mapped or evidence-complete Draft
row. The current Root matrix distinguishes 16 direct raw `Error+` contexts by
their ordered sibling grammar without a new node: initial Starter; Separator
after an `OperatorChain`; 13 trailing-input contexts after their accepted
statement child; and required OperatorDefinition body after `OperatorHeader`.
Every witness has direct `Root` Error-token leaves, no `Invalid`, and a direct
next-statement sibling. Starter/trailing retain the ordered root-keyword set,
Separator retains singleton StatementSeparator, and operator body retains
singleton Expression. Error spelling is not classification input.

The matrix does not yet specify full Root trivia/repetition grammar, multi-run
or UTF-8/opaque extent, LF/EOF/fence handoff, retry/separator progression,
preorder/same-offset behavior, or independently audited CST projection.
Accordingly it neither selects topology nor supports ledger retirement.
Evidence: `crates/yu-syntax/src/tests/root.rs:289–535`; publishers:
`crates/yu-syntax/src/root_statement.rs:174,261,338,431–552`.

### Root direct raw Error bounded candidate

This candidate maps only maximal direct Root Error-token groups and the direct
operator-body Missing that disambiguates a terminal body run. It does not map
ordinary Root Missing, complete statement grammar, nested statement/header
recovery, outer Yumark ownership, or every Root terminal/trivia clause.

| Fact | Candidate catalog row |
| --- | --- |
| identity | `(Root, maximal direct Error-token group or direct operator-body Missing occurrence, root-sequence phase reconstructed from preceding direct siblings)` |
| ordered Rowan grammar | `Root := RootEntry* NativeRootTrivia*`; the bounded entries are `StarterError+`, `OperatorChain Native* SeparatorError+`, `AcceptedStatement Native* TrailingError+`, and `OperatorHeader HeaderChildren Equals Native* (InlineTriviaMissing OperatorChain \| BodyError+ (OperatorChain \| BodyMissing)? \| OperatorChain \| BodyMissing)`. `InlineTriviaMissing` is the direct `Missing` immediately after Equals before an adjacent admitted body OperatorChain; `BodyMissing` is terminal or follows the body Error group. A completed body `OperatorChain` is still in the OperatorDefinition entry, so its following direct Error group is trailing input; a standalone OperatorChain's following group is Separator. A header-local Error remains nested in OperatorHeader and is not this row. Every bounded raw group is adjacent direct `Root > Error+`; no Error node or Invalid is admitted. |
| malformed admission and completion | Initial/newly reset root position selects Starter. Native semicolon resets that position; Root-column newline permits a new entry, while same-line/deeper-line material remains the current Error group. After an accepted ordinary child, its declaration/expression role selects trailing or Separator. An actual emitted Equals inside OperatorHeader selects body even if prior header children recovered; absent Equals leaves the next Root Error trailing. Body Error may retry an admitted NUD or terminate with one direct body Missing; its later successor recovery stays separately nested. |
| nested ownership | Accepted Statement, OperatorHeader, OperatorChain and their descendants own their nested recovery. The candidate owns only direct Root Error leaves and direct body-phase Missing. Header-local recovery, UseAlias Missing and every other nested occurrence are excluded; adjacent direct errors do not merge across a native separator, Missing, nested node, or entry boundary. |
| source and boundary ownership | Initial malformed leading is native direct Root content before its Error group; internal malformed/opaque fragments are Error-token content. Retry and terminal native Root leading remain direct Root content. Semicolon/Root-column CRLF split groups and resume the next entry. EOF CRLF is direct terminal Root trivia after its final Error group. The existing fenced cell proves boundary Items stop before direct Error extent and return unchanged, but outer Yumark ownership is excluded. |
| transition/handoff | `Root entry start or completed child → reconstruct entry/previous role from ordered direct siblings → emit maximal direct Error group, direct InlineTrivia/Body Missing, accepted child or native separator/trivia → body only follows an actual emitted Equals; completed body retains OperatorDefinition for its next trailing group → semicolon/new root line resets Starter; protected close/transition/EOF remains the existing terminal owner → each direct group or Missing witnesses its selected slot, primary zero`. |
| diagnostic projection | One maximal direct Root Error group projects from its reconstructed phase: Starter and trailing use their existing ordered root-keyword alternatives, Separator uses StatementSeparator, and body uses Expression. The direct Missing immediately after Equals before an adjacent body OperatorChain projects InlineTrivia; terminal BodyMissing or BodyError+ then Missing projects Expression. A direct raw group after a completed body projects OperatorDefinition trailing, not Separator; direct Error text, temporary RootUnexpectedHead and recovery records are not inputs. Traverse direct Root children in source order; nested diagnostics follow their owning child and are not absorbed. |
| proof and status | Governing authority: [source-root statement topology](2026-09-09-root-statement-topology.md), [public-cutover priority](2026-09-08-successor-public-cutover-priority-amendment.md), and the CST-derived diagnostics amendment. Direct matrix/extent/retry evidence: `crates/yu-syntax/src/tests/root.rs:148–799`; body-Missing/inline-gap controls: `:800–883`; header/body/trailing proof: `:884–1094`; boundary-cell support: `crates/yu-syntax/src/root_statement.rs:853–951`; publishers: `root_statement.rs:174,261,316–332,338,431–552`. Status: catalog-audited evidence-complete Draft for this bounded Root raw-Error row only; no Root-wide completion, parser/API/SyntaxKind change or ledger-retirement claim. |

### OperatorHeader required-slot Draft

This bounded Draft maps only the ordered required slots directly inside one
`OperatorHeader`: Fixity, Name, the fixity-selected binding-power slot or
slots, and DefinitionIntroducer. It excludes the optional visibility/lazy
prefix except as an ordered prelude, the Root operator-definition body,
header discovery, `HeaderOperator` fact/conflict projection, fences, and every
other declaration/header row.

| Fact | Candidate catalog row |
| --- | --- |
| identity | `(OperatorHeader, required-slot phase reconstructed from its direct child sequence after optional Visibility/Lazy prelude; admitted Fixity selects the remaining finite role sequence)` |
| ordered Rowan grammar | `OperatorHeader := Visibility? Lazy? FixityPhase`; `Visibility := MyKw \| OurKw \| PubKw`. FixityPhase is one of `Missing`, accepted `PrefixKw \| InfixKw \| SuffixKw \| NullfixKw`, or direct `Error+` followed either by an accepted Fixity retry or by header termination at its boundary. No admitted Fixity closes the header immediately. After admitted Fixity, `Prefix := NamePhase RightPowerPhase DefinitionPhase`; `Suffix := NamePhase LeftPowerPhase DefinitionPhase`; `Infix := NamePhase LeftPowerPhase RightPowerPhase DefinitionPhase`; `Nullfix := NamePhase DefinitionPhase`. A later required phase operationally emits direct `Error+ → same-phase Accepted`, direct `Error+ → advance-with-pending-Item`, direct `Missing → advance-with-pending-Item`, or direct Accepted; Accepted is respectively `OperatorName`, `BindingPower`, or `Equals`. This phase machine, rather than a context-free `Error+ \| Missing \| Accepted` alternative, is the ordered-child grammar used for reconstruction. Native leading/trivia is a direct header child before the accepted child or Error group it belongs to. `Invalid` is never admitted. |
| malformed admission and completion | Fixity accepts only its four keyword children. Its direct Error group stops before either an accepted Fixity retry or boundary; only a Fixity initially presented at boundary publishes Missing and closes the header. Once Fixity is admitted, Name, each selected power, and `=` are tried in that order. A non-boundary unaccepted item becomes the current phase's direct Error group, which stops before a boundary, an accepted item, or that role's documented safe point. When it stops before an accepted same-role item, that Item is admitted in the same phase; only a safe-point/boundary stop passes the Item unchanged to the next required phase without an automatic same-role Missing. That next phase may admit it, emit its own Missing, or emit its own Error. A phase whose *initial* Item is boundary or safe point emits direct Missing and passes that Item onward. Thus an accepted later child after either Error or Missing is classified by replaying this fixed direct-child phase machine, never by Error spelling. Actual direct `Equals` completes DefinitionIntroducer; an ultimately unconsumed final Item is handed to Root/body selection. |
| nested ownership | `OperatorName` and `BindingPower` are accepted direct structural children, not nested recovery owners. The candidate owns only direct `OperatorHeader > Missing` and direct `OperatorHeader > Error+` required-slot occurrences. Root owns the post-header body/trailing sequence; there is no body recovery inside this row. |
| source and boundary ownership | Before a non-boundary Error run, current-Item leading is emitted as native direct header content; Error-internal lexical material is Error-token content. An Error run stopped by an accepted same-role item emits that retry's leading in the same header phase. Only a safe-point/boundary run-stop, or an initial Missing, preserves the Item between required phases; a later accepted phase then emits its leading in the header. Only an ultimately returned Item remains outside the header. A phase beginning at boundary or safe point emits its zero-width Missing without emitting that current Item. The `prefix 70 = body` control therefore has Name Missing followed by header-owned whitespace/BindingPower; `prefix (!)70 = body` has binding Error followed by a later header-owned Equals without Missing. The `suffix (!) 128 body + tail` control fixes the terminal partition: `128` is header Error, DefinitionIntroducer Missing is at its end, and the following space remains attached to pending `body`. |
| transition/handoff | `header prelude → Fixity required phase → (if admitted) finite fixity-selected required phases → emit native leading plus direct Error+, direct Missing, or accepted direct child → Error stopped by same-role acceptance retries in that phase; Error stopped by safe point/boundary, or an initial Missing, retains the Item for the next phase, which may admit it or emit its own recovery → actual Equals completes locally; only the ultimately unconsumed pending Item is handed to Root → each direct Error group or Missing witnesses the reconstructed phase`. |
| diagnostic projection | A direct Missing or one maximal adjacent direct Error-token group projects the reconstructed required role: Fixity expects ordered `prefix, infix, suffix, nullfix`; Name expects `OperatorName`; LeftBindingPower/RightBindingPower expects `BindingPower`; DefinitionIntroducer expects `=`. Each uses primary alternative zero and the Missing zero-width or combined Error UTF-8 range. Interpretation replays only direct child kinds, ordered phase, and selected Fixity; it neither reads Error text nor uses recovery records, parser fact state, or an environment conflict. Rowan source order places header-slot occurrences before Root's later body/trailing occurrences. |
| proof and status | Governing authority: [CST-derived diagnostics amendment](2026-09-09-successor-cst-derived-diagnostics-amendment-draft.md) and existing operator-header recovery contract. Direct owner/emission source: `crates/yu-syntax/src/declaration/operator_header.rs:73–114, 261–433`. Direct Rowan proof: `crates/yu-syntax/src/tests/declaration/operator_header.rs:367–536`, covering Fixity Error/retry, Name Missing, binding-power Error/Equals, DefinitionIntroducer safe-point Missing, direct parentage, no Invalid, and pending-leading partition. Status: catalog-audited evidence-complete Draft for this bounded required-slot row only; no full OperatorHeader grammar, header-fact/conflict mapping, parser/API/SyntaxKind change, or ledger-retirement claim. |

### DerivesClause `via` target Draft

This bounded Draft maps only the required raw identifier slot immediately after a
direct `ViaKw` in one `DerivesClause`. It excludes the preceding RoleReference
`TypeExpression`, comma/repetition progression, declaration/companion caller,
outer stops/fence, and every nested Type recovery.

| Fact | Candidate catalog row |
| --- | --- |
| identity | `(DerivesClause, direct required ViaTarget immediately after an accepted direct ViaKw, clause sequence after one accepted RoleReference)` |
| ordered Rowan grammar | The bounded sequence is `DerivesKw TypeExpression Native* ViaKw (Missing \| Error+ Native* Identifier? \| Native* Identifier)`. `Missing` is a direct zero-width DerivesClause child. An Error group is one maximal adjacent direct `Error+` token group; direct native retry leading then precedes a direct raw `Identifier` retry when one is admitted. No `Invalid`, ViaTarget wrapper, or nested Type node is created for this slot. |
| malformed admission and completion | The first Item after direct ViaKw produces direct Missing when the clause gap cannot continue or the Item is a ViaTarget boundary. A non-boundary non-Identifier produces one maximal raw direct Error group, stopping before an admitted raw Identifier or a protected boundary. The admitted Identifier is retried as a direct DerivesClause token without a Missing; a protected boundary returns unchanged without a second Missing. The Error group may instead be terminal at EOF/boundary. |
| nested ownership | The preceding RoleReference remains a `TypeExpression` child and owns any Type recovery. The candidate owns only direct DerivesClause Missing/Error leaves and raw retry Identifier for ViaTarget. A subsequent clause/caller/outer owner owns its own Item, punctuation, boundary and recovery. |
| source and boundary ownership | At immediate absence, ViaTarget Missing is anchored before the pending Item; that Item and all its leading remain outside DerivesClause. During a raw Error run, initial/internal lexical material is Error-token content. If raw Identifier retry is admitted, its leading is direct native clause content before the Identifier. The direct witness `derives Eq via @ target` has Error-token ranges `14..15,15..16`, native whitespace `16..17`, then retry Identifier `17..23`; both `derives Eq via` and `derives Eq via  ` have Missing `14..14`, while the latter leaves its two spaces on pending EOF outside the tree. |
| transition/handoff | `accepted RoleReference → direct ViaKw → acquire ViaTarget Item → boundary/gap wins to direct Missing and unchanged handoff; otherwise direct Identifier completes locally, or maximal Error+ retries direct Identifier / hands off protected boundary unchanged → ViaTarget direct Missing or Error+ witnesses this slot`. |
| diagnostic projection | Direct Missing projects ViaTarget expected `Identifier`, primary zero, at its zero-width UTF-8 range. One maximal adjacent direct Error-token group projects the same expectation at its combined UTF-8 range; native retry leading is excluded. Traverse DerivesClause children in source order after ViaKw. Error spelling, parser recovery records, and the TypeExpression's nested diagnostics are not inputs. |
| proof and status | Governing authority: [CST-derived diagnostics amendment](2026-09-09-successor-cst-derived-diagnostics-amendment-draft.md). Direct publisher/caller: `crates/yu-syntax/src/declaration/derives.rs:40–101,144–232,320–356`. Direct Rowan proof: `crates/yu-syntax/src/tests/declaration/derives.rs:609–770`; prior protected-boundary/retry support: `:772–918`. Status: catalog-audited evidence-complete Draft for this bounded ViaTarget row only; no DerivesClause-wide completion, parser/API/SyntaxKind change, or ledger-retirement claim. |

### StringInterpolationBody root-style statement-sequence map

This bounded Draft row maps only the root-style sequence directly beneath an
accepted interpolation open brace. It does not generalize
`BlockStatementSeparator` to another block owner, map a nested `Statement`,
or map the interpolation-owned borrowed close and its following literal
terminator slot.

| Fact | Draft catalog row |
| --- | --- |
| identity | `(StringInterpolationBody, repeated root-style Statement sequence, direct child of an accepted StringInterpolation open brace)` |
| ordered Rowan grammar | `StringInterpolationBody := (Statement \| Missing \| Error+ \| BlockStatementSeparator)*`. `Statement` is a direct child. An accepted explicit or newline separator is a direct `BlockStatementSeparator`; an explicit separator contains its leading, comma/semicolon, and eligible successor leading, while a following comma/semicolon stops successor-leading absorption but does not terminate the sequence; a newline separator contains its successor remaining leading only. The three mapped malformed alternatives are: `Statement(Missing)` for required starter after leading/repeated explicit separator; direct `StringInterpolationBody(Missing)` for a required separator between two admitted Statements; and one maximal adjacent direct `Error+` group for a malformed starter. No `Invalid` or close node is admitted here. |
| malformed admission and completion | A leading comma/semicolon emits `Statement(Missing)` before that separator; a repeated comma/semicolon emits `Statement(Missing)` before the next separator and continues the sequence. After an admitted Statement, an ordinary newline produces a newline separator; a following admitted Statement without a separator produces the direct body Missing before that Statement. A non-admitted, non-boundary starter emits one maximal direct Error group, which stops before an admitted Statement, comma, semicolon, ordinary newline, EOF, borrowed `}`, or fence. It may retry an admitted Statement immediately, without a separator Missing. An explicit separator followed by EOF, fence, or borrowed `}` is terminal and adds no Statement Missing. |
| nested ownership | Every admitted `Statement` owns its full grammar and its nested Missing/Error/Invalid topology. The direct Error group owns only raw Error leaves; it retains no nested grammar. The enclosing `StringInterpolation` owns borrowed-`}` leading, `StringInterpolationCloseBrace` or its Missing, and outer continuation. |
| transition/handoff | `root-style sequence entry → boundary/borrowed-close wins before statement or separator classification; otherwise explicit separator, admitted Statement, or malformed starter is selected by sequence position → emit Statement(Missing), direct body Missing, maximal direct Error leaves, accepted Statement, or BlockStatementSeparator → accepted Statement completes locally to AfterStatement; Error retries the admitted Statement without a separator Missing; newline/explicit separator returns to AfterSeparator, where a following comma/semicolon emits the next Statement(Missing) and continues; terminal EOF/fence/borrowed close is handed off unchanged with pending leading → Statement(Missing) witnesses Statement/Starter, direct body Missing witnesses Statement/Separator, and direct Error+ witnesses Statement/Starter.` Newline immediately before borrowed `}` remains interpolation-owned, not a separator node. |
| diagnostic projection | `Statement > Missing` projects one `Statement(Starter)` occurrence with expected `Statement`, primary alternative zero, at that direct zero-width Missing range. A direct body Missing projects one `Statement(Separator)` occurrence with expected `StatementSeparator`, primary alternative zero, at its direct zero-width range. One maximal adjacent direct body Error-token group projects one `Statement(Starter)` occurrence with expected `Statement`, primary alternative zero, at the combined UTF-8 Error range. Initial/internal Error leading remains in that group; retry and protected-boundary leading remain outside it. Rowan preorder places each direct body occurrence before recovery projected by a retried/nested Statement and before the enclosing interpolation-close/literal-terminator occurrences. |
| proof and status | Governing slice: [error-admission clarification](2026-09-09-successor-error-admission-schema-clarification.md#proposed-schema-slice-stringinterpolationbody-statement-sequence), Draft. Direct CST evidence: `crates/yu-syntax/src/virtual_statement_block.rs:67` (root-style entry and boundary/borrowed-close priority), `:225` (maximal Error-run/retry), `:298` (retry boundary), `:309` (explicit separator and successor-leading phase), `:347` (newline separator), `:354` (nested starter Missing), and `:368` (Starter/Separator projection facts); `crates/yu-syntax/src/literal/mod.rs:460` (the direct `StringInterpolationBody` wrapper and outer close ownership). Focused proof: `crates/yu-syntax/src/tests/virtual_statement_block.rs:617–873`. Status: `mapped` for these three evidence-complete Draft recovery roles only; promotion, all nested Statement rows, interpolation close, literal terminator, the global interpreter, recovery-ledger retirement, and API migration remain open. |

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
