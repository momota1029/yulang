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
except for its AssignmentTail direct-inline slice, which is Authoritative. The
catalog links that slice rather than copying or extending it. Existing accepted
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
| expression tails and required operands | assignment, annotation, colon/with, fixed access, required operands, delimited expression phases | partial: AssignmentTail direct-inline is externally Authoritative; dedicated Field/Path evidence-complete Draft slices are referenced below |
| expression forms and statement/layout containers | case/if/for, source-root, statement and virtual-statement sequences | unmapped except for delegated evidence links |
| pattern and structured delimiters | Pattern entries, delimited sequences, RecordPattern Item/Separator structured recovery | unmapped; preserve the designated Invalid row below |
| type entries, tails and delimiters | type expression, paths, rows, variants, forall, delimited closes and TypeCall close | partial: listed evidence-complete Draft slices and TypeCall mapping below |
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

### External authoritative slice

The direct-inline `AssignmentTail` RHS slice is Authoritative only in
`2026-09-09-successor-error-admission-schema-clarification.md`,
**Representative schema slice: AssignmentTail inline RHS**. Its ordered
children, leading, Missing/raw Error admission, retry, projection and nested
ownership are not copied here. The indented `Assignment(IndentedStatement)`
alternative remains an excluded open dependency.

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
| TypePathTail segment | error-admission clarification, **Proposed schema slice: TypePathTail segment** | user promotion open |
| LeadingEffectTypeHead | error-admission clarification, **Proposed schema slice: LeadingEffectTypeHead** | user promotion open |
| BracketRow required-arrow continuation | error-admission clarification, **Proposed schema slice: BracketRow-selected required-arrow continuation** | user promotion open |
| actual-arrow TypeArrowTail RHS | error-admission clarification, **Proposed schema slice: TypeArrowTail actual-arrow RHS** | user promotion open |

The AssignmentTail direct-inline slice is intentionally absent from this table:
it is externally Authoritative, rather than an evidence-complete Draft.

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
