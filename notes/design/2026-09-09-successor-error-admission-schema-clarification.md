# Error-admission schema clarification

Status: Draft

Date: 2026-09-09

Scope: declarative CST admission of malformed source in the successor parser.
This clarification makes the per-slot schema requirement of the CST-derived
diagnostics amendment explicit. It does not add accepted source syntax, change
recovery continuation, broaden `Invalid` ownership, alter the topology-only
migration, or authorize a parser/API implementation.

User direction: malformed input is not admitted indiscriminately. A production
specifies the locations and sequences in which its lossless CST may contain
recovery elements, allowing an error-containing CST to be structurally
accepted with finer control than an untyped recovery wrapper.

## Decision proposal

An error-containing CST is structurally admitted only where the owning
production's documented grammar slot allows its exact sequence. Structural
admission means that parsing can produce one lossless CST with explicit
malformed elements. It does not make the original source recovery-free
accepted syntax, and it does not establish downstream HIR, type-checking, or
execution behavior for malformed input.

The schema is ordered and context-sensitive. A slot identity consists of its
containing production, ordered phase/child position, and any documented
ancestor context needed to distinguish it. A parent kind alone is insufficient.
The schema must identify a slot from the CST structure and its documented
context without parser recovery records, opaque-Error relexing, or hidden
provenance.

For every recovery-bearing slot, the production schema records:

| Required fact | Meaning |
| --- | --- |
| ordered child grammar | valid children, optionality, repetition, punctuation, and phase order |
| admitted malformed sequences | whether the slot permits `Missing`, a raw Error group, a retry after that group, a terminal group, or a structured child |
| child ownership | nested grammar that remains owned by a child production and may therefore contain its own admitted recovery |
| source ownership | punctuation, ordinary trivia, malformed-run trivia, and protected-boundary leading |
| diagnostic projection | expected alternatives/primary expectation where applicable, recovery category, and occurrence order |
| slot context | all ancestor/phase facts needed for unambiguous interpretation |

Omission grants no malformed admission. A blanket union such as `Valid |
Missing | Error | Invalid` is not a schema: it cannot express ordering, retry,
boundary preservation, or diagnostic grouping.

## Recovery elements and containment

`Missing` is a zero-width absence admitted at a documented required slot. An
optional absence normally emits no `Missing`. A schema explicitly decides
combined expectations, consecutive same-offset `Missing` occurrences, and any
case where one malformed episode suppresses a same-cause absence.

A raw `Error` group contains nonempty physical source fragments in one
documented slot. Its adjacent token leaves form one group only while they have
the same immediate parent and slot. A schema states whether a valid retry may
follow it, whether it is terminal, and which leading/trailing trivia and
boundaries remain outside the group.

`Invalid` retains structured wrong-slot recovery that contains nested grammar,
`Missing`, or nested raw `Error` groups. This clarification retains the existing
restriction: only polymorphic-variant TagName recovery and record-pattern
wrong-kind Item/Separator recovery may introduce `Invalid`. Their nested
children follow their own documented schemas. A valid enclosing node does not
gain an outer `Invalid` merely because it contains an admitted malformed
descendant.

No production gains a new structured owner, an extra `Invalid`, a changed
continuation, or a changed boundary rule by analogy. Such a case requires a
separate Authoritative amendment.

## Diagnostic interpretation

The existing CST-derived diagnostic rules remain unchanged:

- a `Missing` occurrence emits the documented slot's missing diagnostic at its
  zero-width UTF-8 byte range;
- a maximal adjacent raw `Error` group in one immediate-parent slot emits one
  malformed-input diagnostic over the combined group range;
- an `Invalid` occurrence emits its structured diagnostic before its children;
- environment conflicts are derived at a complete `OperatorHeader` occurrence
  and never mutate the CST.

Slot boundaries must not split physically indistinguishable adjacent Error
fragments merely to obtain a desired diagnostic count. If CST structure and
schema context cannot determine the slot uniquely, the owning CST schema is
incomplete and blocks retirement of parser diagnostic state.

## Compatibility and boundaries

This clarification does not change the approved topology-only gate. Until the
complete per-slot schema and its later migration are complete, existing parser
recovery records, structured reservations, frozen-header reconciliation,
diagnostic IDs, public diagnostic construction, and their temporary extents
remain compatibility machinery exactly as already specified.

It does not change accepted syntax, source losslessness, current-Item/fence
handoff, outer-boundary preservation, or recovery continuation. It introduces
no schema DSL, code generation, runtime validator, new public API, parser
ledger, or second tree.

## Public-reference form

Each reconstructed construct page presents its accepted surface spelling and
source-order Rowan schema. Where the construct has admitted malformed forms,
its EN/JA pair records the relevant slot sequence, punctuation/trivia and
boundary ownership, and diagnostic placement. It does not expose parser
control flow, commits, fixtures, or implementation provenance.

The internal design schema may use a compact slot table beside XML-like Rowan
examples. Public pages use the existing XML-like notation and explanatory
grammar; they do not reproduce a compiler-internal coverage ledger.

## Representative schema slice: AssignmentTail inline RHS

### Authority and boundary

Status: Authoritative for this direct-inline slice only

Approved-by: user

Approved-at: 2026-09-10

The user approved this slice after its focused Rowan evidence and independent
specification and compiler/recovery audits. The approval covers the concrete
child topology, leading ownership, recovery admission and diagnostic
projection stated in this section. It does not promote this document's other
proposal material, the delegated `IndentedStatementBlock` alternative, any
other slot, the inventory, CST interpreter, parser-ledger retirement or public
diagnostic API.

The direct inline `Assignment(Rhs)` position of `AssignmentTail` is the first
specified slice for this clarification.
Its governing authority is
`2026-09-09-successor-expression-structural-tails-draft.md`, **Owner topology
and admission** and **Assignment**; its M2 construction handoff confirms the
flat tail topology, one-character acquisition, one RHS, terminal exit, and
focused recovery verification. This is evidence for the schema method only. It
does not make other expression slots complete or infer their malformed forms.

The ordered direct-inline CST alternatives are:

```text
OperatorChain := <left-expression children and pre-`=` trivia> AssignmentTail
AssignmentTail := Equals (Missing | Error+ | Error+ OperatorChain | OperatorChain
                          | <delegated IndentedStatementBlock>)
Equals := "="
```

This grammar elides trivia only to make the child alternatives legible. Initial
leading before both an accepted and an initially rejected direct RHS is native
trivia directly under `AssignmentTail`, before its `OperatorChain` or raw
Error children. Leading at an admitted retry is instead native trivia in the
new `OperatorChain` child. The boundary/missing rule owns only the leading it
explicitly selects.

`AssignmentTail` never owns or wraps the left expression. In the accepted
direct alternative, and after a raw-group retry, the RHS is a concrete
`OperatorChain` child; `InlineRhs` is not a Rowan node. A raw group is direct
`Error` token children of `AssignmentTail`. Its initial rejected-Item leading
is direct `AssignmentTail` trivia outside the raw group. The tail is admitted
only at the outer, enabled non-ML continuation after an admitted dynamic LED
has declined; lower-threshold and ML candidates have no source, CST, or
recovery effect. This representative proof covers only that direct-inline
alternative.
The deeper-line alternative delegates to the existing
`Assignment(IndentedStatement)` block contract with a concrete
`IndentedStatementBlock` child and a `Statement` expectation; its block-entry
and child-slot schema remain an explicitly open dependency rather than an
implied recovery-free child.

For the direct inline slot, both `Missing` and one maximal raw Error group
project `Assignment(Rhs)` with expected `Expression` and primary index zero.
The raw group is one malformed-input occurrence for this slot, not a parser
unexpected payload or a second Missing. In both raw alternatives below,
initial rejected-Item leading remains outside the raw group, interior leading
belongs to it, and leading before an admitted retry or a protected boundary
remains outside it according to the direct-child placement above.

| `Rhs` sequence | Structural admission and ownership | Diagnostic / continuation fact |
| --- | --- | --- |
| inline `OperatorChain` | one required direct inline child | no recovery element |
| required RHS absent at an admitted stop, boundary, separator, close, non-NUD bracket opener, non-continuing layout, or EOF | one zero-width `Missing` in `Assignment(Rhs)` | expected syntax is `Expression`; protected Item/leading stays pending; ordinary EOF may first emit owner-leading and anchors at physical EOF |
| non-boundary non-NUD run followed by an admitted inline expression | one nonempty direct raw Error group, then one `OperatorChain` child | expected syntax is `Expression`, primary zero; one malformed episode retries the same Rhs position; nested recovery retains its own grammar-owner slots within the RHS child |
| non-boundary non-NUD run reaching a protected boundary | one nonempty terminal raw Error group | terminal raw group returns the boundary unchanged and adds no same-cause `Missing` |

The current temporary parser-record compatibility path distinguishes an
abstract-boundary record anchored at its inspected coordinate, another
protected-boundary record anchored at the remaining Item start with that
complete Item and its leading unread, and the ordinary-EOF rule in the table.
Those record anchors do not relocate the structural `Missing` occurrence. In
the later CST-derived diagnostic migration, its missing diagnostic uses that
node's zero-width CST range as already specified by the governing amendment;
the current record-coordinate compatibility is then retired rather than
preserved as hidden schema provenance.

The raw group uses the implemented Error-token/Invalid-node topology; it does
not authorize an `Invalid` child. The table's ordered alternatives, concrete
direct children, leading placement, direct-tail ownership, and boundary facts
distinguish the Rhs slot without parser records. It also shows why a generic
`Error` child union would be inadequate: the two raw cases have different
following children and protected-boundary behavior.

Draft evidence for this direct-inline slice is complete as of 2026-09-10:
focused Rowan assertions cover accepted RHS, protected Missing, terminal Error,
Error-to-retry with retry-leading ancestry, a contiguous multi-fragment Error
group, and nested FieldTail Missing ownership. Specification and
compiler/recovery delta audits found no remaining slice finding. This records
evidence for the Draft only; it neither promotes this slice nor closes the
indented dependency, complete inventory, interpreter or parser-ledger
migration.

## Proposed schema slice: fixed FieldTail and PathTail names

The next proposed slice covers the dedicated required-name positions of
`FieldTail` and `PathTail`. Its governing recovery authority is
`2026-09-08-successor-expression-fixed-tail-current-item-recovery.md`.
Unlike an Assignment RHS, neither fixed tail retries a name inside the same
tail after raw recovery: it closes and returns the retained Item to ordinary
outer-tail handling.

The trivia-elided direct child alternatives are:

```text
FieldTail := Dot (Missing | Error+ | Identifier)
PathTail  := ColonColon (Missing | Error+ | Identifier | SigilIdentifier)
```

`Dot` is `.` and `ColonColon` is `::`; `PathSeparator` remains only the
scanner concept, not a Rowan token name. Field has grammar-empty internal
leading: leading before a candidate name makes that name absent and remains
with the returned Item. Path owns its existing permitted `G*` before a name,
including a physical newline when no line stop applies. Initial malformed Path
leading is native trivia inside `PathTail` but outside its raw Error group;
retry and protected-boundary leading remain with the returned Item. Accepted
Field names are adjacent ordinary `Identifier` children. Accepted Path names
are `Identifier` or `SigilIdentifier` children after permitted path leading.

The slot mappings are `Expression(FieldName)` for Field and
`Expression(PathSegment)` for Path. For Field, apply the shared boundary list
only after the higher-priority dot/projection judges have admitted a FieldTail.
At each documented stop, boundary, separator, close, accepted dynamic LED,
`(`, `[`, fixed/dynamic tail continuation or colon boundary, the matching name
position has one zero-width `Missing`; its diagnostic projects at that CST
range with expected `Identifier` and primary index zero. The whole protected
Item remains outside the tail. Ordinary Path EOF may first emit its owned
leading before the `Missing`. `.{` and `.(` dispatch to record and tuple
projection respectively before a FieldTail exists, while `::{` is a non-name
Path item and enters Path raw recovery. A lone `:` is always the terminal
outer-tail continuation, even when `STOP_COLON` is not active; deferred-dot
and longer projection judges retain their priority.

A non-boundary non-name item produces one maximal adjacent direct Error-token
group. The run stops before a trivia-bearing retry Item, every protected
boundary above, an accepted Field/Path name, or a fixed/dynamic tail
continuation. Its diagnostic projects once for the containing mapped name slot
over the combined group range, expected `Identifier`, primary index zero. It
neither creates a second Missing nor an `Invalid` node.

After such a raw group, `FieldTail` or `PathTail` finishes without attaching a
replacement name. The outer tail receives the following Item and its retry
leading unchanged, with threshold, ML mode, stops, baseline, line/fence and
ambient context intact; it may form a later fixed/dynamic or ML continuation
under its own slot. Neither dedicated name slot admits nested grammar recovery.

This is a Draft proposal. Exact direct-child evidence must cover accepted
Field/Path names, Missing, raw Error, leading ownership, `.{` projection and
`::{` raw recovery, protected Item continuation, subsequent outer-tail
siblings, UTF-8/CRLF/fence ranges and threshold/ML handoff before review or
promotion.

Draft evidence is complete as of 2026-09-10. Focused Rowan tests cover every
listed case, including root-relative UTF-8 and fence ranges and the true
successor coordinate for unread CRLF leading. Specification and
compiler/recovery reviews closed after bounded test-only repairs. This does not
promote the slice or close any other inventory row.

## Proposed schema slice: StringLiteral terminator

This proposed slice covers only the outer ordinary/heredoc terminator of a
non-Rule `StringLiteral`, under the existing
`Literal(StringTerminator)` recovery authority. Escape and interpolation
recovery remain children of their own literal productions.

```text
StringLiteral := StringStart StringPiece* (StringEnd | Missing)
```

This production elides opener-leading native trivia, which is direct
`StringLiteral` content before `StringStart`. `StringPiece` includes accepted
text, interpolation and escape children, and
the physical Yumark quote-prefix leaves that ordinary scanning emits. Opener
leading remains before `StringStart`. The terminator is the final direct child:
an accepted `StringEnd` token or one zero-width `Missing` node. There is no
direct outer raw Error or `Invalid` alternative for this slot.

The opener's spelling determines normal versus heredoc close width. In ordinary
text scanning, a mismatched heredoc quote run remains `StringText`; Unicode
malformed recovery and interpolation-format text retain their own Error and
FormatText ownership respectively. Thus a CST walk identifies this slot from
the final direct child and opener, never by source quote search.
At EOF or a fence boundary, the outer Missing projects one
`Literal(StringTerminator)` expectation at its zero-width CST range and leaves
the protected pending Item unchanged. Accepted quote-prefix leaves before an
actual close remain native direct children. Nested escape/interpolation
recovery is visited before the final outer terminator occurrence, and an
equal-offset nested Missing is distinguished by its child path.

Exact terminator spelling can be derived from `StringStart` for presentation;
the existing StringTerminator expectation vocabulary remains unchanged. This
is a Draft proposal. Direct CST proof must cover normal and heredoc close,
mismatched quote runs, UTF-8/CRLF EOF, fence boundaries, accepted prefixes,
nested equal-offset Missing, malformed Unicode then EOF, format quotes and
actual Expression/Pattern/Rule-string callers before review or promotion.

Draft evidence is complete as of 2026-09-10. It includes the isolated
interpolation-EOF case whose outer Missing is at the literal CST end while its
trailing leading remains in the pending EOF Item, plus public Root witnesses
that emit that leading as native source-order tokens and preserve full-source
losslessness. This does not promote the slice or specify child recovery slots.

## Proposed schema slice: dedicated Rule literal slots

This proposed slice covers Rule-owned recovery only. It excludes bracket
ExpressionList, RuleLiteral terminator/interpolation/lazy-capture, String and
Virtual children, which retain their own schemas. A `RuleItem` requires its
first atom as a discriminator; its parent kind alone does not select a close
slot.

```text
RuleBody                         := LBrace RuleAlternation (RBrace | Missing)
RuleItem[LParen]                := LParen RuleAlternation Missing
                                  | LParen RuleAlternation RParen RuleNonCapturePostfix* RuleCapture?
RuleCapture                     := Equals (Error* RuleItem | Error* Missing)  // terminal
RuleField                       := Dot (Identifier | Error+ | Missing)
RulePath                        := ColonColon (Identifier | Error+ | Missing)
RuleSequence                    := (RuleItem | Error+)*
```

`RuleNonCapturePostfix` denotes only the existing non-capture postfix forms;
it is not a new CST node. A Missing parenthesis close terminates its RuleItem.
The Body and parenthesized-Item close slots are distinguished by direct opener
and expected punctuation. Capture is optional after non-capture postfixes and
terminal when present. Capture Error belongs directly to `RuleCapture` but
its later Missing belongs to the required RHS position; both project a Rule
item expectation without reconstructing temporary role records. Field/Path
consume one malformed lexical Item and close their name owner: a following
valid name or postfix is handled by the outer RuleItem, never retried inside
the failed name slot. Adjacent raw Error leaves in Capture or RuleSequence form
one occurrence only while their immediate parent and slot agree.

These productions elide native trivia. Leading before an admitted opener,
atom, name, capture or matching close stays as direct content of the parent
that emits it. A rejected Rule Item, including its leading, is emitted in that
owner's Error group; retry leading belongs to the newly admitted child and
protected boundary leading remains with the returned Item. Body/Paren protected
and retry leading therefore stays pending. Body/Paren newline stops apply before name/RHS admission; RuleLiteral
interpolation deliberately owns different stops and remains excluded. At EOF
or a fence, a Missing uses its direct CST insertion range while pending leading
is returned to its terminal owner. Nested same-offset Missing occurrences are
identified by their distinct parent paths, not by legacy record coordinates.
No form above admits `Invalid`; delegated bracket atoms retain ExpressionList
close ownership. RuleCall, RuleIndex and bracket RuleItem interiors likewise
delegate all Item/Separator/close recovery to ExpressionList. RuleSequence
receives its explicit caller stops: Body and parenthesized atoms distinguish
their matching close, separators and newline stop before name/RHS admission;
the inherited outer RuleLiteral quote context remains with that outer owner.

This is a Draft proposal. Exact direct CST evidence must cover closes,
capture Error-to-Missing and Error-to-valid, nested same-offset Missing,
field/path outer siblings, consecutive Error grouping, newline/quoted-fence
stops, UTF-8/CRLF and public Root leading conservation before review or
promotion.

Draft evidence is complete as of 2026-09-10. Focused Rowan tests cover each
listed form, including terminal Capture structure and retry ownership, with
specification and compiler/recovery delta reviews closed. This does not promote
the slice or cover its delegated child schemas.

## Proposed schema slice: StringInterpolationBody statement sequence

This proposed slice covers only the root-style statement sequence directly in
`StringInterpolationBody`. It does not define a global `BlockStatementSeparator`
schema: other block constructors own different successor-leading rules.

```text
StringInterpolationBody := (Statement | SeparatorMissing | Error+ | BlockStatementSeparator)*
BlockStatementSeparator := ExplicitSeparator | NewlineSeparator
```

An accepted explicit separator is a `BlockStatementSeparator` node containing
its leading, comma/semicolon and successor leading unless that successor is
EOF, a fence, comma, semicolon or borrowed `}`; malformed successors qualify
for absorption. An accepted newline separator occurs only after a Statement or
recovery phase and after those terminal checks. It contains successor remaining
leading only, so newline before borrowed `}` remains interpolation-owned. A
required Statement after leading/repeated comma or semicolon is a `Statement`
wrapper containing `Missing` before that separator. A `SeparatorMissing` is
instead a direct `Missing` child of `StringInterpolationBody`. Likewise,
two admitted Statements without a separator receive a direct body Missing for
the separator position before retrying the second Statement.

A malformed statement run is one maximal adjacent direct Error-token group in
the body, expected Statement. Its initial and internal remaining leading belong
to Error; retry/boundary leading remains outside it. An Error run stops at an
admitted Statement, comma, semicolon, ordinary newline, EOF, borrowed `}` or
fence. It may retry the admitted Statement without an invented separator
Missing. Nested statements retain their own slots. `StringInterpolationBody`
has no close node: interpolation owns the borrowed `}`, then its own close and
outer terminator recovery follow in preorder.

This is a Draft proposal. Direct CST evidence must cover explicit/newline and
leading/repeated/trailing separators, direct Missing versus nested child
Missing, Error retry/newline behavior, UTF-8/fence and public Root source
conservation before review or promotion.

## Proposed schema slice: TypePathTail segment

This proposed slice covers the required segment immediately after a Type
`ColonColon` token. It is distinct from expression PathTail because Type
contextual admission, horizontal application and continuation-qualified
newlines select different child ownership.

```text
TypePathTail := ColonColon (Identifier | SigilIdentifier | Missing
                            | Error+ Identifier | Error+ SigilIdentifier | Error+)
```

This grammar elides native trivia. Initial leading remains in `TypePathTail`
before an accepted name, Missing or Error group. Initial ordinary EOF/path
boundaries and shallow layout emit their owned leading before Missing; abstract,
caller and outer boundaries keep their Item and leading pending. After Error,
every boundary keeps its pending leading. A segment Missing or maximal direct
Error group projects one `Type(PathSegment)` occurrence with expected
`TypePathSegment` and primary zero. Integers are malformed; `Invalid` is not
admitted. Adjacent Error leaves are one group only under the same immediate
slot.

An adjacent identifier/sigil or a continuation-qualified deeper newline retries
inside the same tail after Error. Horizontal retry leading instead remains with
the outer TypeApply: `A::@B` gains a segment child `B`, while `A::@ B` closes
the incomplete path and leaves space/`B` to the outer owner. An immediately
adjacent block-comment prefix may be Error content before either outcome.
Same-line contextual initial names win before segment admission; a
newline-bearing contextual Item remains protected even at deeper indentation.
After Error its contextual boundary priority resumes. Repeated `::` finishes
one tail and starts a sibling tail. Active closes/stops, shallow newline, EOF
and fence follow the phase-specific leading rules above.

This is a Draft proposal. Direct CST evidence must cover accepted/sigil/integer
forms, comment-prefix variants, contextual and close priority, retry versus
outer TypeApply, repeated tails, UTF-8/CRLF/fence and public Root conservation
before review or promotion.

## Construction and proof gates

1. Independently review the representative direct inline `Assignment(Rhs)`
   slice above for exact direct-child topology, leading placement, expected
   projection, malformed sequence, continuation, range and boundary
   preservation. Add exact CST evidence for accepted RHS, Missing, terminal
   raw Error, Error-to-retry with retry leading, and nested recovery. No parser
   change occurs in this gate. A clean review and that evidence close only this
   representative direct-inline proof, not the indented-block dependency or
   the whole-slot inventory.
2. Inventory every recovery-bearing slot and publish its ordered schema before
   the existing parser-ledger/public-diagnostic migration. An unmapped slot
   remains explicitly open; it is not inferred from a parent kind or current
   output.
3. Reconstruct public construct pages one EN/JA pair at a time from an
   Authoritative schema slice and an implemented-gate handoff. Compare only the
   specified CST topology; return an unresolved slot or API choice to the
   primary.
4. Preserve the existing topology-only Error-token/Invalid-node gate and its
   compatibility state. Complete the already-authorized full CST-derived
   diagnostic migration only after the slot inventory closes.

Verification for a schema slice covers accepted input; Missing and combined
same-offset cases; malformed-then-valid retry; terminal malformed input;
adjacent raw groups across slot boundaries; nested `Invalid`, `Missing`, and
`Error`; valid syntax inside `Invalid`; UTF-8, CRLF, and Yumark fragments; and
protected boundary preservation. Stop the affected gate if a required
diagnostic needs hidden parser facts, a slot cannot be uniquely identified, or
a proposed form changes existing continuation or source ownership.

## Relationship to existing authority

This document clarifies the CST-derived diagnostics amendment's requirement
that every recovery-bearing slot have ordered child grammar and recoverable
context. It retains the Rowan CST-only amendment's lossless direct-tree model
and the topology-ordering addendum's two-owner `Invalid` restriction. It
supersedes nothing on approval.
