# Draft: canonical successor syntax products

Status: Draft; not implementation authority

Date: 2026-09-09

Scope: a non-final candidate AST syntax-product contract for the **currently
admitted** successor statement surface, to be used by the canonical
materialization seam and selected Yumark cells. It selects syntax structure and
mandatory-slot availability only. It does not change accepted grammar,
recovery policy, CST topology, HIR/runtime meaning, public API, or the deferred
Yulang2 acceptance gates listed below.

This Draft is companion authority preparation for
`2026-09-09-successor-canonical-materialization-seam-draft.md` and
`2026-09-09-successor-literal-syntax-product-draft.md`. Historical chasa
architecture products are candidate evidence; this Draft, if later approved,
is the only source that can adopt their fields for the successor.

## Current admission boundary

The product sum follows actual current successor admission, not every
historical reserved production:

```text
Statement ::= Expression | Binding | Use | OperatorDefinition
            | Mod | Struct | Type | Impl | Cast | Role | Act
            | Enum | Error | For
```

`OperatorDefinition` is required even though root dispatch owns it beside the
ordinary statement classifier. A selected cell uses the same root progression;
it produces syntax for local definitions but never changes the immutable host
operator table.

`DocCommentDeclaration` is authoritatively specified as a later outer Yumark
product but is not currently admitted by production canonical statement
dispatch. It is therefore excluded from this current product sum and remains a
required later document/frame promotion gate; final parser completion may not
silently drop it.

The following forms remain outside the adopted product closure. Assignment and
type annotation are current syntax with candidate fields selected in this
Draft, but their M3 review, user approval and implementation remain pending.
Type-attached `impl` remains outside both successor promotion and this product
closure:

| deferred form | current evidence |
| --- | --- |
| generic expression assignment | Authoritative structural-tail construction is complete; this Draft's candidate field selection awaits M3 review and user approval |
| expression `as Type` annotation | Authoritative structural-tail construction is complete; this Draft's candidate field selection awaits M3 review and user approval |
| Type-attached `impl` | approved TAI authority; Type owner still returns qualifying `impl` Item pending, so successor implementation/promotion remains deferred |

Binding's actual definition `=`, Type's equality form, and Pattern's `: Type`
annotation are included; none is an expression assignment/annotation variant.
The final Yulang2-compatibility closure must review and approve the two current
tail-product candidates and separately construct the deferred Type-attached-Impl
gate rather than treating either omission as product completion.

## Common product and recovery rules

`R<T> ::= Complete(T) | Incomplete` is fact availability, not diagnostic
cardinality. A committed parent with a recovered child remains complete. A
successful retry is complete; a mandatory absence or terminal malformed run
without a retry is incomplete. An optional, unentered form is `None`.

No AST traversal allocates, orders, or infers diagnostics. The shared ledger
retains IDs and record order. A single CaseLike Arrow/Body record makes both
selected slots incomplete without a second record. Separators are ledger-only
unless the selected syntax product retains an actual accepted separator.
`NormalizedExit::Complete(Err(Item))` is successful product completion with an
unread successor; `Deferred` has no product effect.

All products use the candidate source-backed coordinate leaves from the seam
Draft. Every named product carries its physical range; its semantic range may
exclude trailing malformed recovery only where the owning product explicitly
says so. Diagnostic extent is never substituted for a product range.

## Expression, Pattern, block, and control candidates

```text
OperatorChain { items: Vec<ChainItem>, range }
ChainItem ::= PrefixUse(OperatorUse) | NullfixUse(OperatorUse)
            | InfixUse(OperatorUse) | SuffixUse(OperatorUse)
            | Primary(Primary) | FixedPostfix(FixedPostfix)
            | MlArgument { argument: Box<OperatorChain>, range }
            | TerminalOuter(ColonApplication | WithBody | AssignmentTail
                            | TypeAnnotationTail)
            | MissingOperand { range }
            | Error { range, purpose: RetryNoise | Operand }
Primary ::= Identifier(WordSyntax) | Integer(IntegerSyntax)
          | Parenthesized { open, elements: Vec<R<OperatorChain>>,
                            trailing_comma, close: R<Range>, range }
          | If(IfExpression) | Case(CaseExpression) | Catch(CatchExpression)
          | BracedStatementBlock(BracedBlock)
          | String(StringLiteral) | RuleLiteral(RuleLiteral)
          | RuleExpression(RuleExpression)

OperatorUse { spelling: TextSyntax,
              role: Prefix | Infix | Suffix | Nullfix, range }
PathSegment ::= Identifier(WordSyntax) | SigilIdentifier(WordSyntax)
```

`Error.purpose` is supplied by the recovery owner: a run followed by an
accepted retry is `RetryNoise`; a run that is the chain's terminal operand is
`Operand`. It is never inferred from CST or recovery history. Chains remain
flat source order: no binding power, target edge, or precedence tree is stored.

```text
FixedPostfix ::= Call { open, arguments: Vec<R<OperatorChain>>, close: R<Range>, range }
               | Index { open, items: Vec<R<OperatorChain>>, close: R<Range>, range }
               | Field { dot, name: R<WordSyntax>, range }
               | Path { separator, segment: R<PathSegment>, range }
               | ProjectionTuple { dot, open, items: Vec<R<OperatorChain>>, close: R<Range>, range }
               | ProjectionRecord { dot, open, items: Vec<R<ProjectionItem>>, close: R<Range>, range }
ProjectionItem ::= Expression(OperatorChain) | Spread { marker, rhs: R<Box<OperatorChain>>, range }
ColonApplication { colon, rhs: R<InlineArguments | IndentedBlock>, range }
WithBody { keyword, colon: R<Range>, body: R<InlineStatement | IndentedBlock>, range }
AssignmentTail { equals, rhs: R<AssignmentRhs>, range }
AssignmentRhs ::= Inline(Box<OperatorChain>) | Indented(IndentedBlock)
TypeAnnotationTail { as_keyword, type_expr: R<Box<TypeExpression>>, range }
InlineArguments { arguments: Vec<R<OperatorChain>>, range }
InlineChain ::= Box<OperatorChain>
InlineStatement ::= Box<Statement>

Pattern { head: R<PatternPrimary>, tails: Vec<PatternTail>,
          annotation: Option<PatternTypeAnnotation>, range }
PatternPrimary ::= Identifier(PatternName) | Integer(IntegerSyntax)
                 | Symbol { colon, name: R<WordSyntax>, range }
                 | Parenthesized(PatternGroup) | List(ListPattern)
                 | Record(RecordPattern) | String(StringLiteral)
                 | RuleLiteral(RuleLiteral) | RuleExpression(RuleExpression)
PatternTail ::= Alias { keyword, binding: R<WordSyntax>, range }
              | Alternation { pipe, rhs: R<Box<Pattern>>, range }
PatternTypeAnnotation { colon, type_expr: R<Box<TypeExpression>>, range }
PatternGroup { open, elements: Vec<R<Pattern>>, trailing_comma, close: R<Range>, range }
ListPattern { open, items: Vec<R<ListItem>>, trailing_comma, close: R<Range>, range }
ListItem ::= Pattern(Pattern) | Spread { marker, rhs: R<Box<Pattern>>, range }
RecordPattern { open, items: Vec<R<RecordItem>>, trailing_comma, close: R<Range>, range }
PatternName { kind: Ordinary | Sigil, text: WordSyntax, range }
RecordItem ::= Field { name: PatternName, form: RecordFieldForm, range }
             | Spread { marker, rhs: R<Box<Pattern>>, range }
RecordFieldForm ::= Shorthand
                  | Nested { colon, pattern: R<Box<Pattern>>,
                             default: Option<RecordDefault> }
                  | Default(RecordDefault)
RecordDefault { equals, expression: R<Box<OperatorChain>>, range }
```

The Assignment/TypeAnnotationTail entries are candidate products for the
already admitted structural tails; their grammar and recovery are fixed by
`2026-09-09-successor-expression-structural-tails-draft.md`, but these fields
remain subject to this Draft's M3 approval. Pattern String and RuleExpression
primaries are already admitted by the literal-cone authority, including the
Pattern contextual `rule {}` route. Their fields reuse the companion literal
schema rather than creating Pattern-local literal products. Case/Catch
terminators retain the Authoritative optional semicolon range; they are not
sequence separators.

`OperatorUse` excludes leading/trailing trivia, table identity, binding power
and operand association; the enclosing role-specific ChainItem records its
source position. A PathSegment has no independent recovered separator: its
FixedPostfix Path owner owns that slot, and a successful retry is the next
outer continuation. InlineArguments owns the colon application's nonempty
inline chain vector but no comma products; InlineChain and InlineStatement
are transparent single-child helpers, not list wrappers. These are candidate
products grounded in the existing owner topology. In particular, the proposed
range of an admitted AssignmentTail starts at `=` and ends at the last physical
byte locally published through its RHS, whether that child is complete or
incomplete; when the RHS publishes no physical byte, it ends at `=`. A
TypeAnnotationTail applies the same rule from `as` through its Type child.
Neither range absorbs a Missing coordinate, terminal Error diagnostic extent,
or protected unread successor: physically emitted Error bytes are included by
the publication rule, but no endpoint is inferred from a diagnostic extent.

PatternName preserves the currently accepted ordinary/sigil distinction in
both primary and record-field positions. A committed record name completes its
field skeleton; Default and a Nested default own their actual `=` and required
expression separately. The proposed RecordDefault range begins at `=` and ends
at the last physical byte locally published through its expression, whether
complete or incomplete; it ends at `=` only when that expression publishes no
physical byte.
List/record spread markers similarly commit their outer item while their RHS
remains recovered. These range rules are candidates for M3 review, not a
change to Pattern recovery or CST ownership.

An accepted skeleton retains its variant with incomplete children. Unaccepted
record heads are incomplete record entries; no fabricated name is permitted.
The candidate availability rule for a missing Pattern head followed by an
accepted tail is stated below; before approval it still needs its exact
current-authority/evidence locator and review, rather than a second invented
policy row.

### Candidate inline and Pattern sequence products; not yet selected

`InlineArguments` preserves its existing distinct initial `Rhs` and subsequent
`InlineArgument` obligations. A malformed run followed by an admitted chain
completes that obligation; a boundary without retry leaves it incomplete. A
locally owned comma or qualifying newline advances one argument position;
comma plus qualifying newline still advances once, and a final implicit newline
before End advances none. An outer-owned separator remains unread and creates
no position. Records alone never advance a position.

The candidate wrapper-commit rule is: an admitted first chain **or an actual
local continuation separator** commits InlineArguments. Thus `f:` has its
separate ColonApplication RHS incomplete; `f:, x` has
`[Incomplete, Complete(x)]`; and `f:x,` has
`[Complete(x), Incomplete]`. This is a new product choice, not an inference
from the current CST. The candidate InlineArguments range starts at its first
post-colon byte locally published by this owner and ends at its last, including
owned separators, emitted trivia and Error bytes. The colon remains solely in
ColonApplication. A committed zero-byte vector is zero-width at the post-colon
coordinate; Missing/diagnostic ranges and unread boundary leading do not extend
it.

For Pattern group/list/record forms, the actual opener commits the enclosing
skeleton independently of `PatternCompletion`; unavailable child or close slots
do not erase it. Fresh item Missing adds one incomplete position. Group/list
ordinary-child availability follows the Pattern skeleton rule, including an
admitted tail after a missing head. For Record item-phase lexical/structured
wrong-kind recovery, the candidate mapping reserves one pending item position
across successive recovery units: admitted name/spread retry completes it;
locally owned comma, matching local close, EOF, fence or protected caller-close
handoff finalizes it incomplete. A consumed unclaimed wrong close keeps that
pending position for a later name/spread retry and creates no new position.
Diagnostics do not multiply the entry. Separator-role recovery creates no item
position. A matching initial close means empty contents; one terminal actual
comma adds no position, while fresh repeated commas retain their existing
Missing positions.

An actual spread marker commits a complete spread item with its RHS recovered
independently; an actual field name commits its field, `:` commits its nested
form and `=` commits its default form independently of child completeness.
Delimited ranges start at their actual opener and end at their last locally
published byte, including a matching local close or terminal recovery emission.
Local-close Missing and protected caller/fence handoff do not extend them. Item
ranges exclude sequence-owned leading/separators; spread/default ranges start
at their marker and include all published child/recovery bytes. A missing child
does not reduce either to marker-only when Error bytes were emitted. If
retained, `trailing_comma` means the last actual consumed terminal comma;
recovered separator records never fabricate it. Its state when later recovery
follows that comma remains open.

These are M3 candidate choices. They require exact controls for initial/later
inline slots, local versus outer separators, Pattern retry/finalization, local
wrong close, spread/default terminal recovery and EOF/fence handoff, then
compiler/recovery and specification review plus user approval before any API or
implementation.

```text
BracedBlock { open, statements: Vec<R<Statement>>, close: R<Range>, range }
IndentedBlock { base_indent, block_indent, statements: Vec<R<Statement>>, range }
VirtualStatementBlock { statements: Vec<R<Statement>>, range }

IfExpression { arms: nonempty Vec<IfArm>, else_arm: Option<ElseArm>, base_indent, range }
IfArm { keyword, condition: R<OperatorChain>, body: R<ColonArmBody>, range }
ElseArm { keyword, body: R<ColonArmBody | Box<OperatorChain>>, range }
ColonArmBody { colon: R<Range>, rhs: R<InlineChain | IndentedBlock>, range }

CaseExpression { keyword, label: Option<CaseLikeLabel>,
                 scrutinee: R<Box<OperatorChain>>, block: R<CaseBlock>,
                 base_indent, range }
CatchExpression { keyword, label: Option<CaseLikeLabel>,
                  scrutinee: R<Box<OperatorChain>>, block: R<CatchBlock>,
                  base_indent, range }
CaseLikeLabel { text: TextSyntax, range }
ColonArmLayout ::= Inline | Indented { base_indent, arm_indent }
CaseBlock { colon: R<Range>, arms: R<ArmSequence<CaseArm>>,
            layout: ColonArmLayout, range }
CatchBlock ::= Colon { colon: R<Range>, arms: R<ArmSequence<CatchArm>>,
                       layout: ColonArmLayout, range }
             | Braced { open, arms: R<ArmSequence<CatchArm>>, close: R<Range>, range }
ArmSequence<A> { arms: Vec<R<A>>, trailing_comma, range }
CaseArm { pattern: R<Pattern>, guard:Option<Guard>, arrow: R<Range>, body: R<ArmBody>,
          terminator:Option<Range>, range }
CatchArm { pattern: R<Pattern>, handler: Option<R<Pattern>>, guard:Option<Guard>,
           arrow: R<Range>, body: R<ArmBody>, terminator:Option<Range>, range }
Guard { keyword: If(TextSyntax) | Where(TextSyntax),
        condition:R<Box<OperatorChain>>, range }
ArmBody ::= Inline(Box<OperatorChain>) | Indented(IndentedBlock)
```

A CaseLikeLabel is one accepted sigil-identifier token; `None` is the only
unentered label state. Colon-form block ranges are proposed to start at their
colon and end at the last physical byte locally published through their arm
sequence, including an accepted trailing comma; with no such byte, they end at
the colon. A braced block starts at its opener and ends at a complete close or
the last physical byte locally published by that block, including its arm
sequence, accepted separators and close-recovery leading; returned boundary
leading remains excluded. With neither, it ends at the opener. ArmSequence
excludes the block introducer/close. An arm starts at its first locally
published physical byte, or at its owning recovery anchor when it has none,
and ends at its terminator when present, otherwise at its last locally
published physical byte; an entirely unpopulated arm is zero-width at that
anchor. Inter-arm comma/newline remains list ownership, not arm range. These
candidate physical envelopes preserve the existing distinct
inline/indented/braced forms and do not derive availability from separator
diagnostics.

The optional guard keyword is positive committed evidence. No keyword gives
`None`; an admitted `if` or `where` gives `Some(Guard)` and only its mandatory
`condition` carries `R`. Immediate absence is therefore
`Some(Guard { condition: Incomplete })`; a malformed run followed by a NUD
completes that condition with retry noise; a terminal malformed run leaves it
incomplete without a second Missing. An outer `Option<R<Guard>>` has no
reachable incomplete-guard event and is not selected. Nested operand recovery
keeps its own Expression role. Closing delimiter roles map to their
corresponding `close`; a failed statement sequence position maps to a vector
entry, while separator recovery does not.

`ExpressionList` is distinct from ordinary call lists:

```text
ExpressionList { open, items: Vec<R<OperatorChain>>,
                 separators: Vec<ExpressionSeparator>, close: R<Range>, range }
ExpressionSeparator { kind: Comma | Newline, range, after_items }
```

`after_items` is the number of finalized entries, including incomplete ones,
immediately after any item Missing caused by this separator and before the
separator itself. The owner retains bounded local pending-product state:

| ExpressionList event | candidate product effect |
| --- | --- |
| empty matching close | empty items and separators |
| NUD admitted while expecting an expression | append complete chain; nested recovery remains inside it |
| one or more Item Errors | reserve one pending position; append nothing yet |
| retry NUD after Item Error | finalize that pending position complete |
| comma/newline while expecting an expression | existing Item Missing finalizes one incomplete entry, then append separator |
| comma/newline after an expression | append separator only |
| matching close after a valid separator | no trailing incomplete entry |
| terminal boundary after Item Error | existing Item Missing finalizes the pending position incomplete |
| separator Error | append neither item nor separator product |
| EOF/fence/outer close with protected unread leading | close incomplete; append no separator from the unread leading |

Thus repeated commas/newlines create the currently selected item-Missing
positions, while one retry after a run of Item Errors completes only one
position. No recovery scan or diagnostic record count reconstructs this state.

For every ordinary delimited owner—parenthesized primary, Call, Index,
ProjectionTuple, and ProjectionRecord—an item-role Missing creates one
`Incomplete` vector entry. An item-role Error reserves that entry and finalizes
it complete only if the owner admits a NUD/spread retry; separator/close/
boundary finalizes it incomplete. Separator-role Missing/Error, semicolon
separator recovery, and wrong-close Error create no entry. An initial matching
close produces an empty vector; a single trailing separator produces none;
repeated separators retain their existing item-Missing positions. Record spread
is an admitted complete skeleton with a recovered RHS. This local pending-entry
fact is product-only and bounded: it must not change the existing grammar
phase or be reconstructed from diagnostics.

Chain availability follows the admitted skeleton rather than Error count:

| owner event | product availability |
| --- | --- |
| optional expression non-match | no product |
| initial required expression boundary or terminal malformed-only run | `Incomplete` |
| malformed initial run then admitted NUD | complete chain with `RetryNoise` |
| accepted prefix/infix with absent or terminal-malformed operand | complete chain retaining operator and `MissingOperand`/`Error(Operand)` |
| retry reaches prefix whose operand fails | complete retained prefix skeleton and nested operand failure |
| lower-threshold unread operator/abstract boundary | product unchanged; full Item remains handoff |
| FieldName/PathSegment Error | field/segment is incomplete; the returned identifier is a new outer-tail continuation, not a recovered child |

An accepted Pattern head, tail, or annotation skeleton similarly retains a
complete Pattern with an incomplete head/child as applicable. In particular, a
Missing/Error primary followed by a **committed** Alias, Alternation, or
TypeAnnotation skeleton yields `Complete(Pattern { head: Incomplete, .. })`.
If no primary, tail, or annotation skeleton is committed, Pattern is
`Incomplete`. A candidate rejected by precedence, active stops, layout or a
boundary commits nothing and leaves availability unchanged. This is independent
from the grammar's `PatternCompletion` control state.

## Type and declaration-helper candidates

```text
TypeExpression { leading_effect_row: Option<BracketRow>, primary: R<TypePrimary>,
                 postfix: Vec<TypePostfix>, arrow: Option<TypeArrow>, range }
TypePrimary ::= Identifier(WordSyntax) | SigilIdentifier(WordSyntax) | Number(TextSyntax)
              | Parenthesized(TypeGroup) | Record(TypeRecord) | Forall(ForallType)
              | EffectRow(EffectRowType) | PolymorphicVariant(PolyvariantType)
TypePostfix ::= Path { separator, segment:R<Identifier|SigilIdentifier>, range }
              | Call { open, arguments:Vec<R<TypeExpression>>, close:R<Range>, range }
              | Apply { boundary:Range, argument:Box<TypeExpression>, range }
TypeArrow { argument_effect:Option<BracketRow>, arrow:R<Range>,
            rhs:R<Box<TypeExpression>>, range }
TypeGroup { open, elements:Vec<R<TypeExpression>>, trailing_explicit_separator,
            close:R<Range>, range }
BracketRow { open, items:Vec<R<TypeExpression>>, close:R<Range>, range }
EffectRowType { apostrophe, open, items:Vec<R<TypeExpression>>, close:R<Range>, range }
TypeRecord { open, fields:Vec<R<TypeRecordField>>, trailing_comma, close:R<Range>, range }
TypeRecordField { name:R<WordSyntax>, colon:R<Range>, type_expr:R<Box<TypeExpression>>, range }
ForallType { keyword, binders:nonempty Vec<R<ForallBinder>>, colon:R<Range>,
             body:R<Box<TypeExpression>>, range }
ForallBinder { boundary:R<Range>, name:WordSyntax, range }
PolyvariantType { colon, open, tags:Vec<R<PolyvariantTag>>, trailing_comma,
                  close:R<Range>, range }
PolyvariantTag { name:R<WordSyntax>, payloads:Vec<R<PolyvariantPayload>>, range }
PolyvariantPayload { boundary:R<Range>, type_expr:R<Box<TypeExpression>>, range }
```

A bare bracket is only a committed `leading_effect_row`, never a primary. Its
committed recovery may yield a complete TypeExpression with an incomplete
primary; ordinary terminal required-Type failure remains incomplete at its
caller. Apply admission always has an admitted argument and keeps a complete
boxed child. Item roles create recovered vector entries, separator roles remain
ledger-only, and close roles map to the owner close. The locally Authoritative
PV product keeps `payloads: Vec<R<PolyvariantPayload>>`: an admitted payload
is a complete outer entry even when its boundary/type child is incomplete. This
wrapper is retained rather than silently superseded.

The owner-specific availability rows are:

| owner event | candidate product availability |
| --- | --- |
| ordinary required Type absent/terminal malformed before a primary skeleton | caller's `R<TypeExpression> = Incomplete` |
| committed leading bracket row without a primary | complete TypeExpression with `primary = Incomplete` |
| Type call/group/effect/bracket item Missing | finalizes one incomplete vector entry; a later item starts a distinct entry |
| Type item Error ending at local terminal | current vector entry incomplete; separator Error creates no entry |
| Forall keyword then no first binder | `binders = [Incomplete]`; colon may still be accepted without fabricating a name |
| Forall binder Error then admitted retry | retain the malformed binder entry incomplete; append the admitted binder as a distinct complete entry |
| Forall colon/body unavailable | their own fields incomplete without extra record |
| PV malformed tag run ending at boundary / published Tag Missing | current tag vector entry incomplete |
| PV malformed tag run then accepted name | complete tag entry with complete name and retained later payloads |
| PV wrong-kind head or malformed run then wrong-kind head | complete tag entry with incomplete name and retained later payloads |
| PV payload boundary/type failure after accepted payload skeleton | complete `R<PolyvariantPayload>` entry with recovered boundary/type child; no optional payload invented |
| absent optional payload | no payload entry |

The same actual-owner rule applies to record fields and polymorphic payloads:
an accepted skeleton preserves its inner recovered fields; a wholly unadmitted
list position is incomplete. PV tag/payload ranges start with their committed
head/boundary, exclude outer-list leading already emitted, and end at their last
owned byte; a missing payload boundary is zero-width at the admitted Type
start. Nested Type recovery remains its own owner.

Forall differs from a tag retry: a malformed first-binder run is a completed
incomplete list position before a later apostrophe binder is admitted. The
later binder is therefore a distinct entry, preserving source order and the
Forall recovery authority rather than repairing the malformed entry in place.

### Candidate Type physical envelopes; not yet selected

The following is a coherent M3 candidate, not an implication of the
current-Item recovery authorities. A Type product's physical range is the
envelope of bytes actually published through its selected owner, including
nested children and recovery emission. It begins at that owner's first actual
publication: introductory leading counts when that owner emits it, while
leading already emitted by its caller does not. Availability is independent:
`Incomplete` does not mean no byte was published, while a Missing coordinate
and a diagnostic extent never extend a product range. Actually emitted
close-recovery/ordinary-horizontal leading counts; a protected unread Item and
its leading never count.

| product | candidate start | candidate end |
| --- | --- | --- |
| TypeExpression | first byte published through its admitted primary or leading BracketRow | last byte published through its primary, postfixes, arrow, recovery or owner-emitted trailing trivia |
| TypeGroup / Call / BracketRow / TypeRecord | first delimiter-owner publication, including still-owned introductory leading | actual close end, or last byte locally published by the delimiter owner when close is unavailable |
| EffectRowType | first owner publication, including still-owned introductory leading before its apostrophe | the same delimiter rule, while remaining distinct from a bare leading BracketRow |
| Path postfix | first path-owner publication, including still-owned separator leading | last byte published through the path owner, falling back to its actual `::` when no later byte is published |
| Apply postfix | first physical byte of its admitted argument boundary | last byte published through that argument child |
| TypeArrow | first selected-tail publication, including still-owned leading before its argument-effect row or arrow | last byte published through the arrow owner, falling back to its admitted argument-effect row or actual arrow when no later byte is published |
| ForallType | first owner publication, including still-owned introductory leading before `for` | last byte published through the owner, falling back to actual `for` when no later byte is published |
| ForallBinder | first binder-owner publication, including physically emitted boundary leading | actual binder-token end |
| PolyvariantType | first PV-owner publication, including still-owned leading before adjacent `:{` | actual close end, or last PV-owned emitted byte |
| PV tag / payload | first committed tag head/recovery byte / owned payload-boundary byte, or zero-width at admitted Type start when that boundary is Missing | last tag/payload-owned byte, including nested recovery |

A leading row remains inside TypeExpression when its required head is
unavailable. An argument-effect row belongs to TypeArrow when that tail is
admitted; neither parent is inferred from the shared BracketRow product alone.
Terminal required-Type failure before any Type skeleton is admitted remains the
caller's `Incomplete` product position; it does not fabricate a TypeExpression
only to hold emitted Error bytes. Forall retry keeps the earlier incomplete
binder position and its owner bytes before a distinct later admitted binder;
PV tag retry likewise keeps the earlier same-tag Error bytes.

This candidate leaves the source representation of Apply/Forall/PV payload
boundaries open. TypeRecordField and declaration field mapping follows below.
The table requires compiler/recovery and specification review, exact range
controls, and user approval before it can authorize a product API or
implementation.

### Candidate recovered field products; not yet selected

This narrows and supersedes the preceding open TypeRecordField and later
NamedField/TupleField availability/envelope rows. List-position availability
follows grammar admission; recovery records alone establish neither a completed
field nor its range.

| current owner event | candidate product effect |
| --- | --- |
| TypeRecordField/NamedField actual name | complete field; colon and Type remain independently recovered |
| initial actual colon | complete field with unavailable name, actual colon and required Type |
| malformed name reaching owner-authorized colon | complete colon-bearing field with unavailable name; initial Error remains field-owned |
| whole-field Error stops at a new name/head or at boundary | one incomplete list position; a later admitted head begins a distinct field; no empty completed field |
| Tuple required-Type retries to an admitted Type skeleton | one complete TupleField containing that Type |
| Tuple required-Type never admits a skeleton | one incomplete list position; no complete empty TupleField |
| admitted Type with failed inner child | complete outer field/Type skeleton with recovered child |

Every completed TypeRecordField, NamedField and TupleField ranges from its
field owner's first physical publication through that owner's last, including
internal leading, recovery and child output. A completed TupleField therefore
includes a field-owned required-Type Error before its later admitted Type child;
its child range begins only at that child's own first publication. Sequence
introductory leading and every byte published by the enclosing sequence are
excluded. A field owner never subtracts or reconstructs already emitted
field-owned leading; the still-unread Item and its remaining leading are also
excluded. Missing coordinates and diagnostic extents do not extend any field
envelope.

Record RHS recovery retains the RecordFieldType role, while declaration
required-Type malformed recovery retains native Type(Primary) ownership.
Actual colon followed by terminal malformed RHS leaves Type unavailable while
retaining its emitted field bytes; colon failure at a boundary adds no invented
second diagnostic. Actual matching closes remain list-owned. Struct local
mismatched-close recovery may retry a field; Variant borrowed close remains
unread with unavailable local close; TypeRecord wrong-close recovery remains
close-only and cannot acquire declaration-list retry behavior. Close-recovery
bytes extend a list envelope, never its preceding completed field.

For indented named fields, valid deeper indentation admits its nested sequence;
failed indentation leaves that sequence unavailable while retaining the
colon-bearing Struct form. An entered sequence containing only an incomplete
position retains its actual sequence-emitted bytes. Its enclosing body ends at
the last published body byte, falling back to its colon if there was none.
These remain M3 candidates requiring focused product controls, review and user
approval; they change no existing admission, record or Item handoff rule.

### Candidate Type recursive boundary leaves; not yet selected

An Apply retains `boundary: Range` for exactly the remaining leading physically
published by the Apply owner before its already-admitted argument. Its
nonempty grammar-leading admission predicate is not reconstructed from that
range, which may include foreign-prefix fragments; no recovery wrapper is
introduced. The argument starts after this publication.

A Forall binder retains `boundary:R<Range>` plus its actual apostrophe/name
leaf. Its complete boundary contains binder-owned leading; grammar-absent
boundary remains incomplete under the existing BinderBoundary Missing. The
binder envelope nevertheless begins at its first actual publication, so it
keeps physically emitted foreign leading even when the boundary leaf is
incomplete. The colon leaf contains only its actual token; unavailable colon
remains incomplete. The body uses its admitted Type product, while Forall
retains body retry Error and leading it published before entry. A terminal
malformed body leaves that child incomplete but extends the Forall envelope.

PV payload retains `boundary:R<Range>`. An accepted gap uses its original
payload-owned leading before malformed-run processing; retry leading extends
the payload envelope but not that boundary leaf. An adjacent admitted Type has
an incomplete boundary under the existing Missing, while an absent optional
payload creates no entry. Tag/payload envelopes include their malformed prefix
and nested recovery publication, excluding tag-list leading and returned
successor leading. A wrong-kind tag retains its incomplete name and structured
Type Error. A matched close leaf is only the actual `}`; wrong-close Error and
its leading extend the PV parent, and unavailable close leaves the parent at
its last actual publication.

`nonempty Vec<R<ForallBinder>>` remains an invariant, not a new collection API:
a private ordinary vector is constructed with at least one position after
`for`. First-binder absence yields `[Incomplete]`; a malformed **first-binder**
retry yields an earlier incomplete position plus a distinct complete binder.
After an admitted binder, a colon-role malformed run creates no additional
binder position; only the existing explicit separator-placeholder paths do.
These are M3 candidates requiring exact controls, review and user approval;
they authorize neither a generic nonempty type nor implementation.

```text
InlineStatementBody ::= Inline(Box<Statement>) | Indented(IndentedBlock)
InlineExpressionBody ::= Inline(OperatorChain) | Indented(IndentedBlock)
ModBody ::= Bodyless { semicolon } | Braced(BracedBlock)
          | Colon { colon:R<Range>, body:R<InlineStatementBody> }
ImplBody/RoleBody ::= Bodyless { semicolon } | Braced(BracedBlock)
                   | Colon { colon:Range, body:R<InlineStatementBody> }
ActBody ::= Bodyless { semicolon:Option<Range> } | Braced(BracedBlock)
          | Colon { colon:Range, body:R<InlineStatementBody> }
ForBody ::= Braced(BracedBlock) | Colon { colon:Range, body:R<InlineExpressionBody> }
CastPattern { open:R<Range>, value:R<Box<Pattern>>, close:R<Range>, range }
CastTarget { colon:R<Range>, value:R<Box<TypeExpression>>, range }
CastForm ::= Bodyless { semicolon } | Definition { equals:Range,
             body:R<InlineExpressionBody>, range }

NamedField { name:R<WordSyntax>, colon:R<Range>, type_expr:R<Box<TypeExpression>>, range }
NamedFieldList { open, fields:Vec<R<NamedField>>, trailing_comma, close:R<Range>, range }
TupleField { type_expr:R<Box<TypeExpression>>, range }
TupleFieldList { open, fields:Vec<R<TupleField>>, trailing_comma, close:R<Range>, range }
StructBody ::= Bodyless { semicolon } | CompanionIntroduced
             | NamedBraced(NamedFieldList)
             | NamedIndented { colon, base_indent, block_indent,
                               fields:Vec<R<NamedField>>, trailing_comma, range }
             | Tuple(TupleFieldList)
ImplDescription { colon:Range, value:R<Box<TypeExpression>>, range }
ActSource { equals:Range, source:R<Box<TypeExpression>>, range }
VariantBody ::= Bodyless { semicolon:Option<Range> }
              | Braced { open, variants:Vec<R<Variant>>, trailing_comma, close:R<Range>, range }
              | Colon { colon, body:R<IndentedVariants> }
              | Equals { equals, body:R<InlineVariants|IndentedVariants> }
InlineVariants { variants:Vec<R<Variant>>, trailing_pipe, range }
IndentedVariants { base_indent, block_indent, variants:Vec<R<Variant>>, range }
Variant { name:R<WordSyntax>, payload: Unit | From{keyword,type_expr:R<Box<TypeExpression>>}
        | Named(NamedFieldList) | Tuple(TupleFieldList)
        | Positional{types:Vec<R<Box<TypeExpression>>}, range }
DeclarationParameter ::= Identifier(WordSyntax) | SigilIdentifier(WordSyntax)
DerivesClause { keyword, roles:Vec<R<Box<TypeExpression>>>, via:Option<DerivesVia>, range }
DerivesVia { keyword, target:R<WordSyntax>, range }
DerivesAttachment { position: Header | Trailing, clause:DerivesClause, range }
```

Mod's recovered colon remains distinct from Impl/Role/Act/For actual-only
colons; among Mod/Impl/Role/Act/For only Act has implicit bodyless completion.
Enum/Error have their separately selected implicit bodyless forms. Struct retains a mandatory
`CompanionIntroduced` form rather than a fabricated semicolon. Enum/Error are
distinct declaration products that share neutral VariantBody values while
retaining their role transport. The already-authoritative companion form is
retained exactly with owned leaves. Upstream terminal failure leaves downstream
slots unavailable without creating new recovery records.

`DerivesAttachment.position` deliberately retains the existing two-value
vocabulary. For Act, clauses after the head and after the source are both
`Header`; source order and each attachment's range distinguish them. A clause
after the body is `Trailing`. No `BeforeSource`, `AfterSource`, or `AfterBody`
identity is introduced.

Act body availability is not inferred from a successful handoff:

| Act event after the Head or actual Source slot | candidate body / companion |
| --- | --- |
| complete predecessor + approved clean boundary | `body = Complete(Bodyless { semicolon: None })`; zero recovery and boundary remain unread |
| actual semicolon | `body = Complete(Bodyless { semicolon: Some(_) })` |
| actual brace or colon form | complete selected body skeleton; its required child/close has its own `R` availability |
| accepted post-Head or post-Source companion | `companion = Some(_)`, `body = Incomplete`, with no Body/BodyIntroducer cascade; post-Head also leaves `source = None` |
| incomplete Head/Source reaches the same boundary | `body = Incomplete`; do not manufacture implicit bodyless success or a same-cause body record |
| nonempty malformed body-introducer run then actual starter | retain the existing BodyIntroducer Error and retry the selected body form |
| nonempty malformed body-introducer run reaches boundary | `body = Incomplete` with that Error; do not convert it to clean bodyless success |
| actual colon followed by unavailable inline/indented body | complete `Colon` skeleton with its body child incomplete; Body recovery remains the colon-body owner |

`ImplDescription` is a distinct actual-colon product, not an annotation on a
body colon. At the first post-head colon, no following physical newline selects
`description = Some(ImplDescription { colon, value })`; its successor is then
judged for `ImplBody`. A newline-bearing first colon selects
`description = None` and `ImplBody::Colon` directly. After a description,
the next actual colon is a body colon. Thus `impl T: D: x` owns two different
colons, while `impl T:\n  x` owns only the body colon. A missing description or
an independently missing body preserves the other available field. When an
actual description colon has no value at its boundary, both
`description.value` and the still-unentered `body` are incomplete, but this is
one description recovery cause, not a second body recovery.

## Declaration and root candidates

All declaration slots below use the common `R` rule; current typed recovery
roles map directly to the named required field. Inline/indented bodies retain
their distinct accepted form.

```text
VisibilitySyntax ::= ImplicitPrivate
                   | Explicit { value: Private | Our | Public, keyword, range }
DeclarationParameter ::= Identifier(WordSyntax) | SigilIdentifier(WordSyntax)
```

Implicit private visibility carries no synthetic range or token. `my` must
remain explicit even where its semantic visibility equals private. Where a
declaration admits parameters, they are actual leaves in source order; an
absent list is empty and neither creates a zero-width list nor an incomplete
placeholder. These are candidate lossless syntax leaves; owner-specific
malformed/range mappings remain in the pre-approval locator closure.

| statement | candidate fields |
| --- | --- |
| Binding | `visibility, target:R<Pattern>, definition: Option<{equals, body:R<InlineChain\|IndentedBlock>}>, range` |
| Use | `visibility, tree:R<UseTree>, range`; see dedicated tree below |
| Mod | `visibility, test_marker, name:Option<R<WordSyntax>>, body:R<ModBody>, range` |
| Struct | `visibility, name:R<WordSyntax>, derives, body:R<StructBody>, companion, range` |
| Type | `visibility, name:R<WordSyntax>, parameters:Vec<DeclarationParameter>, derives, form:R<Nominal\|Equality{equals:R<Range>,rhs:R<Box<TypeExpression>>}>, companion, range` |
| Impl | `visibility, head:R<Box<TypeExpression>>, description, body:R<ImplBody>, range` |
| Cast | `visibility, pattern:R<CastPattern>, target:R<CastTarget>, form:R<CastForm>, range` |
| Role | `visibility, head:R<Box<TypeExpression>>, body:R<RoleBody>, range` |
| Act | `visibility, head:R<Box<TypeExpression>>, derives:Vec<DerivesAttachment>, source, body:R<ActBody>, companion, range` |
| Enum / Error | distinct declarations with `visibility, name:R<WordSyntax>, parameters:Vec<DeclarationParameter>, derives, body:R<VariantBody>, companion, range` |
| For | `label, pattern:R<Box<Pattern>>, in_keyword:R<Range>, iterable:R<OperatorChain>, body:R<ForBody>, range` |

Named fields retain `name:R<WordSyntax>, colon:R<Range>, type_expr:R<Box<TypeExpression>>`;
tuple fields retain recovered types; field lists retain actual opener, entries,
accepted trailing punctuation, recovered close and range. Variants retain
`name:R<WordSyntax>` plus unit/from/named/tuple/positional payload forms and
their recovered child lists. Derives retains its clause and recovered type
entries. Declaration companions retain their already-authoritative companion
shape, using owned leaves only.

An attachment's candidate range equals its sole DerivesClause range; attachment
position is chosen only at its owner entrypoint, never reconstructed from CST
order. Actual body introducers begin their selected helper range and that range
ends at the last locally owned child/recovery byte, excluding returned
separator/dedent Items. This preserves Mod's recovered-colon distinction,
actual-only Impl/Role/Act/For colons, and Struct's accepted
CompanionIntroduced variant without fabricating a semicolon. The exact range
row for each body branch remains a review obligation.

### Candidate declaration sequences; not yet selected

Declaration parameters are actual `Identifier`/`SigilIdentifier` leaves only:
each spans its spelling and excludes preceding gap. Their empty vector means no
parameter was admitted, with no synthetic wrapper or unavailable slot. Admission
requires the current nonempty same-line grammar gap and accepted spelling;
rejection preserves input. Parameters alone have no aggregate named range.

| product | candidate availability | candidate physical envelope |
| --- | --- | --- |
| NamedField | actual name or colon commits a field skeleton; malformed input reaching colon commits its colon-bearing skeleton with unavailable name; terminal malformed start is an unavailable list position | first field-owner byte through last owned name/colon/Type/recovery byte |
| TupleField | an admitted Type commits its skeleton; unavailable Type is an unavailable list position, never both an incomplete list entry and a complete empty TupleField | Type child envelope |
| delimited field list | actual opener commits even an empty list; missing/borrowed close retains fields and unavailable `close` | opener through last locally emitted byte, including local recovery, never unread foreign close/leading |
| indented named fields | actual colon commits the Struct form; only valid deeper indentation admits its nested sequence | colon through last locally emitted body byte; exact empty-entered-sequence endpoint remains open |
| VariantBody | actual brace, colon or equals commits the selected form; failed required indentation leaves that form complete with unavailable nested sequence | introducer through last locally emitted body byte, subject to each form's close/dedent handoff |
| Variant | accepted/retried name retains its Unit/From/Named/Tuple/Positional skeleton; actual `from` or payload opener commits its required child/list; terminal malformed name leaves an unavailable position | first variant-owner byte through the last byte published by that owner, falling back to the actual name |
| DerivesClause | actual `derives` commits a clause with one required role; every actual comma adds one required role position; actual `via` commits a DerivesVia skeleton with required target | first clause-owner byte through the last byte published by that owner, falling back to the actual `derives` keyword |

All candidate envelopes retain physically emitted owned bytes even when a child
is unavailable; neither Missing anchors nor diagnostic extents substitute for
them. Retry leading belongs exactly to the owner that emits it. Parent envelopes
may therefore include recovery bytes that no completed child represents.

The candidate separator rules remain owner-specific. Field lists admit commas
and qualifying newline; semicolon remains recovery, matching close has priority
and no field is created merely because close follows a separator. Braced
variants admit comma/qualifying newline but not pipe; equals-inline variants
admit pipe but not comma or implicit newline; colon-/equals-indented variants
admit pipe, comma and exact-baseline newline, while dedent ends their sequence.
One initial non-braced pipe is admitted without an unavailable variant. Struct
local mismatched close may recover and retry; Variant field lists borrow a
foreign close, retain unavailable local close, and preserve that Item.

These are M3 candidates. Tuple-field availability, empty entered-sequence
endpoints, retention of accepted interior separators, exhaustive malformed
NamedField retry and Enum/Error parameter exclusions remain open. They need
exact controls and compiler/recovery plus specification review before user
approval or any API/implementation.

`UseTree` is structural syntax, never flattened header projection:

```text
UseTree { range, form, prefix: UsePath, terminal, aliases, qualifiers:UseQualifiers }
UsePath { segments: Vec<R<UseSegment>>, separators: Vec<UseSeparator> }
UseSegment ::= Word(WordSyntax) | Operator { spelling:R<TextSyntax>, close:R<Range>, range }
UseTerminal ::= Single | Group { join:Option<UseSeparator>, group: UseGroup }
                | Glob { join:Option<UseSeparator>, star:Range,
                         without:Option<UseWithout> }
UseGroup { delimiter, entries: Vec<R<UseTree>>, close:R<Range>, range }
UseAlias { target:R<WordSyntax>, range }
UseQualifiers { version:Option<UseVersion>, anchor:Option<UseAnchor> }
UseVersion { spelling:TextSyntax, range }
UseAnchor { keyword:Range, path:UseAnchorPath, range }
UseAnchorPath { segments:nonempty Vec<R<WordSyntax>>, separators:Vec<UseSeparator> }
UseWithout { keyword:Range, entries:nonempty Vec<R<UseExclusion>>, range }
UseExclusion ::= Segment(UseSegment) | Glob { range } | Group(UseGroup)
```

Import Path/Alias/GroupEntry/close roles attach only to their immediate tree
slot. An admitted `with`, `without`, alias, form marker, group opener, glob
star or operator-name opener retains its own skeleton; its missing mandatory
child is incomplete and terminal Error does not erase the tree. An inline-gap
Missing can precede an immediately admitted child, so availability is never
deduced from a record alone. Group leading/repeated comma creates an incomplete
entry; a missing comma before an admitted sibling and wrong-close recovery add
none. Group Error may retry one entry or terminally leave it incomplete. A
prefix separator followed by a missing segment retains that separator and one
incomplete segment. Group/glob joins are not prefix separators. Empty prefixes
remain valid for leading groups/globs and stripped Realm/Band markers, so the
exact invariant is
`prefix.separators.len() == prefix.segments.len().saturating_sub(1)`.

`with` anchor paths admit only words joined by slash or `::`; they are not
general operator-name paths. Versions are raw `TextSyntax`, never normalized
or semver-validated. `without = None` differs from an admitted `without` with
an incomplete first exclusion. Exclusion groups carry recursive ordinary
`UseTree` entries, rather than recursively nesting `UseExclusion`; glob aliases
remain on the enclosing tree before exclusions.

Header projection remains a separate all-or-none per-declaration fact batch
and cannot flatten or invalidate this product. A recovery alone does not
invalidate it, while glob/qualifiers, multiple aliases, or invalid route shape
can. This Draft neither changes `HeaderImport` nor makes materialization resolve
qualifiers.

`OperatorDefinition` groups header and body as one syntax product despite their
approved sibling CST topology:

```text
OperatorDefinition { header:R<OperatorHeaderSyntax>, body: NotEntered | R<OperatorChain>, range }
OperatorHeaderSyntax { visibility:VisibilitySyntax, lazy:Option<Range>,
                       signature:R<OperatorSignature>, range }
OperatorSignature ::= Prefix{fixity,name:R<OperatorName>,right:R<BindingPower>,equals:R<Range>}
                    | Infix{fixity,name:R<OperatorName>,left:R<BindingPower>,right:R<BindingPower>,equals:R<Range>}
                    | Suffix{fixity,name:R<OperatorName>,left:R<BindingPower>,equals:R<Range>}
                    | Nullfix{fixity,name:R<OperatorName>,equals:R<Range>}
OperatorName { spelling:TextSyntax, close:Range, range }
BindingPower { components:Vec<NumberSyntax>, range }
```

No actual `=` means `NotEntered` body, not a fabricated body Missing. An
accepted header fact survives malformed/missing body; cell headers never enter
table compilation. Under current admission an `OperatorName` is an all-or-none
parenthesized atom: incomplete name recovery belongs to its enclosing
`OperatorSignature`, not to fabricated inner spelling or close slots. Any
partial-name product needs a separate admission and product decision. Exact
header-failure completeness and body Error→boundary mapping are:

`fixity` is an actual keyword range and `lazy` is absent or its actual keyword
range, never a semantic boolean. The header range is proposed to start at an
explicit visibility keyword when present, otherwise at `lazy` or `fixity`, and
to end at its last locally published actual header byte: the actual `=` when
present, otherwise whichever visibility, `lazy`, fixity, signature or recovery
byte it last publishes. It excludes following trivia/body and does not borrow a
Missing coordinate or unread successor. Operator-name subfragments and
binding-power digits/dots must enter the later materializer as verified source
partitions, not copied spellings or assumed contiguous tokens. Their exact
coordinate publication remains a seam-review obligation.

| header/body event | candidate availability |
| --- | --- |
| admitted visibility/lazy header skeleton but no fixity | complete header with incomplete signature; no signature fields fabricated |
| fixity admitted, later signature slot Missing/Error then boundary | accepted signature skeleton with that slot incomplete; later slots only where actually admitted |
| actual name/applicable powers/`=` | complete signature regardless of header projection success |
| no actual `=` | `body = NotEntered` and pending Item preserved |
| actual `=` then body boundary | `body = Incomplete` and current body Missing record retained |
| body Error then NUD | complete body chain plus body Error record |
| body Error then boundary | body incomplete while retaining existing Error and body Missing records |

`BindingPower` is syntax spelling/components, never the normalized table value.
Header projection/frozen reconciliation stays independent: source-leading
projection may reject an otherwise retained syntax skeleton, and no AST is
rebuilt from `HeaderOperator`.

`SourceRoot { statements: Vec<R<Statement>>, range }` shares declaration
payloads with nested statements. Root-only operator header/body assembly and
leading-header projection stay separate. Root availability is published by its
own driver, never reconstructed from records:

| root event | candidate product effect |
| --- | --- |
| Statement admitted | append `Complete(statement)`; recovered mandatory children remain in that statement |
| `Statement(Starter)` Error | append one terminal `Incomplete` statement position for the full lexical run |
| `Statement(Separator)` Error | sequence-owned ledger evidence only; append no statement |
| `Statement(TrailingInput { owner })` Error | sequence-owned ledger evidence only; append no statement or extend the preceding declaration |
| trivia, semicolon, ordinary EOF, abstract fence | append nothing |
| OperatorDefinition body recovery | retain it in the logical `OperatorDefinition.body` despite its sibling CST placement |

Thus a root Error never silently attaches to a child, but neither does every
root-owned Error become a fabricated Error-statement product.

### Candidate SourceRoot physical envelope; not yet selected

The candidate SourceRoot range is the physical envelope of its root owner's
input region, including owner-emitted trivia and recovery. It is not formed by
unioning statement ranges: a trivia-only or Error-only root still occupies its
physical source. Missing locations and diagnostic extents do not enlarge it.

| construction | candidate range | excluded physical text |
| --- | --- | --- |
| full source facade | `0..source.len()`, including leading/trailing trivia and Root Error bytes; empty source is `0..0` | none within the source input |
| selected Yumark cell | `body_start..body_end` in the owning document coordinate space; `body_start` is the outer body's explicit entry coordinate and `body_end` is its consumption frontier after terminal body-leading publication | outer opener, close/transition boundary line and unread suffix |

The selected-cell form includes accepted foreign prefixes, including a
leading-only EOF prefix, but does not consume boundary facts merely to extend
its range. Its current wrapper is still test-only; this is a candidate product
decision for the later document owner, not permission to expose that wrapper.
The existing root availability table remains unchanged: a Starter Error makes
one incomplete statement position, while Separator/TrailingInput Error remains
sequence evidence even though its emitted bytes are inside the root range.
Whether the terminal frontier always equals a pending boundary coordinate is
explicitly unselected and must be proved separately for EOF, close and
transition exits.

## Evidence-backed closure queue; no candidate selection

The following finite queue records current-owner evidence that the candidate
schema still needs. It neither selects a range/API nor turns a recovery fact
into materialization authority.

| family | established current-owner evidence | still required before approval |
| --- | --- | --- |
| Type core and delimiters | `type_expr/mod.rs` owns primary/tail/apply/arrow progression; `type_expr/delimited.rs` owns Call, Group, EffectRow and BracketRow items/closes; the required-Type, leading-row-head and P/E current-Item records fix their recovery and handoff | physical endpoints for TypeExpression, rows, postfixes, arrow, groups, records and closes, including terminal emitted Error and returned boundary leading; source representation/range for Apply's `boundary`; exact accepted trailing-separator leaves |
| Type recursive forms | `type_expr/forall.rs` owns the distinct malformed-binder retry; `type_expr/variants.rs` owns PV tag/payload sequences; `type_expr/mod.rs` dispatches record/forall/effect/PV primaries | Forall binder/colon/body, TypeRecordField, PV/tag/payload envelopes and all recovered-close endpoints; `nonempty Vec` concrete representation remains an API choice |
| Inline and Pattern lists | `expression/tails/colon.rs` distinguishes first RHS from later InlineArgument; `pattern/delimited.rs` owns group/list/record comma/layout/close and spread/default children | first versus subsequent slot availability, retry/error-to-entry mapping, separator treatment and physical endpoints per owner; do not borrow the ordinary ExpressionList rule |
| Declaration list helpers | `declaration/type_decl.rs`, `enum_decl.rs` and `error_decl.rs` admit only contiguous, same-line parameters; `declaration/fields.rs` owns field-list slots/closes; `declaration_variant.rs` owns form-specific variant separators/payloads; `declaration/derives.rs` owns required role and independent `via` target | parameter range/no-wrapper contract; field/variant/derives entry, separator, borrowed-close and endpoint rows for each form |
| SourceRoot and coordinate publication | `source_file.rs` creates only Rowan Root plus recoveries; `root_statement.rs` owns root progression/leading/Error handoff; `cst_output/mod.rs` accounts raw token bytes without general coordinates; `lexical/item.rs` derives Item parts from threaded origin | selected SourceRoot range convention for full source versus selected cells, trailing trivia/fence relation, product recovery mapping, and a shared coordinate-publication surface. The mechanically available full-source span is not yet a selected semantic range |

The exact current tests for these queues are `tests/colon_sequence.rs`,
`tests/colon_with_recovery.rs`, `tests/pattern/recovery/sequence.rs`,
`tests/pattern/recovery/delimited.rs`, `tests/declaration/type_decl.rs`,
`tests/declaration/declaration_variant.rs`, and the type/declaration
owner-local suites. They are evidence controls, not authorization to change
their expectations.

## Mandatory pre-approval closure

1. Give every row above a field-to-current-authority/evidence locator and
   resolve historical local-authority versus Proposal status.
2. Close every currently reachable candidate product: TypeExpression and its
   record/forall/effect-row/polyvariant/bracket families; all declaration body,
   form, parameter, derives, companion, variant and field products; and every
   recursive list's exact range/recovery mapping. Candidate prose is not an
   adopted product until its field-to-authority/evidence locator is reviewed.
3. Adjudicate and mark the candidate choices for missing Pattern heads with
   tails, ordinary delimited expression entries, ExpressionList separator
   correspondence, exact Type/PV availability, operator-header
   signature/failure mapping, and every field-to-authority locator. The first
   four have candidate mappings in this Draft; their open state is approval,
   locator and review, not an absence of proposed shape.
4. For flat chains, distinguish wholly unavailable initial expressions from
   accepted chains whose operand is missing or terminally malformed; define
   successful retry and nested-operand outcomes without deriving them from an
   exit or a record count.
5. Finish the companion literal schema and common source-backed coordinate,
   provenance, recovery-ledger and physical-publication contracts. Its physical
   fragment cursor is emission-local and monotone: derive/validate an Item
   partition once per Item emission, never by repeatedly calling extent/cursor
   derivation per fragment. Direct CST replaces rather than wraps the current
   counter path, with no AST storage or dynamic dispatch.
6. Name exact superseded paragraphs; retain effect-free entry, Item handoff,
   frozen header reconciliation, structured reservation and extent rules.
7. M3 compiler/recovery, specification and static performance review must
   challenge the complete product closure before user approval. The pilot needs
   deep accepted/recovered nesting and static direct-path/code-size evidence;
   timing is conditional on material uncertainty after that inspection.

After approval, first extract the common ledger/account with direct CST
unchanged, then pilot a closed recursive family in both modes. No family may be
silently replaced with a placeholder. The outer Yumark document/frame and
public AST surface remain later gates.
