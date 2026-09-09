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

The following forms are outside this product closure.  Assignment and type
annotation are current syntax, but their canonical fields remain unselected
until this Draft's M3 materialization closure is approved.  Type-attached
`impl` remains outside both successor promotion and this product closure:

| deferred form | current evidence |
| --- | --- |
| generic expression assignment | Authoritative structural-tail construction is complete; its canonical product field remains pending M3 materialization approval |
| expression `as Type` annotation | Authoritative structural-tail construction is complete; its canonical product field remains pending M3 materialization approval |
| Type-attached `impl` | approved TAI authority; Type owner still returns qualifying `impl` Item pending, so successor implementation/promotion remains deferred |

Binding's actual definition `=`, Type's equality form, and Pattern's `: Type`
annotation are included; none is an expression assignment/annotation variant.
The final Yulang2-compatibility closure must select the two current tail
products and separately construct the deferred Type-attached-Impl gate rather
than treating either omission as product completion.

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
            | TerminalOuter(ColonApplication | WithBody)
            | MissingOperand { range }
            | Error { range, purpose: RetryNoise | Operand }
Primary ::= Identifier(WordSyntax) | Integer(IntegerSyntax)
          | Parenthesized { open, elements: Vec<R<OperatorChain>>,
                            trailing_comma, close: R<Range>, range }
          | If(IfExpression) | Case(CaseExpression) | Catch(CatchExpression)
          | BracedStatementBlock(BracedBlock)
          | String(StringLiteral) | RuleLiteral(RuleLiteral)
          | RuleExpression(RuleExpression)
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

Pattern { head: R<PatternPrimary>, tails: Vec<PatternTail>,
          annotation: Option<PatternTypeAnnotation>, range }
PatternPrimary ::= Identifier(WordSyntax) | Integer(IntegerSyntax)
                 | Symbol { colon, name: R<WordSyntax>, range }
                 | Parenthesized(PatternGroup) | List(ListPattern)
                 | Record(RecordPattern) | RuleLiteral(RuleLiteral)
PatternTail ::= Alias { keyword, binding: R<WordSyntax>, range }
              | Alternation { pipe, rhs: R<Box<Pattern>>, range }
PatternTypeAnnotation { colon, type_expr: R<Box<TypeExpression>>, range }
PatternGroup { open, elements: Vec<R<Pattern>>, trailing_comma, close: R<Range>, range }
ListPattern { open, items: Vec<R<ListItem>>, trailing_comma, close: R<Range>, range }
ListItem ::= Pattern(Pattern) | Spread { marker, rhs: R<Box<Pattern>>, range }
RecordPattern { open, items: Vec<R<RecordItem>>, trailing_comma, close: R<Range>, range }
RecordItem ::= Field { name: PatternName, form: Shorthand
                       | Nested { colon, pattern: R<Box<Pattern>>, default }
                       | Default { equals, expression: R<Box<OperatorChain>> }, range }
             | Spread { marker, rhs: R<Box<Pattern>>, range }
```

An accepted skeleton retains its variant with incomplete children. Unaccepted
record heads are incomplete record entries; no fabricated name is permitted.
The candidate availability rule for a missing Pattern head followed by an
accepted tail is stated below; before approval it still needs its exact
current-authority/evidence locator and review, rather than a second invented
policy row.

```text
BracedBlock { open, statements: Vec<R<Statement>>, close: R<Range>, range }
IndentedBlock { base_indent, block_indent, statements: Vec<R<Statement>>, range }
VirtualStatementBlock { statements: Vec<R<Statement>>, range }

IfExpression { arms: nonempty Vec<IfArm>, else_arm: Option<ElseArm>, base_indent, range }
IfArm { keyword, condition: R<OperatorChain>, body: R<ColonArmBody>, range }
ElseArm { keyword, body: R<ColonArmBody | Box<OperatorChain>>, range }
ColonArmBody { colon: R<Range>, rhs: R<InlineChain | IndentedBlock>, range }

CaseExpression/CatchExpression { keyword, label, scrutinee: R<Box<OperatorChain>>,
                                  block: R<CaseBlock/CatchBlock>, base_indent, range }
CaseBlock { colon: R<Range>, arms: R<ArmSequence<CaseArm>>, layout, range }
CatchBlock ::= Colon { colon: R<Range>, arms: R<ArmSequence<CatchArm>>, layout, range }
             | Braced { open, arms: R<ArmSequence<CatchArm>>, close: R<Range>, range }
ArmSequence<A> { arms: Vec<R<A>>, trailing_comma, range }
CaseArm { pattern: R<Pattern>, guard:Option<Guard>, arrow: R<Range>, body: R<ArmBody>, range }
CatchArm { pattern: R<Pattern>, handler: Option<R<Pattern>>, guard:Option<Guard>,
           arrow: R<Range>, body: R<ArmBody>, range }
Guard { keyword: If(TextSyntax) | Where(TextSyntax),
        condition:R<Box<OperatorChain>>, range }
ArmBody ::= Inline(Box<OperatorChain>) | Indented(IndentedBlock)
```

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
              | Apply { boundary, argument:Box<TypeExpression>, range }
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
| Forall binder Error then admitted retry | current binder entry complete; boundary leaves it incomplete |
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

| statement | candidate fields |
| --- | --- |
| Binding | `visibility, target:R<Pattern>, definition: Option<{equals, body:R<InlineChain\|IndentedBlock>}>, range` |
| Use | `visibility, tree:R<UseTree>, range`; see dedicated tree below |
| Mod | `visibility, test_marker, name:Option<R<WordSyntax>>, body:R<ModBody>, range` |
| Struct | `visibility, name:R<WordSyntax>, derives, body:R<StructBody>, companion, range` |
| Type | `visibility, name:R<WordSyntax>, parameters, derives, form:R<Nominal\|Equality{equals:R<Range>,rhs:R<Box<TypeExpression>>}>, companion, range` |
| Impl | `visibility, head:R<Box<TypeExpression>>, description, body:R<ImplBody>, range` |
| Cast | `visibility, pattern:R<CastPattern>, target:R<CastTarget>, form:R<CastForm>, range` |
| Role | `visibility, head:R<Box<TypeExpression>>, body:R<RoleBody>, range` |
| Act | `visibility, head:R<Box<TypeExpression>>, derives:Vec<DerivesAttachment>, source, body:R<ActBody>, companion, range` |
| Enum / Error | distinct declarations with `visibility, name:R<WordSyntax>, parameters, derives, body:R<VariantBody>, companion, range` |
| For | `label, pattern:R<Box<Pattern>>, in_keyword:R<Range>, iterable:R<OperatorChain>, body:R<ForBody>, range` |

Named fields retain `name:R<WordSyntax>, colon:R<Range>, type_expr:R<Box<TypeExpression>>`;
tuple fields retain recovered types; field lists retain actual opener, entries,
accepted trailing punctuation, recovered close and range. Variants retain
`name:R<WordSyntax>` plus unit/from/named/tuple/positional payload forms and
their recovered child lists. Derives retains its clause and recovered type
entries. Declaration companions retain their already-authoritative companion
shape, using owned leaves only.

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
OperatorHeaderSyntax { visibility, lazy, signature:R<OperatorSignature>, range }
OperatorSignature ::= Prefix{name:R<OperatorName>,right:R<BindingPower>,equals:R<Range>}
                    | Infix{name:R<OperatorName>,left:R<BindingPower>,right:R<BindingPower>,equals:R<Range>}
                    | Suffix{name:R<OperatorName>,left:R<BindingPower>,equals:R<Range>}
                    | Nullfix{name:R<OperatorName>,equals:R<Range>}
OperatorName { spelling:R<TextSyntax>, close:R<Range>, range }
BindingPower { components:Vec<NumberSyntax>, range }
```

No actual `=` means `NotEntered` body, not a fabricated body Missing. An
accepted header fact survives malformed/missing body; cell headers never enter
table compilation. Exact header-failure completeness and body Error→boundary
mapping are:

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
