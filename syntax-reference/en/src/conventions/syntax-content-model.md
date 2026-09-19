# Syntax content model

Use this page to find what may appear in each syntax context. It is the
primary navigation layer for accepted `syntax-v0` source forms. A construct
page supplies the BNF-equivalent production for its own form; this page does
not replace or merge those productions.

## Authority and scope

`syntax-v0` is the accepted grammar and direct Rowan CST topology preserved by
the Authoritative *Syntax freeze and vertical-implementation completion-policy
amendment* (2026-09-17). That amendment preserves accepted syntax and recovery
ownership; the cited Authoritative design records define grammar and topology.
Implementation, tests, fixtures, and commits are not normative sources.

The inventory below exhaustively records syntax-v0 placement. Some forms have
no detailed page yet. Their entries record placement only; their governing
Authoritative design record remains the source for production and direct-CST
placement. A detailed page is not implied by an inventory entry.

## Reading productions

Construct-local productions use the following conventional notation unless the
page defines a more specific lexical condition.

| Notation | Meaning |
| --- | --- |
| `A B` | Required sequence of `A` then `B` |
| `[ A ]` | Optional `A` |
| `{ A }` | Zero or more repetitions of `A` |
| `A | B` | One alternative |
| `Name` | Nonterminal defined by the same or a linked construct page |
| `<identifier>` | Lexical placeholder; its accepted token form is defined by the production that uses it |
| `"keyword"` or punctuation | Source spelling required at that position |

The exact meanings of page-local symbols such as trivia, layout, stop, and
separator names are defined on the page that introduces them.

## Source syntax, direct CST, and recovery

The source-syntax model records the Authoritative accepted-valid forms that may
occupy a context. The direct-CST model records
the source-order placement of the corresponding syntax children. It does not
add source forms.

Recovery is a separate reference layer. `Missing`, raw `Error`, and structured
`Invalid` describe retained recovery structure for malformed input; they do not
make malformed text an accepted alternative. See [recovery topology](recovery-error-invalid-topology.md) and [source-root and diagnostic ownership](source-root-and-diagnostics.md).

## Entry contexts

The reference documents these entry contexts:

```text
Root
  root expression or declaration child
  root-only operator definition: OperatorHeader, expression body

Nested statement owner
  Statement
    nested expression or declaration child

Expression
  Pattern
  TypeExpression
```

This is a placement map, not a replacement root production. Root expressions
and declarations are direct `Root` children. A nested statement owner adds the
`Statement` parent; it does not add a statement-sequence wrapper.

## Content-model inventory

### Statement sequence and declarations

In the CST columns, `R` means direct `Root` placement and `S` means direct
placement below a nested `Statement`. “Source order” includes the production's
literal tokens and trivia; named children below list its structural children.

| Context and permitted form | Child grammar and boundary | Direct CST parent | Ordered direct children and cardinality | Authority |
| --- | --- | --- | --- | --- |
| Root or nested Statement: expression statement | [operator chain](../expressions/operator-chain.md); terminal continuation | R: `Root`; S: `Statement` | `OperatorChain`; exactly 1 | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` § “Surface grammar” in dynamic-operator addendum (4375–5012) |
| Root or nested Statement: binding or use | [binding and use](../statements/binding-use.md); statement boundary | R: `Root`; S: `Statement` | `BindingStatement` (visibility, `Pattern`, optional body) or `UseDeclaration` (use tree); exactly 1 | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` § “canonical Statement binding / use declaration extension” (11086–11623) and § “Complete use declaration grammar and projection” (933–1924) |
| Root or nested Statement: nominal or equality `type` | [nominal](../statements/bare-nominal-type.md), [equality](../statements/equality-type.md) | R: `Root`; S: `Statement` | `TypeDeclaration`: header, optional attachments, selected form; exactly 1 | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ `TND-G` and `TD-G` |
| Root or nested Statement: `mod`, `struct`, standalone `impl`, or `cast` | [mod](../statements/mod-declaration.md), [struct](../statements/struct-declaration.md), [impl](../statements/impl-shell.md), [cast](../statements/cast-declaration.md) | R: `Root`; S: `Statement` | Respective declaration node; header then body/form children in source order; exactly 1 | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ “canonical Statement / root Declaration mod declaration extension”, `SD-G`, `IMD-G`, `CAST-G` |
| Supported declaration host: `derives` attachment | [`derives`](../statements/derives-attachment.md); exact positions below | Host declaration | `DerivesClause` children occur in source order, 0 or more per admitted attachment point; never a `Statement` child | Shared clause grammar: `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ `DRV-G`, `DRV-J`; later owner placements are cited below |
| `StructDeclaration`: declaration companion | Exact contextual `with` after header derives and before the body, or after an actual-complete braced or tuple close and trailing derives | `StructDeclaration` | One `DeclarationCompanion` child at either authorized position; it contains `WithKw`, its actual or recovered introducer, then inline one direct `Statement` or one-or-more direct `DerivesClause` children, `DeclarationCompanionIndentedBody` with direct item children, or braces with direct item children, in source order. At most 1 per declaration | `notes/design/2026-08-30-declaration-companion-with-addendum.md` §§ `DC-G`, 6 “Owner and attachment matrix”, 8.2 “CST” |
| `TypeDeclaration`: declaration companion | Exact contextual `with` after header derives and the attached-`impl` probe, or after equality RHS and trailing derives | `TypeDeclaration` | One `DeclarationCompanion` child at either authorized position; it contains `WithKw`, its actual or recovered introducer, then inline one direct `Statement` or one-or-more direct `DerivesClause` children, `DeclarationCompanionIndentedBody` with direct item children, or braces with direct item children, in source order. At most 1 per declaration | `notes/design/2026-08-30-declaration-companion-with-addendum.md` §§ `DC-G`, 6 “Owner and attachment matrix”, 8.2 “CST” |
| `EnumDeclaration`: declaration companion | Exact contextual `with` after header derives, after an actual-complete braced close and trailing derives, or after the equals-inline variant sequence | `EnumDeclaration` | One `DeclarationCompanion` child at the authorized position; it contains `WithKw`, its actual or recovered introducer, then inline one direct `Statement` or one-or-more direct `DerivesClause` children, `DeclarationCompanionIndentedBody` with direct item children, or braces with direct item children, in source order. At most 1 per declaration | `notes/design/2026-08-30-declaration-companion-with-addendum.md` §§ `DC-G`, 6 “Owner and attachment matrix”, 8.2 “CST” |
| `ErrorDeclaration`: declaration companion | Exact contextual `with` after header derives, or after an actual-complete braced close and trailing derives; no equals-inline companion position exists | `ErrorDeclaration` | One `DeclarationCompanion` child at either authorized position; it contains `WithKw`, its actual or recovered introducer, then inline one direct `Statement` or one-or-more direct `DerivesClause` children, `DeclarationCompanionIndentedBody` with direct item children, or braces with direct item children, in source order. At most 1 per declaration | `notes/design/2026-08-30-declaration-companion-with-addendum.md` §§ `DC-G`, 6 “Owner and attachment matrix”, 8.2 “CST” |
| `ActDeclaration`: declaration companion | Exact contextual `with` after Head and header derives, or after Source and header derives; an accepted companion terminates Act continuation | `ActDeclaration` | One `DeclarationCompanion` child at the selected post-Head or post-Source position; it contains `WithKw`, its actual or recovered introducer, then inline one direct `Statement` or one-or-more direct `DerivesClause` children, `DeclarationCompanionIndentedBody` with direct item children, or braces with direct item children, in source order. At most 1 per declaration | `notes/design/2026-08-30-declaration-companion-with-addendum.md` §§ `DC-G`, 6 “Owner and attachment matrix”, 8.2 “CST” |
| `type` declaration: attached `impl` | Type header continuation; type-declaration boundary | `TypeDeclaration` | header, optional derives, `ImplKw`, head `TypeExpression`, optional description, body; at most 1; no nested `ImplDeclaration` | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ `TAI-G`, “AST / direct-CST shape” |
| Root only: operator definition | Operator header and expression-body boundary | `Root` | `OperatorHeader`, then sibling `OperatorChain`; one header/body pair; never `Statement` | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ “Root statement loop”, “Operator definition body full-only continuation” |
| Root or nested Statement: `role`, `act`, `enum`, `error`, or `for` | Declaration/statement-specific body boundary | R: `Root`; S: `Statement` | Respective `RoleDeclaration`, `ActDeclaration`, `EnumDeclaration`, `ErrorDeclaration`, or `ForStatement`; header then direct form/body children; exactly 1 | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ `RLD-G`, `ACT-G`, `ENUM-G`, `ERROR-G`, `FOR-G` and their “AST / direct-CST shape” sections |
| Root or nested Statement: doc-comment declaration with Yumark | Document-envelope and Yumark-block boundary | R: `Root`; S: `Statement` | `DocCommentDeclaration`: marker and `YmDoc` content in source order; exactly 1 | `notes/design/2026-09-01-doc-comment-yumark-addendum.md` §§ 2 “Envelope and dispatch”, 8 “AST, CST, and recovery vocabulary” |

`derives` hosts and positions are exact. `StructDeclaration` admits header
(after its shared header and before its body) and trailing (after an
actual-complete braced or tuple body). `TypeDeclaration` admits header (after
its header and before form selection) and trailing (after an equality RHS).
These Struct and Type positions use `DRV-G`/`DRV-J`. `EnumDeclaration` and
`ErrorDeclaration` admit header and trailing only after an actual-complete
braced close; their owner-specific authority is the architecture record's
respective “Derives composition” sections and the *Direct Enum/Error companion
trailing-close amendment* § “Decision”. `ActDeclaration` admits header derives
after a complete Head, then, when an actual Source is complete, after Source;
it admits trailing derives only after an actual-complete braced close. Its
owner-specific authority is `ACTDRV-G`/`ACTDRV-J`. `Role`, `Impl`, `Cast`,
`Mod`, binding, use, and operator definitions are not `derives` hosts.

### Expression

| Context and permitted form | Child grammar and boundary | Direct CST parent | Ordered direct children and cardinality | Authority |
| --- | --- | --- | --- | --- |
| Expression | [operator chain](../expressions/operator-chain.md); terminal continuation | R: `Root`; S: `Statement` | `OperatorChain`, one; its items retain source order | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` § “Surface grammar” (dynamic-operator addendum) |
| Expression primary: parenthesized form | [parenthesized expressions](../expressions/parenthesized-expression.md); parentheses/separators | `OperatorChain` | `ParenthesizedExpression`, containing 0 or more direct `OperatorChain` elements; at most 1 primary | Parenthesized-expression authority, `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ 4103–4355; layout separator authority |
| Completed chain: call, field, path, ML, index, or projection | [fixed tails](../expressions/call-field-path-tails.md), [index/projection](../expressions/index-projection-tails.md) | `OperatorChain` | corresponding tail nodes and their direct argument/item chains in source order; 0 or more continuations | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ “Call/Field/Path/ML fixed-tail addendum”, “IndexTail/ProjectionTail fixed-tail addendum” |
| Completed chain: type annotation | Annotation continuation boundary | `OperatorChain` | `TypeAnnotationTail`: annotation token then `TypeExpression`; 0 or more nonterminal tails | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` § “Surface grammar” (`TypeAnnotationContinuation`) |
| Completed chain: colon application, assignment, or `with` body | [colon](../expressions/colon-application.md), [assignment](../expressions/assignment-tail.md), [`with`](../expressions/with-body-tail.md) | `OperatorChain` | respective terminal tail and direct body/argument child; 0 or 1 terminal continuation | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ “Valid grammar” (colon), `WithBodyTail` addendum, and assignment direct-inline contract |
| Expression primary: `if`, braced block, `case`, or `catch` | [if](../expressions/if-expression.md), [block](../expressions/braced-statement-block.md), [case/catch](../expressions/case-catch.md) | `OperatorChain` | respective primary node; direct arm/statement children in source order; at most 1 primary at its value slot | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ NUD-primary `if` (5469–6065), braced block (6067–6627), `case`/`catch` (7243–8017) |
| Expression primary: string or rule literal | Literal delimiter boundary | `OperatorChain` | `StringLiteral`, with `StringStart`, `StringText`/`StringEscape`/`StringInterpolation` contents, then `StringEnd`; or `RuleLiteral`, with `RuleLiteralStart`, `RuleLiteralText`/`RuleLiteralInterpolation`/`RuleLazyCapture` contents, then `RuleLiteralEnd`. Each is at most 1 value | `notes/design/2026-09-05-direct-literal-cone-addendum.md` §§ 2 “Exact grammar and lexical ownership”, 3 “Proposed CST and public surface”, 6 “Dispatch and successor acquisition” |
| Expression primary: contextual rule expression | Exact `rule RuleIntroducerTrivia {` | `OperatorChain` | `OperatorChain > RuleExpression`; `RuleExpression` contains `RuleKw`, source trivia, then `RuleBody` in source order. Exactly 1 primary | `notes/design/2026-09-05-direct-literal-cone-addendum.md` §§ 2 “Exact surface grammar”, 6 “Dispatch and successor acquisition”; `LC-8` |

### Pattern

| Context and permitted form | Child grammar and boundary | Direct CST parent | Ordered direct children and cardinality | Authority |
| --- | --- | --- | --- | --- |
| Pattern: core/parenthesized, list, or record primary | [core](../patterns/pattern-core.md), [list](../patterns/list-pattern.md), [record](../patterns/record-pattern.md) | `Pattern` | respective primary node, with direct pattern/item children in source order; one primary per `Pattern` | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ Pattern addendum (6629–7242), ListPattern (8019–8612), RecordPattern (8613–9312) |
| Pattern primary: string literal | A three-or-more quote run at the Pattern literal boundary | `Pattern` | `StringLiteral`, with `StringStart`, `StringText`/`StringEscape`/`StringInterpolation` contents, then `StringEnd`; exactly 1 primary | `notes/design/2026-09-05-direct-literal-cone-addendum.md` §§ 2 “Exact grammar and lexical ownership”, 3 “Proposed CST and public surface”, 6 “Dispatch and successor acquisition”; `LC-5` |
| Pattern primary: rule literal | A one-quote Pattern literal opener | `Pattern` | `RuleLiteral`, with `RuleLiteralStart`, `RuleLiteralText`/`RuleLiteralInterpolation`/`RuleLazyCapture` contents, then `RuleLiteralEnd`; exactly 1 primary | `notes/design/2026-09-05-direct-literal-cone-addendum.md` §§ 2 “Exact grammar and lexical ownership”, 3 “Proposed CST and public surface”, 6 “Dispatch and successor acquisition”; `LC-5` |
| Pattern primary: contextual rule expression | Exact `rule RuleIntroducerTrivia {` | `Pattern` | `RuleExpression`, containing `RuleKw`, source trivia, then `RuleBody` in source order; exactly 1 primary | `notes/design/2026-09-05-direct-literal-cone-addendum.md` §§ 2 “Exact grammar and lexical ownership”, 3 “Proposed CST and public surface”, 6 “Dispatch and successor acquisition”; `LC-5`, `LC-8` |
| Completed Pattern: trailing type annotation | [pattern annotation](../patterns/type-annotation.md); colon/`TypeExpression` boundary | `Pattern` | `PatternTypeAnnotation`: colon then `TypeExpression`; 0 or 1 terminal annotation | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` § `PTA-G` |

### TypeExpression

| Context and permitted form | Child grammar and boundary | Direct CST parent | Ordered direct children and cardinality | Authority |
| --- | --- | --- | --- | --- |
| TypeExpression: core atom/path/call/application/arrow/group | [core](../types/type-expression-core.md); type delimiter/arrow boundary | `TypeExpression` | primary token/node, then source-order tight/apply tails, then optional `TypeArrowTail`; each tail 0 or more, arrow 0 or 1 | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ “Authoritative surface grammar”, “CST vocabulary and shape” (12155–12866) |
| Type primary: named record, `forall`, effect row, or polymorphic variant | [record](../types/named-record-type.md), [`forall`](../types/forall-type.md), [effect row](../types/effect-row-type.md), [variant](../types/polymorphic-variant-type.md) | `TypeExpression` | respective primary node and its direct field/binder/item/tag children in source order; one primary | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` §§ NamedRecordType (12867–13429), Forall (13431–13980), EffectRowType (13982–14525), polymorphic-variant primary (14527–15233) |
| TypeExpression: leading bracket row | [bracket row](../types/bracket-row-grammar.md); row boundary | `TypeExpression` | `BracketRow`, then chain trivia, then mandatory ordinary type head; 0 or 1 leading row | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` § `BR-G` |
| `TypeArrowTail`: trailing bracket row before mandatory arrow | [bracket row](../types/bracket-row-grammar.md); row/arrow boundary | `TypeArrowTail` | optional `BracketRow`, chain trivia, arrow, RHS `TypeExpression`; 0 or 1 row and exactly 1 arrow/RHS slot | `notes/design/2026-08-20-yu-syntax-chasa-architecture.md` § `BR-G` |

The cross-cutting [layout-aware separator authority](../cross-cutting/layout-aware-separator-authority.md), [positional fence](../cross-cutting/positional-fence.md), and [ambient statement-owner boundary](../cross-cutting/ambient-statement-owner-boundary.md) pages define shared boundary rules where a construct page delegates to them.
