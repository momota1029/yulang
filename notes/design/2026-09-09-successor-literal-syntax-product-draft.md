# Draft: successor literal syntax products

Status: Draft; not implementation authority

Date: 2026-09-09

Scope: owned syntax products for the already-authoritative String, String
interpolation, Rule DSL, and expression/Pattern RuleLiteral grammar. This is a
companion to the canonical materialization-seam Draft, because selected Yumark
cells require actual canonical `Vec<Recovered<Statement>>` and literals are
already admitted canonical expressions. It does not change literal acceptance,
CST, recovery roles, HIR/runtime interpretation, Yumark fence forms, or public
entrypoints.

Authority considered: `2026-09-05-direct-literal-cone-addendum.md` §§1--8;
the chasa architecture's mandatory-slot `Recovered<T>` rule; typed-output and
structured-recovery amendments; and parsed-Yulang-fence addendum §4.

## Missing authority

The literal-cone addendum is Authoritative for grammar, direct CST, recovery,
and fenced streaming, but explicitly excludes AST/HIR interpretation. Its
later StringLiteral, RuleLiteral, and Rule ExpressionList recovery addenda are
also recovery-only. No later Authoritative literal syntax product was found.

Thus a canonical materializer cannot honestly return a Statement product for a
cell containing a string or rule literal. It may not substitute a raw range,
CST handle, whole-body source copy, placeholder Statement, or
`Recovered::Incomplete`. This Draft proposes the required syntax-only product
schema for a later user-approved companion amendment.

## Retained rules

- Literal owners alone select grammar form, consume lexical Items, publish
  recovery, and return fence/outer boundaries. Materializers construct products
  only after these decisions.
- String/Rule product construction happens in the same one-forward driver as
  direct CST; no CST walk, source replay, dequoted/body buffer, event tape,
  nested public parse, second builder, or duplicated literal grammar exists.
- Products retain syntax, not decoded runtime strings or escape semantics.
  A physical range is metadata, never a substitute for the move-only Item
  handoff. Accepted foreign quote prefixes remain in the physical envelope but
  do not become logical literal content.
- `Recovered<T>` describes mandatory semantic-fact availability. A retained
  value may coexist with a committed Error; one record neither creates a new
  record nor makes every enclosing product incomplete.

## Candidate product schema

Every node below carries its physical source envelope. Token leaves use the
canonical Draft's candidate `TextSyntax { physical, logical }` coordinate
representation: an inline contiguous logical range or a boxed, coalesced range
slice only after two non-adjacent logical fragments. They retain no `Item`,
short payload view, decoded value, source/body buffer, or source owner; only
the completed AST package owns the source allocation used by package-derived
views. Each leaf coordinate comes from the Item owner's sealed one-pass
`PublishedFragment`, never from emitted byte counts or a second prefix scan.

```text
StringLiteral {
  form: Normal | Heredoc { quote_count },
  open, pieces: Vec<StringPiece>, close: Recovered<Range>, range,
}
StringPiece ::= Text(TextSyntax)
              | Escape(StringEscape)
              | Interpolation(StringInterpolation)
StringEscape {
  lead,
  form: Simple { target: Recovered<TextSyntax> }
      | Unicode { open, digits: Recovered<TextSyntax>, close: Recovered<Range> },
  range,
}
StringInterpolation {
  percent, format: TextSyntax,
  body: Absent { open: Recovered<Range> }
      | Present { open, statements: Vec<Recovered<Statement>>,
                  close: Recovered<Range> },
  range,
}

RuleExpression { keyword, body: RuleBody, range }
RuleBody { open, alternatives: RuleAlternation, close: Recovered<Range>, range }
RuleAlternation {
  sequences: Vec<RuleSequence>, separators: Vec<RuleSeparator>, range,
}
RuleSeparator ::= BodyPipe(Range) | BodyNewline(Range)
                | ParenPipe(Range) | ParenComma(Range) | ParenNewline(Range)
RuleSequence { items: Vec<Recovered<RuleItem>>, range }
RuleItem { atom: RuleAtom, postfixes: Vec<RulePostfix>, capture: Option<RuleCapture>, range }
RuleAtom ::= Identifier(WordSyntax) | SigilIdentifier(WordSyntax)
           | Integer(IntegerSyntax) | Any(Range) | String(StringLiteral)
           | Parenthesized { open, alternatives: RuleAlternation, close: Recovered<Range> }
           | Expressions(ExpressionList { open, items, separators,
                                          close: Recovered<Range>, range })
RulePostfix ::= Quantifier { kind: Star | Plus | Optional | LazyStar | LazyPlus, range }
              | Field { dot, name: Recovered<WordSyntax> }
              | Path { separator, name: Recovered<WordSyntax> }
              | Call(ExpressionList) | Index(ExpressionList)
RuleCapture { equals, rhs: Recovered<Box<RuleItem>>, range }

RuleLiteral { form: ExpressionTilde | PatternQuote,
              open, pieces: Vec<RuleLiteralPiece>, close: Recovered<Range>, range }
RuleLiteralPiece ::= Text(TextSyntax)
                   | Interpolation { open, sequence: RuleSequence, close: Recovered<Range> }
                   | LazyCapture { colon,
                         form: Name(Recovered<TextSyntax>)
                             | Braced { open, text: TextSyntax, close: Recovered<Range> } }
```

The terminal capture RHS owns its own postfixes; it is not flattened onto the
left RuleItem. Empty Rule alternatives remain actual empty `RuleSequence`
values. Body alternatives use only `|` and newline separators; parenthesized
alternatives additionally admit comma. Separators occur in source order between
their adjacent sequences. Empty, adjacent, and terminal separators retain an
actual empty `RuleSequence` child: consequently there is exactly one more
sequence than separator in every alternation, including a trailing separator.
`ExpressionList` is the canonical list product: its opener, items,
comma/newline separators, and recovered local close remain owned by that list,
not by Rule atom/call/index wrappers.

## Recovery-slot mapping

| immediate recovery | product home |
| --- | --- |
| String terminator | `StringLiteral.close` |
| simple escape target | `StringEscape::Simple.target` |
| Unicode no valid digits (`\u{}` or malformed-only run) | `StringEscape::Unicode.digits = Incomplete`; retain the one existing Error/Missing only |
| Unicode accepted digits followed by Error | `digits = Complete(TextSyntax)`; retain Error separately and continue to the selected close outcome |
| Unicode end | `StringEscape::Unicode.close` |
| interpolation open missing | `StringInterpolation::Absent.open` only |
| interpolation close | `StringInterpolation::Present.close` |
| Rule body/parenthesis close | matching `RuleBody`/`RuleAtom::Parenthesized` close |
| Rule capture RHS, field/path name | matching mandatory child slot |
| malformed Rule item at a sequence item position | current `RuleSequence.items = Incomplete`, then retry the next sequence item |
| malformed capture RHS | `RuleCapture.rhs` retry Error only; a successful retry is `Complete(rhs)`, and close/boundary yields its `Incomplete` without an outer sequence entry |
| RuleLiteral terminator/interpolation close | matching RuleLiteral piece/close |
| lazy name/braced close | matching LazyCapture child slot |
| expression-list recovery | canonical `ExpressionList` product only |

No missing interpolation open invents an empty body or close. A Unicode Error
after valid digits retains its accepted escape product; an Error is not
converted to `Incomplete` merely because it occurs within that product. The
same immediate-owner distinction applies to malformed field/path names: their
RuleItem remains complete with the name slot incomplete when the owner accepted
the postfix skeleton; an unaccepted outer Rule item is instead the sequence
entry incomplete. Neither mapping adds or reorders committed records.

## Shared representation dependency

The source-backed coordinate candidate in the canonical materialization Draft
is still unapproved. Its amendment must still prove source provenance,
foreign-prefix exclusion, Item destruction safety, and that committed segment
metadata never becomes a parser event/source buffer. The literal schema cannot
be implemented before that shared representation passes compiler/recovery,
specification, and static performance review.

## Verification required after approval

Prove AST/direct-CST recovery tuples, source progression, and untouched pending
Items agree for normal/heredoc quote counts, UTF-8/CRLF and foreign prefixes,
empty versus missing interpolation opening, Unicode valid-prefix-plus-Error,
nested declaration interpolation, Rule epsilon branches, terminal capture
precedence, both `{a=;b}` and `{a=;}` capture-RHS cases, malformed field/path
names, and every fence exit. Direct CST must
allocate no literal AST vectors; AST mode must build no Rowan tree. Any need
for replay, CST-derived products/extents, an opaque placeholder, fabricated
child, or materializer-selected recovery returns the work to design.

## Approval boundary

This is a new M3 syntax-product decision. It needs compiler/recovery and
specification review together with the canonical materialization amendment,
then recorded user approval before any literal product or shared output change.
