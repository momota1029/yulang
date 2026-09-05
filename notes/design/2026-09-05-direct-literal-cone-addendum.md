# Direct literal cone for the recursive-descent rewrite

Status: Authoritative

Drafted-by: primary with direct-rewrite architecture mapping

Reviewed-by: independent compiler/recovery, specification, and regression
reviews, 2026-09-05

Approved-by: user, 2026-09-05

Supersedes: none. This supplies the literal grammar/CST/recovery decisions
deliberately left open by the recursive-rewrite and parsed-fence plans.

Scope: This addendum proposes the direct-rewrite grammar, CST, recovery,
current-item ownership, and fenced-cell streaming for normal/heredoc strings,
string interpolation, `rule { ... }`, `~"..."` rule literals, and the later
Pattern routes for those forms. It does not change production dispatch, the
legacy/opaque parser, public `parse_file` reachability, AST/HIR interpretation,
or Yumark integration. Those remain rewrite Gate 9 and parsed-fence Gates 8--9.

Fixed user decisions:

- normal strings accept physical LF and CRLF;
- multiline lexical owners use the existing fence judge and one-forward,
  source-backed stream: no dequoted/body buffer, source replay, second Rowan
  builder, nested public root, token vector, cursor wrapper, or ambient
  literal/fence state; and
- ordinary syntax has no artificial nesting cap.

Authority basis: the recursive-descent rewrite plan §§2--5, the parsed-Yulang
fence addendum §§3, 5, 7--8, and the fenced block-comment lexical capability
amendment. They decide direct procedure, item, boundary, and fence ownership;
they do not define this literal grammar, CST, or literal recovery. Yulang2 and
the frozen opaque scanner are operational evidence only.

This is M3 language/CST/recovery work. LC-1 through LC-12 in §7 are
user-approved on 2026-09-05. Isolated L0 completed on 2026-09-05: it appended
the public literal vocabulary and added the literal-private fragmented emitter
without parsing reachability or changes to existing Item emitters. Isolated L1
also completed on 2026-09-05: its literal lexical Item scanner and one
fence-line transition primitive preserve the one-current-Item handoff without
NUD dispatch. Isolated L2 also completed on 2026-09-05: its test-only
normal/heredoc String construction, escape/recovery, and structural-prefix
handoff remain unreachable from production dispatch. Isolated L3 also completed
on 2026-09-05: percent/format/open-brace construction uses only an injected
borrowed-close witness, without virtual child grammar or production dispatch.
L4 is the next authorized implementation; all later gates retain the stated
construction and joint-certification dependencies.

## 1. Current lexical Item and fence handoff

A literal is a committed primary after its opener has been accepted. Its
interior scanner still constructs one ordinary current lexical `Item` at a
time; it never makes a compound payload containing both accepted literal bytes
and a pending boundary.

The literal-private scanner outcome is exactly:

```rust
enum LiteralPiece {
    Complete(Item),
    Boundary {
        accepted: Option<Item>,
        pending: Item,
    },
}
```

`Complete(item)` is one complete literal lexical Item. `Boundary` has an
already complete `accepted` Item exactly when bytes before the boundary formed
a lexical Item. `pending` is either the original direct `Payload::Eof` Item,
or the original `Payload::Boundary` Item constructed by the fence-aware
current-item builder. It is not reconstructed from the accepted Item, has no
accepted literal bytes or carrier appended to it, and moves to the caller
unchanged. `accepted` is absent when the boundary is encountered before the
next lexical Item has any physical text.

A literal lexical Item is one of the following, each with its exact contiguous
physical envelope:

- `StringText`, `StringInterpolationFormatText`, `RuleLiteralText`, or
  `RuleCaptureText`, maximal under the grammar below;
- a literal start/end/delimiter/escape token; or
- the one non-empty malformed run owned by a literal recovery slot.

The outer NUD Item owns any ordinary leading trivia and the literal start. An
interior literal Item has empty ordinary leading trivia. If an accepted Yumark
body prefix occurs at the beginning of an interior token, that token's physical
payload starts with the prefix; if it occurs inside a text token, the same
text token contains the bytes before and after it. Thus every prefix lies in
exactly one current Item and never crosses an Item part boundary.

That Item owns one lazy `Option<Vec<ForeignSplit>>`, records each accepted
prefix for that Item only, and invokes `PendingFragments::finish` once with
that Item's physical origin and full physical length. The carrier then moves
with the Item to the committed literal owner, which emits it through a
literal-private fragmented emitter on the one existing builder. It is never
emitted while the lexical probe may still return `None`, cloned, appended,
rescanned, or made into a body/event buffer. This is the parsed-fence
addendum's one-carrier-per-interrupted-lexical-Item rule, not a per-text-part
finalization scheme.

There is one transactional boundary: before a literal opener is accepted, its
NUD alternative may reject and restore the token input. From the accepted
opener onward, each literal operation is total: it returns `Complete` or
`Boundary`, emits/recoveries locally, and never returns lexical `None`, rolls
back an Item, or abandons an accepted carrier. Thus `accepted` reaches its
committed literal owner exactly once before that owner returns `pending`.

At a `BorrowedClose`, fence transition, or EOF, the committed literal owner
first emits its `accepted` Item if any, then emits only its own zero-width
recovery, closes its nodes, and returns `pending`. The close/transition line
is not consumed, split, emitted, or sent through a normal token predicate.
The outer Yumark owner later adds its own missing fence close. Therefore the
literal's Missing precedes the Yumark Missing at the same physical boundary.

The ordinary scanner remains branch-free. The fence-aware entry is a
literal-private construction path with only live input, immediate checked
coordinate, `&FenceBoundary`, and the current lexical Item's accumulator. No
source/root/cursor/fence/literal value enters `Recover`, Rowan state, Item
metadata, or persistent parser state.

## 2. Exact surface grammar

`NL` is LF or CRLF. `scalar` is one Unicode scalar value other than LF.
`xid_start` and
`xidc` are Unicode XID start and continuation. `LF` is the one-byte line feed.
`RuleStopKeyword` is one of `do`, `if`, `else`, `case`, `catch`, or `rule`.
`RuleIdentifier` is an `xid_start xidc*` word other than those six spellings,
or `_`; `SigilIdentifier` is one of `$`, `&`, `_`, or `'` immediately followed
by an ordinary identifier. `quote(n)` is exactly `n`
consecutive ASCII quote bytes. `Terminator(mode)` is one quote for normal mode
and the exact whole quote run selected for heredoc mode. `RuleIntroducerTrivia`
is zero or more ordinary source-trivia Items, including horizontal space,
comments, LF, and CRLF; its scanner remains fence-aware at every physical line
transition.

```text
StringLiteral       ::= NormalString | HeredocString
NormalString        ::= '"' StringPiece* '"'
HeredocString       ::= quote(n >= 3) StringPiece* quote(n)
StringPiece         ::= StringText | StringEscape | StringInterpolation

StringEscape        ::= '\\' SimpleEscape | '\\u{' HexDigit+ '}'
SimpleEscape        ::= scalar | LF
StringInterpolation ::= '%' FormatText '{' VirtualStatementBlock '}'

RuleExpression      ::= RuleKw RuleIntroducerTrivia RuleBody
RuleBody            ::= '{' RuleAlternatives '}'
RuleAlternatives    ::= RuleAlternative { RuleBodySeparator RuleAlternative }
                              [ RuleBodySeparator ]
RuleBodySeparator   ::= '|' | NL
RuleAlternative     ::= RuleSequence
RuleSequence        ::= RuleItem*
RuleItem            ::= RuleAtom RuleNonCapturePostfix* [ RuleCapture ]
RuleAtom            ::= RuleIdentifier | SigilIdentifier | integer | '..'
                      | StringLiteral | '(' RuleParenBody ')' | '[' ExpressionList(RBracket) ']'
RuleParenBody       ::= RuleParenAlternatives
RuleParenAlternatives ::= RuleAlternative { RuleParenSeparator RuleAlternative }
                              [ RuleParenSeparator ]
RuleParenSeparator  ::= '|' | ',' | NL
RuleNonCapturePostfix ::= RuleQuantifier | '.' RuleIdentifier | '::' RuleIdentifier
                         | '(' ExpressionList(RParen) ')' | '[' ExpressionList(RBracket) ']'
RuleCapture         ::= '=' RuleItem
RuleQuantifier      ::= '*' | '+' | '?' | '*?' | '+?'

ExpressionRuleLiteral ::= '~"' RuleLiteralPiece* '"'
PatternRuleLiteral  ::= '"' RuleLiteralPiece* '"'
RuleLiteralPiece    ::= RuleLiteralText | RuleLiteralInterpolation | RuleLazyCapture
RuleLiteralInterpolation ::= '{' RuleSequence '}'
RuleLazyCapture     ::= ':' xidc+ | ':' '{' RuleCaptureText '}'
RuleCaptureText     ::= { scalar or LF other than '}' }
```

`StringText` is maximal source between string structural starters and a valid
terminator. It accepts LF, CRLF, UTF-8, braces, and a quote run that is not a
valid heredoc terminator. `SimpleEscape` accepts exactly one scalar or LF. In
the selected migration-compatible contract, `\\\r\n` is two lexical Items: the escape
consumes `\\\r`, and the following `\n` is `StringText`; its line judge runs
after that text Item. The `u{` spelling is recognized only immediately after
the escape lead; otherwise `u` is a simple-escape target. `FormatText` starts
after `%` and is raw through every quote, escape, LF, and CRLF until the first
`{`; only EOF or a Yumark boundary is an unconsumed recovery sentinel before
`{`. It invokes the fence judge before reading each next physical line.

The opener rule is inherited observed behavior, not a new choice: a maximal
run of one quote starts a normal string, a maximal run of three or more starts
a heredoc, and `""` is one empty normal string. LC-1 selects an **exact whole
run** close: a run shorter or longer than the opener is
`StringText`, not a partial close. The old opaque scanner used an at-least-`n`
sentinel; that alternative is rejected in §7.

`VirtualStatementBlock` is a root-style `Statement*` sequence stopped by an
explicit borrowed `RBrace`; it is not a public `Root`, ordinary braced-block
expression, or expression-only shortcut. The sequence's normal statement
recognizer chooses expression statements versus declarations. It owns its
ordinary comma/semicolon/newline separators, but not its outer `}`. This
selected choice follows the earlier architecture's distinct `%{...}` virtual
statement-block owner; it requires the direct root statement/declaration
closure before it can be more than an isolated witness.

`RuleSequence` is a grammar owner for the source-level parser-combinator DSL,
not an extension of host Pratt tails. It never consults the host dynamic
operator table and never gains host ML application. A sequence is allowed to
be empty: it is the DSL's epsilon branch. Therefore an empty body, a trailing
separator, and two adjacent separators are valid respectively as an empty
alternative, a trailing separator, and an intervening empty alternative; none
creates a synthetic missing item. An `NL` ends a sequence and is then owned as
an alternative separator. Other ordinary non-newline trivia may separate two
RuleItems; adjacency works whenever lexical tokenization leaves two RuleItems.

`=` takes one full `RuleItem` right side and is terminal for its outer item:
the RHS owns any postfixes of its own, but no later postfix applies to the LHS.
A no-space postfix accepts every `RuleNonCapturePostfix`; after inline
non-newline trivia only `=` is a postfix. `*?` and `+?` are active lazy
quantifiers in the selected migration-compatible contract. `(`/`RuleParenBody` stays
in the rule DSL. Rule call and index arguments use the direct ordinary
expression-list owner after that owner is available:

```text
ExpressionList(close) ::= [ Expression { ExpressionListSeparator Expression }
                              [ ExpressionListSeparator ] ]
ExpressionListSeparator ::= ',' | NL
```

The `RuleCall` or `RuleIndex` owner consumes its matching close. It invokes the
Gate-4 direct expression entry with `close`, comma, and newline as explicit
borrowed stops. The list allows a trailing separator; a second separator or a
non-expression Item where another expression is required is recovered by that
list owner's `ExpressionListItem` slot. EOF, a fence boundary, or an outer
close emits its `ExpressionListClose` and returns that Item unchanged. A child
expression's own Error/Missing is emitted before this list recovery. This is
the exact ownership contract; it neither calls the legacy parser nor leaves
an unspecified `ExpressionArguments`/`Expression?` production.

`ExpressionRuleLiteral` and `PatternRuleLiteral` share the `RuleLiteral` CST
node and its `RuleLiteralPiece` owner. Their first physical token is uniformly
`RuleLiteralStart`: it covers `~"` in Expression and the one quote in Pattern.
Both terminate on an unescaped one-quote and use the same
`RuleLiteralTerminator` recovery. Backslash is ordinary rule text. `:{}` is a
valid empty braced lazy capture; `:name` requires one or more `xidc`. The
selected spec-first braced capture is raw through `=`, quotes, LF, and CRLF
until its own `}`; a quote inside it therefore cannot terminate the outer
RuleLiteral. In a rule-literal interpolation, `}` is the normal close; an
outer literal quote is a recovery sentinel only when the RuleSequence has
returned to an item boundary. It yields the interpolation's Missing close and
then is accepted by the outer `RuleLiteral`. A quote where a nested
`StringLiteral` is syntactically required remains that nested string's opener.
This prevents an already completed rule item from swallowing the outer
terminator while preserving nested strings in valid rule syntax.

## 3. Proposed CST and public surface

The following `SyntaxKind` values are selected public additions:
`SyntaxKind` is part of the public green-tree surface even while direct rewrite
tests are isolated. The implementation appends values only, preserves every
existing discriminant, updates exhaustive Rowan conversion, and adds
round-trip controls. It does not claim public parser reachability before the
atomic production cutover.

```text
nodes:
  StringLiteral, StringEscape, StringInterpolation, StringInterpolationBody
  RuleExpression, RuleBody, RuleAlternation, RuleSequence, RuleItem
  RuleCapture, RuleQuantifier, RuleField, RulePath, RuleCall, RuleIndex
  RuleLiteral, RuleLiteralInterpolation
  RuleLazyCapture

tokens:
  StringStart, StringEnd, StringText
  StringEscapeLead, StringEscapeSimple
  StringEscapeUnicodeStart, StringEscapeUnicodeHex, StringEscapeUnicodeEnd
  StringInterpolationPercent, StringInterpolationFormatText
  StringInterpolationOpenBrace, StringInterpolationCloseBrace
  RuleKw, RuleQuantifierToken, RuleLiteralStart, RuleLiteralEnd
  RuleLiteralText, RuleLiteralOpenBrace, RuleLiteralCloseBrace,
  RuleLiteralColon
```

Existing punctuation (`LBrace`, `RBrace`, `Pipe`, `Comma`, `Equals`, and so
on) remains its existing token kind under the new owners. `RuleCaptureText`
uses `RuleLiteralText`; it adds no duplicate text token kind. A Pattern uses
the same literal/rule nodes rather than an opaque Pattern token.

This full-word vocabulary is the selected CST choice, not a claim of
byte-for-byte Yulang2 kind naming. In particular, Yulang2 retained
`StringStart` below a one-quote Pattern rule literal; this design instead uses
the uniform `RuleLiteralStart` token for all RuleLiteral routes. §7 exposes
that public CST tradeoff explicitly.

## 4. Exact recovery, stops, and ordering

The direct recovery helper has these literal-local slots. The slot is an
immediate recovery argument selecting one committed `Missing`/`Error`; it is
not stored in `Recover`, an Item, or persistent state.

```text
StringTerminator
StringEscapeSimpleTarget
StringEscapeUnicodeHex
StringEscapeUnicodeEnd
StringInterpolationOpenBrace
StringInterpolationCloseBrace
RuleBodyCloseBrace
RuleParenClose
RuleCaptureRightItem
RuleFieldName
RulePathName
RuleUnexpectedItem
RuleLiteralTerminator
RuleLiteralInterpolationCloseBrace
RuleLazyCaptureName
RuleLazyCaptureCloseBrace
```

Every Missing is zero-width at the unconsumed sentinel. Every Error consumes
the designated non-empty run shown below, never a caller-owned close or fence
boundary. A slot produces at most one Error and at most one Missing. Different
accepted slots may each need their own Missing at one boundary; that is not a
duplicate recovery.

`ExpressionListItem` and `ExpressionListClose` are not literal-local slots:
they belong to the Gate-4 direct `ExpressionList(close)` owner specified in
§2. RuleCall/RuleIndex may invoke that owner but never re-emit, translate, or
supplement either of its recoveries.

### 4.1 String slots

| source at the current slot | committed result | input returned |
| --- | --- | --- |
| valid normal/heredoc terminator | emit matching `StringEnd` | scan literal successor normally |
| EOF, borrowed fence close, or fence transition while expecting terminator | `Missing(StringTerminator)` | exact pending boundary unchanged |
| `\\` followed by ordinary scalar | lead + `StringEscapeSimple` | continue literal |
| `\\` followed by LF | lead + one LF `StringEscapeSimple`; judge before next-line byte | continue literal or return judge boundary |
| `\\` followed by CRLF | lead + CR `StringEscapeSimple`, then a separate LF `StringText`; judge before next-line byte | continue literal or return judge boundary |
| `\\` followed by terminator/EOF/fence boundary | lead + `Missing(StringEscapeSimpleTarget)`; do not consume sentinel | terminator is then accepted, or `StringTerminator` returns boundary |
| `\\u{}` | lead + unicode start + `Missing(StringEscapeUnicodeHex)` + unicode end | continue literal |
| `\\u{` plus hex digits then `}` | ordinary unicode tokens | continue literal |
| `\\u{` plus no hex/digits followed by terminator, `%`, EOF, or fence boundary | `Missing(StringEscapeUnicodeHex)` then `Missing(StringEscapeUnicodeEnd)`; do not consume sentinel | outer string owns that sentinel |
| `\\u{` plus hex digits followed by terminator, `%`, EOF, or fence boundary | `Missing(StringEscapeUnicodeEnd)`; do not consume sentinel | outer string owns that sentinel |
| first non-hex, non-`}`, non-sentinel scalar in a unicode escape | one `Error` consumes the maximal run through but excluding `}`, a terminator, `%`, EOF, or fence boundary; if `}` arrives it is emitted as unicode end, otherwise the absent unicode end is Missing | enclosing literal owns the preserved sentinel |
| `%` followed by `{` | emit percent, maximal format text, and open brace; enter `StringInterpolationBody` | body owns until its borrowed `RBrace` |
| `%` format reaches EOF or fence boundary before `{` | emit percent/format text, `Missing(StringInterpolationOpenBrace)`, finish interpolation; do not consume sentinel | StringTerminator Missing returns the exact pending boundary |

The maximal malformed-unicode run performs the same physical-line judge before
every next-line byte. A body prefix accepted during that run belongs to its
single Error Item. Thus even a malformed escape cannot swallow a fence line.

The interpolation body receives an explicit `RBrace` stop. On success it
returns the exact unconsumed `Item { Payload::Token(RBrace), leading }`. The
interpolation owner emits its leading trivia in the interpolation, retags only
the accepted payload as `StringInterpolationCloseBrace`, and scans no generic
trivia after it. Bytes after `}` are therefore the next string lexical Item,
not trailing trivia of the close. If the Gate-6 virtual-statement child has an
unfinished statement/declaration at `}` or at EOF/fence, it first emits only
that child's own local Error/Missing and returns the same stop Item. The
interpolation owner then emits `Missing(StringInterpolationCloseBrace)` only
for EOF/fence; StringLiteral next emits `Missing(StringTerminator)` and returns
that same pending Item. Thus child recovery precedes interpolation close,
literal terminator, and Yumark recovery. A malformed child cannot consume this
`}` or a fence boundary.

### 4.2 Rule slots

| source at the current slot | committed result | input returned |
| --- | --- | --- |
| exact `rule` followed by `RuleIntroducerTrivia` then `{` | accept `RuleKw` and begin `RuleBody` | rule body owns its matching close |
| `rule` not followed by `RuleIntroducerTrivia` then `{` | this is not a RuleExpression acceptance; ordinary identifier/dynamic-operator classification decides it | no literal/rule recovery is emitted |
| RuleBody/RuleParen separator followed by its close | valid trailing separator; no Missing | matching close is consumed by its owner |
| RuleBody/RuleParen adjacent separators | valid empty RuleAlternative; no Missing | both separators are consumed by the enclosing alternative owner in source order |
| RuleBody/RuleParen missing matching close at EOF/fence/outer close | `Missing(RuleBodyCloseBrace)` or `Missing(RuleParenClose)` | exact caller boundary unchanged |
| RuleSequence sees a non-start, non-stop Item | one `Error(RuleUnexpectedItem)` around exactly that Item | continue the same RuleSequence |
| `=` without a RuleItem before a DSL close/outer boundary | `Missing(RuleCaptureRightItem)` | close/boundary unchanged |
| `.`/`::` followed by a caller stop, EOF, or fence boundary | `Missing(RuleFieldName)` / `Missing(RulePathName)` | exact stop/boundary unchanged |
| `.`/`::` followed by a non-identifier ordinary Item | one Error around that one Item as the malformed name; no additional Missing | continue the same RuleItem after the Error |
| `*`, `+`, `?`, `*?`, or `+?` | emit one `RuleQuantifier` containing that token | continue RuleItem |
| RuleLiteral ordinary terminator | emit `RuleLiteralEnd` | scan literal successor normally |
| RuleLiteral EOF/fence boundary | `Missing(RuleLiteralTerminator)` | exact pending boundary unchanged |
| RuleLiteral interpolation matching `}` | retag/emit it as `RuleLiteralCloseBrace` | resume RuleLiteral |
| RuleLiteral interpolation reaches outer literal terminator at a returned RuleSequence item boundary | `Missing(RuleLiteralInterpolationCloseBrace)`; do not consume quote | outer RuleLiteral accepts the same quote |
| RuleLiteral interpolation reaches EOF/fence boundary | `Missing(RuleLiteralInterpolationCloseBrace)` then `Missing(RuleLiteralTerminator)` | exact pending boundary unchanged |
| `:` followed by non-`xidc`, quote, EOF, or fence boundary | `Missing(RuleLazyCaptureName)`; do not consume sentinel | RuleLiteral owns preserved quote/boundary |
| `:{` reaches `}` | emit close, including valid empty content | resume RuleLiteral |
| `:{` reaches EOF/fence before `}` | `Missing(RuleLazyCaptureCloseBrace)`; do not consume sentinel | RuleLiteral owns preserved boundary |

`RuleSequence` receives caller stops explicitly. Under `RuleBody` they are its
`}`, `|`, and newline separator; under `RuleParenBody` they are `)`, `|`,
comma, and newline; under `RuleLiteralInterpolation` they are its `}` plus the
outer literal's quote at an item boundary. It never consumes any of those
stops as a RuleAtom. `RuleCall` and `RuleIndex` delegate only their delimited
ordinary-expression interior to the exact `ExpressionList` owner in §2; the
Rule tail owns their opener and node, and that list owner owns the matching
close and its `ExpressionListItem`/`ExpressionListClose` recovery. In a
Pattern, the same rule owners use Pattern's outer tail/boundary frame, not
expression dispatch.

At a shared Yumark boundary, the complete recovery order is innermost literal
slot(s), then literal terminator, then the outer Yumark fence Missing. The
literal and RuleSequence never emit the pending Item's leading trivia; Yumark
owns it after handoff.

## 5. Fence-aware line transitions

Every literal scanner operation that can pass a physical line terminator uses
one shared literal line-transition primitive. This includes ordinary text,
format text, lazy-capture text, Unicode Error runs, and escaped LF/CRLF. After
consuming LF or CRLF, before reading the next physical byte, it calls
`judge_fence_line`.

For a `Body` decision with a prefix, it records exactly one prefix split in the
current lexical Item, consumes that prefix, and continues. If the next ordinary
literal token begins immediately after the prefix, that token is the current
Item and owns the prefix physically; a preceding finished token never receives
an appended carrier. Strict close is always tested before prefix recording. A
close, reduced-depth, greater-depth, non-prefix, explicit-quote, or physical
EOF returns the corresponding pending Item untouched.

Required direct controls include normal/heredoc/rule text, format text,
lazy-capture text, Unicode malformed text, and a backslash-at-EOL whose next
physical line is respectively body, close, and every transition. Format
controls specifically include a quote and a CRLF before its first `{`, plus
EOF/fence before `{`; braced-capture controls include `:{x=y}`, an embedded
quote, and a CRLF before `}`. Each family must prove CRLF/UTF-8 offsets, exact
suffix pointer/Item identity, one prefix record per accepted prefix, unsplit
no-carrier behavior, physical source-order emission with `YmQuotePrefix`, and
absence of a Yulang string/rule color for the prefix.

## 6. Direct dispatch and staged construction

Expression NUD recognizes only adjacent `~"` before dynamic operator lookup:

```text
~"x"  -> RuleLiteral
~a     -> ordinary table-driven `~`
~ "x" -> ordinary table-driven `~` followed by its ordinary operand path
```

`rule` is recognized only as the exact contextual word `rule`, never `rulex`,
`rule?`, or `rule!`. Its contextual route receives the un-emitted ordinary
word Item, then completes exactly one successor Item. That successor owns all
intervening `RuleIntroducerTrivia` as its leading trivia and its one payload.
If that payload is `{`, the route moves the first Item as `RuleKw` and the
successor as the RuleBody opener into one committed RuleExpression. Otherwise
it emits neither Item as a rule construct and returns the unchanged successor
to ordinary expression-tail handling, where the first Item is an ordinary
identifier. This includes successor EOF/fence boundaries. There is no raw
source probe, trivia-spanning rewind, rescan, clone, or retained Item vector:
the existing one-successor Item reader performs all fence-aware trivia
classification exactly once. Ordinary host operator rules remain untouched
outside that accepted contextual form. `StringLiteral`, `RuleLiteral`, and
`RuleExpression` return to the ordinary expression tail protocol only after
their own owner completes.

Pattern dispatch is a later direct Pattern gate:

```text
one-quote Pattern opener -> RuleLiteral without `~`
three-or-more quote run  -> StringLiteral
contextual `rule` + `{`  -> RuleExpression
```

The Pattern routes share literal/rule interior owners but not expression NUD
or tail dispatch. They require their own ordinary, multiline-fence, tail, and
boundary controls.

| gate | isolated construction | prerequisite and evidence |
| --- | --- | --- |
| L0 | append public `SyntaxKind` vocabulary and literal-private fragmented emitter | old discriminants unchanged, Rowan round trip, all existing Item emitters unchanged |
| L1 | literal lexical Item scanner and fence transition primitive, with no NUD dispatch | complete `LiteralPiece`/fragment/boundary topology, 1/3/4 quote and exact-close matrix, LF/CRLF/UTF-8, all transition controls |
| L2 | normal/heredoc text, escapes, terminator, and all non-interpolation §4.1 recovery | closed/EOF/fence/tail continuation and no speculative emission; `%` is a construction stop, not a claim that valid interpolation is complete |
| L3 | StringInterpolation percent/format/open-brace construction and its missing-open-brace path | raw-through-quote format, EOF/fence format boundary, escaped-line fences, borrowed `}` witness with an injected child Item; no full child grammar claim |
| L4 | isolated `RuleSequenceCore` witness: RuleIdentifier/SigilIdentifier/integer/`..`, RuleParenBody, quantifier, capture, field, and path only | `rule\n{}`, `rule /*…*/ {}`, empty/trailing/double separators, stop-keyword controls, active lazy quantifiers, terminal-capture, field/path recovery, and multiline lexical controls. Its explicit non-core successors (`StringLiteral`, `[` atom, `(` tail, `[` tail) return their exact unconsumed Item to the witness harness; no RuleExpression production entry exists at L4 |
| L5 | add RuleAtom string/bracket and Rule call/index through the Gate-4 direct expression/list checkpoint; add Pattern literal construction witnesses through the Gate-5 Pattern checkpoint | bracket/call close, ExpressionList recovery, one-quote Pattern `RuleLiteralStart`, and all non-interpolation cases; a nested StringInterpolation remains deferred |
| L6 | VirtualStatementBlock and all StringInterpolation-reachable literal positions | only after the Gate-6 root statement/declaration construction checkpoint; child error, separator, borrowed `}`, and fence propagation |
| L7 | complete literal delta closure, including RuleAtom `StringLiteral` and Pattern literal routes | after L6; direct expression/pattern delta ledgers, all nested literal/fence matrices, and no legacy/direct crossing |
| Gate 4 | expression-owner construction checkpoint plus isolated literal witnesses L0--L3 | it must not claim `%{ Statement* }` or a fully closed StringLiteral before L6 |
| Gate 5 | Pattern-owner construction checkpoint plus isolated Pattern witnesses | it must not claim a complete Pattern literal/rule route before L7 |
| Gates 4--6 barrier | joint certification of the three owner closures after L7 | closes the previously open literal E/RB-E and P/RB-P delta rows together; no earlier gate completion claim |

L0 changes a public enum but not parsing reachability; it is not described as
private vocabulary. All other gates are isolated construction checkpoints until
the joint barrier. The existing recursive-rewrite Gate-4 E and RB-E rows that
cover strings are **blocked by L6**, not direct-owner-unreachable: their source
language permits interpolation, and a complete virtual body needs the Gate-6
statement/declaration construction checkpoint. Likewise the Pattern P/RB-P
literal rows are blocked by L7. The plan therefore records owner-side
construction at Gates 4--6, leaves these rows open, and closes their literal
deltas together only at the post-L7 barrier. This is a dependency correction,
not permission to call any of Gates 4--6 complete out of order. Focused direct
tests and `cargo check -p yu-syntax` are sufficient per isolated gate; no
workspace-wide suite follows. No legacy opaque/header scanner is changed.

## 7. Decisions required for Authoritative status

| id | approved decision | rejected alternative and consequence |
| --- | --- | --- |
| LC-1 | heredoc terminator is an exact whole quote run | retain opaque at-least-`n` behavior; then 3-open/4-run closes and leaves one quote for later parsing |
| LC-2 | adopt the full-word public CST vocabulary in §3, including `RuleLiteralStart` for one-quote Pattern literals and dedicated Rule tail nodes | use Yulang2 abbreviations/generic tail nodes or its Pattern `StringStart`; consumers see a less uniform public tree |
| LC-3 | use the §4 local slot table: zero-width Missing, exactly designated Error extent, and literal recovery before fence recovery | retain silent legacy EOF behavior; unclosed literals lose typed CST recovery and fence ordering evidence |
| LC-4 | reserve only adjacent `~"` before dynamic operator lookup | reserve all `~` or table-drive the literal spelling; either changes `~a`/`~ "x"` or makes lexical ownership mutable |
| LC-5 | Pattern one-quote -> RuleLiteral, 3+ -> StringLiteral, and Pattern `rule {}` -> RuleExpression | make all Pattern quotes StringLiteral or omit Pattern `rule`; the selected route is a new decision, not a claimed verified current-spec behavior |
| LC-6 | use the separate Rule DSL in §2: epsilon alternatives, `|`/newline and paren comma separators, terminal `=`, the stated atom set with `do`/`if`/`else`/`case`/`catch`/`rule` excluded as RuleAtoms, no host operators/ML application, and Gate-4-owned ordinary argument lists | use host Pratt grammar or accept the six stop words as RuleAtoms; the former leaks dynamic operators/ML application, the latter changes rule-boundary behavior and recovery |
| LC-7 | keep `*?` and `+?` as active lazy quantifiers with one `RuleQuantifier` CST node | reject them as Error-wrapped inactive spellings; this intentionally breaks existing Yulang2 rule programs and CST |
| LC-8 | accept contextual `rule` only when exact `rule RuleIntroducerTrivia {` is present, including a newline or comment before `{`; otherwise leave the word to ordinary classification | require same-line horizontal trivia or commit bare `rule` as a keyword; the former rejects legacy multiline forms, the latter reserves bare `rule` and adds a Missing `{` |
| LC-9 | StringInterpolation owns the explicit virtual `Statement*` body and borrowed `}` | restrict interpolation to an expression; this removes declaration/separator forms and needs a different recovery/CST contract |
| LC-10 | FormatText is raw through quotes, escapes, LF, and CRLF until `{`, with only EOF/fence as a missing-open sentinel | make the enclosing string terminator a sentinel; then `%format "text"` closes/recoveries before `{`, unlike the old opaque and Yulang2 scanner |
| LC-11 | braced lazy capture `:{...}` is empty-capable raw text through `=`, quotes, LF, and CRLF until `}` | use the Yulang2 scanner rule: nonempty capture text stops before `=` but quotes/LF/CRLF remain capture text; `:{x=y}` closes the capture node without its `}`, then the outer literal owns `=y}` as text, while `:{"}` and `:{a\r\nb}` keep their quote/multiline text in the capture. Quote- or newline-sentinel variants are rejected because they give the outer literal recovery ownership before the capture's `}` |
| LC-12 | preserve the migration-compatible escaped-CRLF CST split: one `StringEscape` Item contains `StringEscapeLead "\\"` then `StringEscapeSimple "\r"`; the next Item is `StringText "\n..."` | make CRLF one escaped-line token; that is more atomic but changes the public token grouping from Yulang2 |

The approved package is LC-1 through LC-12. The two-quote empty normal
string and normal-string newlines are already fixed; neither is offered as a
new decision.

## 8. Review and stop conditions

Independent review verified the quote-run table, §4 safe sentinels, literal
Item/carrier boundary proof, virtual-statement prerequisite, Rule DSL
grammar/CST/recovery, Pattern routing, dynamic `~`/`rule` collisions, public
`SyntaxKind` stability, and raw/non-Yulang fence non-reachability.

Return to design if any implementation requires a compound literal-plus-
boundary payload, a carrier appended to a completed Item, retained
source/cursor/literal/fence state, a body/event buffer, source replay, a
second builder, an opaque/legacy bridge, fence-boundary consumption, or
non-linear byte work. Static cost remains `O(bytes + structural work)` with
storage bounded by structural nesting plus the largest pending segmented
lexical Item. No timing is needed unless that static bound becomes uncertain.
