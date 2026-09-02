# Authoritative: standalone doc-comment declaration and structured Yumark

Status: Authoritative

Approved-by: user

Approved-at: 2026-09-01

Reviewed-by: independent spec, compiler/recovery, and performance reviewers on
2026-09-01; the final design re-entry closed command promotion, `my` head/body
ownership, and embedded-delimiter recovery.

Scope: declaration-level doc-comment syntax, neutral structured Yumark grammar,
AST/direct-CST/recovery, and canonical Statement/root dispatch in `yu-syntax`.

User direction: on 2026-09-01, select a complete structured Yumark grammar,
including its documented command language, rather than an opaque temporary
body; make a block-document closing `---` strict; treat the written Yumark
draft, frozen in this repository as
`notes/design/oracles/2026-09-01-yumark-draft.md` from
`yulang-private-old` commit `5a087d34c199fb09a95a107090413d4549085b96`, as
the surface authority instead of its incomplete legacy parser; use an explicit
Yumark frame stack with no artificial nesting-depth limit; and define `do` as
capture of the block items following the paragraph containing its command,
distinct from that command's optional colon/brace body. The user also selects
the §10 completion rows: a line-start block-doc opener; parent return for list
middle indentation; raw single-line link/image destinations; Missing image
destination; sole `do` argument; inline-reference semicolon; blank-line-tolerant
if chains; opener-column fence/explicit-quote close; and valid empty heading.
`\use UseTree;` is an allowed existing-tree form, while parenthesized `\use`
remains written-surface syntax. `\my f x` is accepted through a Yumark binding
head: `=` owns an expression body and `:` is the indented shorthand for its
braced document body.

Authority basis: `docs/yulang3-architecture.md` §4.2; the Authoritative
`notes/design/2026-08-20-yu-syntax-chasa-architecture.md` declaration,
trivia, Yumark, recovery, and direct-CST sections; and the declaration-
companion addendum's explicit doc-comment exclusion. This document is
implementation authority for its declared scope.

## 1. Oracle and scope

Yumark is an embedded document language. A doc comment is neither ordinary
trivia nor opaque text: it is a standalone declaration whose body is a
structured Yumark document. This parser preserves syntax only. It never
attaches the document to a following declaration and does not implement
rendering, hover, doctests, HIR, resolver, formatter, evaluation, or
documentation association.

The written Yumark draft is the syntax oracle. The old Yulang2 parser is an
operational reference only: it may supply scanner examples and fixtures, but an
omitted or incompatible legacy implementation never narrows the written
surface.

| written surface | Y3 disposition |
| --- | --- |
| headings, implicit/explicit sections, lists, both quote forms | preserved |
| paragraphs, blank lines, emphasis/strong, groups, links, images, applies | preserved |
| references, Yulang arguments, colon/brace bodies, `do`, `my`, `use`, if chain | preserved as syntax only |
| raw fenced code | preserved as raw source, never expanded |
| legacy contiguous `--` lines | deliberately diverged: one line document ends at its newline |
| legacy prefix `---x` close and silent EOF/generic invalid recovery | deliberately diverged: strict close plus typed Y3 recovery |
| quoted/block Yumark literals elsewhere in Yulang | retain their existing opaque lexical-region behavior |

This slice excludes field-doc items, semantic attachment, Markdown/CommonMark
beyond the written surface, custom control syntax, public `parse_file`
recursion, parsed-Yulang fences, dynamic operator-table construction, CST
replay/cache, and all non-parser semantics. A `yulang` fence remains raw:
Yulang appears only in command/apply argument positions.

### 1.1 Lexical conventions

`H` is zero or more ASCII space or horizontal-tab bytes. `PhysicalNewline` is
one LF byte, or the CRLF pair when both bytes are present; it is one physical
line boundary. `LineStart` is source start or the byte immediately after a
physical newline. `indent_col` is the existing `yu-syntax` physical-line
column measured by the shared indentation scanner; Yumark neither expands nor
redefines tabs. A strict marker's `H* (PhysicalNewline | EOF)` suffix is a
lookahead condition, not part of that marker's committed range.

## 2. Envelope and dispatch

`DocCommentDeclaration` is a separate canonical `Statement` and root
`Declaration`. It is never a child of `TypeDeclaration`,
`StructDeclaration`, or a following declaration. An orphan document is valid.

```text
Declaration ::= ... | DocCommentDeclaration
Statement   ::= ... | DocCommentDeclaration

DocCommentDeclaration ::= LineDocComment | BlockDocComment
LineDocComment        ::= "--" InlineDocument(LineDocMode)
BlockDocComment       ::= "---" H* PhysicalNewline
                          BlockDocument(BlockDocMode)
                          RecoveredBlockDocClose
RecoveredBlockDocClose ::= BlockDocClose
                          | Missing(DocComment, ClosingDelimiter)
BlockDocClose         ::= LineStart "---" H* (PhysicalNewline | EOF)
```

`BlockDocComment`'s opener is also `LineStart "---" H* PhysicalNewline`; the
short grammar display relies on the §1.1 convention. It cannot begin after a
same-line semicolon or other statement text. Both document markers commit only
their three-byte spelling. The block-close suffix belongs to the enclosing
statement sequence, never to the just-finished document.

The marker judge is sink-free, input/local-state neutral, and longest-first:
`---` wins over `--` at canonical Statement start. It runs after caller-owned
leading trivia and before a dynamic operator of the same spelling only there.
An expression NUD/LED or another non-statement position retains the existing
operator path. A root-leading doc declaration becomes `FirstNonHeader`.

Atomic promotion updates the closed declaration sum in root AST/direct,
canonical Statement AST/direct, candidate/intro classifiers, `StatementKind`,
header projection, AST/recovery/SyntaxKind vocabulary, and all root/braced/
indented/inline dispatch tests. No field-list or owner-specific sequence gains
a doc-only path.

## 3. Envelope boundaries

A line doc owns `--` and inline Yumark up to, but never including, its first
physical newline or EOF. The newline is outer statement-sequence trivia. A
later `--` starts a new declaration. Empty `--` is valid.

A block doc close is recognized only when it is after the opening line, at
physical line start, at the opening base column, spelled exactly `---`, and
followed only by horizontal trivia then newline/EOF. `---x`, `----`,
differently-indented markers, and a marker on the opening line are document
text. The close commits its three marker bytes only; its suffix belongs to the
outer statement sequence. EOF emits exactly one zero-width
`Missing(DocComment, ClosingDelimiter)` at EOF.

## 4. One iterative grammar

`grammar/yumark/` is one neutral AST/direct decision driver with output
adapters, not two grammars. It uses an explicit `Vec<YumarkFrame>` work stack,
not Rust recursion through Yumark. It has no artificial depth limit: each
nested document, section, list, quote, group, body, or argument pushes a frame
and pops at its own boundary. Memory grows with actual nesting and normal
process resources, not a language-defined cap.

```text
YumarkFrame ::= Document(base, envelope-stop)
              | Inline(owner, close)
              | ImplicitSection(level)
              | ExplicitSection(level, parent-indent, body-indent)
              | List(indent)
              | ListItem(marker, indent, content-column)
              | ExplicitQuote(depth, marker)
              | PrefixQuote(depth)
              | RawFence(marker, indent)
              | BracedBody(owner)
              | IndentedBody(owner, parent-indent, body-indent)
              | DoCapture(command-start, indent)
              | IfChain(indent, seen-else)
              | EmbeddedYulang(owner, outer-kind, delimiter-floor)
```

Frames retain only source positions/layout/terminators/checkpoints: no copied
text, replay events, character index, or per-document parse buffer. Text,
fence body, link destination, marker payload, and trivia are source ranges or
tokens. AST vectors exist only for documented structural children.

Every structural probe checkpoints input, ErrorSink, line state, Yumark frames,
lexical mode, delimiter/stop frames, indentation, ambient owner, and
diagnostic/recovery identity. It rolls all back unless it commits its node or
recovery. A Yumark-frame checkpoint is O(1): stack length plus an undo-log
watermark, never `Vec<YumarkFrame>::clone`. A frame mutates only after commit,
or records its prior top-frame value in that same undo log; rollback restores
both watermarks before other ParseLocal state.

The shared chunk judge has source range, line-start/indent/quote/blank facts,
text through the next boundary, and one NUD. Order is:

1. active frame/envelope terminator, then EOF;
2. blank line, then physical newline;
3. line-start section close, heading, ordered list, unordered list, raw fence,
   explicit quote, prefix quote;
4. `![` and `**`;
5. `\`, `[`, `*`;
6. maximal raw text.

`#.` precedes heading, `**` precedes `*`, `![` precedes `[`, decimal list
precedes raw text, and explicit quote precedes prefix quote. Heading/list
markers require their documented ASCII space. A lone `\` and `_` are text.
`]`/`}` stop only an active matching frame.

## 5. Block and inline surface

```text
BlockDocument  ::= BlockItem*
BlockItem      ::= Section | List | ExplicitQuote | PrefixQuote | CodeFence
                 | CommandBlock | Paragraph | BlankLine
InlineDocument ::= InlineItem*
InlineItem     ::= Text | InlineGroup | InlineLink | InlineImage | InlineApply
                 | InlineReference | Emphasis | Strong
```

### 5.1 Sections

At line start, `#`+ plus one ASCII space starts a heading and its hash count is
the level. `#`+`.` is a close at that level. A heading without `:` opens an
implicit section, ending before a lower-or-equal heading or matching explicit
close. A heading followed by `:` requires horizontal trivia, newline, then a
strictly deeper body; it opens an explicit section.

The heading-tail judge runs only after its inline title completes. It splits a
colon from raw title text only when that colon is the final title byte before
`H* PhysicalNewline`; a group/apply colon or any non-terminal colon remains
inline text.

| input | result |
| --- | --- |
| heading level `L` after active levels `>= L` | close those implicit sections, open `L` |
| heading level `L` after top level `< L` | open nested implicit section; skipped levels allowed |
| heading `L` below/equal an explicit section level | close inner sections and that explicit section; return the heading unconsumed to its parent |
| matching close `L` for either active section kind | close deeper sections, emit close, close `L` |
| unmatched close | marker-sized `Error(Section, SectionClose)`; no unrelated pop |
| explicit-body dedent | close inner implicit sections, then explicit section |
| EOF/envelope close in implicit section | normal close, no Missing |
| accepted explicit colon without body | `Missing(Section, Body)` |

### 5.2 Lists

List markers are `-` plus one ASCII space or ASCII digits plus `.` plus one
ASCII space. A list item stores raw marker range, `indent_col`, and
`content_col`.

| next nonblank line | result |
| --- | --- |
| column below `indent_col` | close item/list; return line to parent |
| marker at `indent_col` | sibling item |
| marker at/after `content_col` | child list |
| non-marker at/after `content_col` | continuation |
| blank line | item-internal paragraph separator |
| non-marker in `indent_col <= col < content_col` | close item/list and return line to parent |

Equal-indent sibling recognition precedes the child-marker rule. The first
non-owned line is returned without consumption.

### 5.3 Quotes and paragraphs

An explicit quote marker is a marker-only line-start run of at least three
`>` bytes at its frame base column, followed by horizontal trivia and
newline/EOF. A run with following content is always a prefix quote, even at
depth three or higher. Inside an explicit quote, the exact active width closes;
any different marker-only width opens a nested explicit quote. This preserves
the written `>>>>` outer / `>>>` inner example. EOF emits
`Missing(Quote, ClosingDelimiter)`.

A prefix quote starts with one or more `>` at line start, preserving optional
or interspersed horizontal space. Exact depth continues; greater depth nests;
reduced depth ends frames without consuming the line; blank unprefixed line
ends the quote. Explicit and prefix forms never convert; a mixed form is
`Error(Quote, QuoteForm)`.

An explicit quote close commits its marker only. Its following horizontal
trivia and physical newline are direct trivia/token children of the immediately
containing `YmDoc`, after the just-closed quote node; they never become children
of that quote or a synthetic paragraph. The same rule applies to an inner quote
close, whose suffix belongs to its enclosing quote's `YmDoc`. A mixed-form
`QuoteForm` Error covers only the offending marker; following content and the
newline remain owned by the active parent document.

A paragraph owns a newline only when the next line remains in the block and is
not a block starter/terminator. Blank line, dedent/list transition, section,
quote, fence, command, document close, or parent terminator ends it.

### 5.4 Inline syntax

`*...*` and `**...**` own an `InlineDocument`. `[doc]` is an
`YmInlineGroup`; adjacent `(dest)` makes `YmInlineLink`; adjacent
`![doc](src)` makes `YmInlineImage`; adjacent `:ident` with optional Yulang
arguments makes `YmInlineApply`. After completing a group, choose `(`, then
`:`, then no tail. Newlines are allowed inside a group; blank lines terminate
the group before a block begins. A link/image destination is raw, same-line
source from its opening `(` through the first `)`; it has no escape or nesting
rule. `![doc]` without an immediately adjacent destination commits image form
and emits `Missing(InlineImage, Destination)` at the end of its `]`.

`\ident`, `\ident;`, and `\ident(args)` are `YmInlineRef`. The semicolon
terminates the name. Arguments use current canonical Yulang expressions, the
inherited immutable operator table, and a local delimiter stop—never a public
parse recursion.

## 6. Commands and do capture

Commands are syntax only. Resolving names/imports/bindings, Doc expansion, and
condition evaluation is out of scope.

```text
YulangArguments ::= "(" CanonicalYulangCallArguments ")"
BracedDocBody  ::= "{" BlockDocument "}"
IndentedDocBody ::= ":" H* PhysicalNewline StrictlyDeeperBlockDocument
DocBody        ::= BracedDocBody | IndentedDocBody

CommandBlock   ::= BlockGeneralCommand | MyCommand | UseCommand | IfChain
BlockGeneralCommand ::= "\" Identifier ImmediateBlockTail
                      | "\" Identifier YulangArguments PromotingBlockTail
ImmediateBlockTail ::= DocArgument CommandArgument* [DocBody]
                     | DoCapture [DocBody]
                     | DocBody
PromotingBlockTail ::= DocArgument CommandArgument* [DocBody]
                     | DocBody
CommandArgument ::= YulangArguments | DocArgument
DocArgument     ::= "[" InlineDocument "]"
DoCapture      ::= "(" "do" ")"

YumarkBindingHead ::= Pattern
                      (H+ NonBracedHeadPattern
                       | "(" Pattern ("," Pattern)* ")")*
NonBracedHeadPattern ::= canonical Pattern whose first nontrivia byte is not "{"
MyExpressionBody ::= "=" H* InlineYulangExpression H* RecoveredMySemicolon
                   | "=" H* PhysicalNewline StrictlyDeeperYulangExpression
MyCommand       ::= "\my" H+ YumarkBindingHead H*
                    (MyExpressionBody | BracedDocBody | IndentedDocBody)
                  | "\my" H* "(" YumarkBindingHead ")" H*
                    (MyExpressionBody | BracedDocBody | IndentedDocBody)
UseCommand      ::= "\use" "(" UseTree ")"
                   | "\use" H+ UseTree ";"
IfChain        ::= IfBranch ElsifBranch* ElseBranch?
IfBranch       ::= "\if" "(" RequiredYulangExpression ")" DocBody
ElsifBranch    ::= "\elsif" "(" RequiredYulangExpression ")" DocBody
ElseBranch     ::= "\else" DocBody
```

`YumarkBindingHead` is a Yumark-local structural head: its first atom and each
space-separated atom are existing canonical `Pattern`s; a parenthesized comma
list is a function-head argument group. It accepts both written
`\my(warning(x))` and user-selected bare `\my f x`. It is not a global Pattern
application feature and never changes ordinary binding declarations. The bare
form requires `H+` after `\my`; the parenthesized form permits both `\my(...)`
and `\my (...)`. Its `MyHeadBoundary` is active only at the Yumark delimiter
floor: a completed head yields top-level `=`, strict `:` plus `H*` newline, or
`{` unconsumed to `MyCommand`; a parenthesized-head `)` is the Yumark wrapper's
close. The same bytes inside a nested canonical Pattern delimiter remain owned
by that Pattern. After a completed head, the parser checkpoints horizontal
trivia and tests a braced/strict-colon/equality body before another bare Pattern;
thus `\my f { body }` always starts a braced document body. A brace-start
Pattern parameter remains available only in the explicit parenthesized
parameter group. A physical newline after `=` selects the indented-expression
form; only the inline equality form owns a required semicolon.

At a block-document line start, a general `\ident` becomes
`BlockGeneralCommand` only for immediately observable block evidence: an
immediate `[` DocArgument, a contextual `do` candidate, `{`, a strict colon body
introducer, or one already parsed ordinary `YulangArguments` immediately followed
by `[`, `{`, or that strict colon. The contextual candidate begins exactly
`(do` where `do` is a maximal word and its next byte is `)`, horizontal
trivia, comma, or a Yumark hard boundary. It commits the block form for
recovery, but enables sibling capture only for exact complete `(do)`; `(domain)`
and `( do )` remain ordinary Yulang arguments. `\ident`, `\ident;`, and
`\ident(args);` are all
`YmInlineRef`, exactly as in the written surface. Arbitrarily many leading
Yulang arguments are not probed to seek a later body. The line-start adapter
parses at most that first ordinary argument once under an output checkpoint,
then wraps its committed prefix as `YmInlineRef` or `YmCommand`; direct CST
uses `start_node_at`, never replay or source rescan. Once block evidence has
committed the form, later source-ordered `YulangArguments` and `DocArgument`s
are parsed once as command arguments. Inline positions never promote. Exact
builtin spellings `my`, `use`, `if`, `elsif`, and `else` select their builtin
parser first. `my`/`use` are never general-reference fallbacks. A general local
body is braced or indented, not both. `if`/`elsif` require conditions while
`else` rejects one. A same-level blank line does not break an immediately
preceding if-chain; the first nonblank sibling does. Orphan `elsif`/`else`
retains its builtin node/body and emits one marker-plus-head `Error(IfChain,
BranchPredecessor)`.

`do` is a separate capture argument:

1. a command-argument classifier recognizes the bounded contextual
   `DoCapture` candidate before canonical Yulang arguments. Exact `(do)`
   is accepted only when it is the entire parenthesized payload; mixed
   ordinary-Yulang-plus-`do` input is one `Error(DoCapture, Arguments)` and
   does not start capture. The malformed candidate rows in §9 retain the same
   block form but likewise disable capture. Otherwise it accepts source-ordered
   `(...)` Yulang arguments and `[...]` Yumark document arguments; a
   `{...}` form is a local body, never a document argument;
2. `\cmd(do)` completes its containing command paragraph/block item, including
   optional local `:` or `{...}` body, before capture begins;
3. the `DoCapture` owns subsequent sibling block items in the parent document;
4. it returns the parent's dedent, section/quote/fence/doc close, or EOF
   unconsumed;
5. a later `\other(do)` is inside the first capture and opens a nested capture;
6. local `:` and `{...}` bodies are permitted alongside `do` but remain
   mutually exclusive with each other.

Thus `\wrap(do):\n  local\nafter` has a local body and separately captures
the later `after` block. `\my f x = expr;` is inline expression syntax;
`\my f x =\n  expr` is indented expression syntax; and
`\my f x:\n  doc` is the indented shorthand for a braced document body.

## 6.1 Embedded Yulang delimiter ownership

Every `YulangArguments`, parenthesized `MyHead`, `MyExpressionBody`,
parenthesized `UseTree`, bare `UseTree` terminator, and `if`/`elsif`
condition uses one `YumarkEmbeddedBoundary { owner, outer_kind, floor,
hard_parent_boundaries, adapter_home }`. `outer_kind` is either a paired
Yumark delimiter or a required terminal separator. For a paired delimiter,
Yumark consumes/emits its opener, pushes a tagged delimiter frame, and records
that frame's depth as the floor. Canonical parsing may own lexical regions and
delimiters strictly above the floor, but at the floor its matching closer is a
Yumark stop. For an inline `my` expression or bare `use`, the wrapper instead
installs its required `;` as a terminal stop at the current delimiter depth.
Canonical parsing returns a paired closer, terminal separator, and every Yumark
hard boundary untouched. Yumark then consumes the present outer token and pops
its frame if any, or emits exactly one zero-width
`Missing(owner, ClosingDelimiter|Terminator)`; the canonical parser never emits
that outer-token record.

At the floor the shared bridge checks, in order: a canonical lexical/raw region;
a nested canonical delimiter above the floor; the matching borrowed Yumark
closer; a Yumark parent boundary (layout newline after classification, group or
body close, list sibling/dedent, quote/doc/fence close, or EOF); then ordinary
canonical candidates. A missing inner value and a missing Yumark outer close
are separate slots and may each emit one record. This bridge applies to general
and inline-reference arguments, My head/expression, UseTree, and If/Elsif
conditions. `DocArgument` follows the same outer-close protocol with an inner
Yumark inline frame instead of a canonical parser. Nested canonical delimiters
and lexical regions suspend the bridge only above its floor.

## 7. Raw code fences

A code fence is a line-start triple-U+0060 marker plus raw info text and a
newline; its close is the same triple-U+0060 marker at the opener's column,
followed only by horizontal trivia and newline/EOF. Its body is one lossless
raw text range. Brackets, braces, backslashes, commands, doc closes, quote
closes, and the word `yulang` have no structure inside. Only fence close/EOF
are active. Missing close emits `Missing(CodeFence, ClosingDelimiter)` at EOF,
then enclosing explicit-frame recovery rows occur inner-to-outer.

The opening marker is a fence only if its line has a physical newline; otherwise
its bytes are paragraph text. A close commits its marker only. Its horizontal
suffix and physical newline are direct trivia/token children of the parent
`YmDoc` frame, never of `YmCodeFence` and never a new paragraph. This gives
the close line one named CST home while preserving the parent document's next
block-start decision.

Fence discovery is in the one AST/direct-CST-producing Yumark pass. Calling
`scan_opaque_body`, `scan_raw_yumark_fence_body`, or
`scan_yulang_fence_body` over the body and then parsing it again is forbidden.
Existing opaque scanners are lexical precedents only; reuse may be a bounded
close predicate, never a full-body prepass.

## 8. AST, CST, and recovery vocabulary

```text
DocCommentDeclaration { form: Line | Block { close: Recovered<Range> }, document }
YumarkDocument { blocks }
YumarkBlock ::= BlankLine | Section | List | Quote | CodeFence | Paragraph | Command | IfChain
YumarkInline ::= Text | Group | Link | Image | Apply | Reference | Emphasis | Strong
YumarkCommand {
  range,
  promotion: GeneralCommandPromotion,
  arguments: Vec<CommandArgument>,
  local_body,
  do_capture: Option<Recovered<YumarkDoCapture>>,
}
YumarkCommandBody ::= BracedDoc | IndentedDoc
YumarkDoCapture { range, blocks }
YumarkMy {
  head_form: Bare | Parenthesized,
  head: Recovered<YumarkBindingHead>,
  body: InlineExpression { terminator } | IndentedExpression | BracedDoc | IndentedDoc,
}
YumarkUse { form: Parenthesized | Bare { terminator }, route: Recovered<UseTree> }
YumarkIfChain { branches: Vec<YumarkIfBranch>, else_branch }

GeneralCommandPromotion ::= ImmediateDocArgument | ImmediateDo | ImmediateBody
                          | YulangThenDocArgument | YulangThenBody
CommandArgument ::= Yulang { range } | Document { document, close }
```

CST preserves every written form. AST has a distinct surface-form field for
every listed alternative and retains every selected/recovered delimiter range;
it may not normalize a general command into an inline reference, a
parenthesized form into a bare form, argument kinds into one untyped list, or a
complete `do` into a malformed/noncapturing form. Direct CST streams nodes and
never builds/replays an AST.

| AST form | direct CST child order |
| --- | --- |
| document | recovered `YumarkBlock` values in source order, including `BlankLine` |
| implicit/explicit section | heading, implicit/explicit document body, then optional section-close marker |
| list item | marker then one `YmListItemBody` document |
| quote | opening/prefix marker, document, then recovered explicit close only for explicit form |
| raw fence | open marker, info, opening newline, raw text, recovered close marker; suffix lives in parent `YmDoc` |
| general command | command head/arguments, optional local `YmCommandBody`, optional `YmDoCapture`; its AST records `ImmediateDocArgument`, `ImmediateDo`, `ImmediateBody`, `YulangThenDocArgument`, or `YulangThenBody` |
| do capture | later sibling block items only, in source order; it is a child of its initiating command |
| my | `YmMyBindingHead`, then exactly one expression-body or doc-body node; AST records bare/parenthesized head and all four body forms |
| use | backslash/name, then parenthesized or bare `UseTree`, then required bare-form semicolon; AST records the selected form |
| if chain | `YmIf`, then zero or more `YmElsif`, then optional `YmElse`; each condition wrapper retains its recovered close |

| envelope/token kinds | structural node kinds |
| --- | --- |
| `DocCommentDeclaration`, `DocLinePrefix`, `DocBlockOpen`, `DocBlockClose` | `YmDoc`, `YmSection`, `YmImplicitSection`, `YmExplicitSection`, `YmHeading`, `YmSectionClose` |
| `YmText`, `YmHeadingMarker`, `YmListMarker`, `YmQuoteFenceMarker`, `YmQuotePrefix`, `YmFenceMarker` | `YmBlankLine`, `YmList`, `YmListItem`, `YmListItemBody`, `YmQuoteBlock`, `YmCodeFence`, `YmCodeFenceInfo`, `YmCodeFenceText`, `YmParagraph` |
| Yumark local punctuation/identifier tokens | `YmCommand`, `YmCommandArgs`, `YmCommandBody`, `YmDoCapture`, `YmMy`, `YmMyBindingHead`, `YmMyExpressionBody`, `YmUse`, `YmIfChain`, `YmIf`, `YmIfCondition`, `YmElsif`, `YmElsifCondition`, `YmElse` |
| `YmBackslash`, `YmBangLBracket`, `YmStrongMarker`, `YmEmphasisMarker` | `YmInlineRef`, `YmInlineGroup`, `YmInlineLink`, `YmInlineImage`, `YmInlineApply`, `YmInlineApplyHead`, `YmInlineApplyArgs`, `YmYulangArgs`, `YmDocArg`, `YmEmphasis`, `YmStrong` |

At root `DocCommentDeclaration` is one `Root` child. In a nested canonical
sequence it is the declaration child of existing `Statement` shape. All Yumark
nodes are descendants of that owner. Existing canonical Yulang CST appears
only below these closed adapter homes: `YmYulangArgs` for call arguments,
`YmInlineApplyArgs` for inline-apply arguments, `YmMyBindingHead` for
`Pattern`, `YmMyExpressionBody` for an `OperatorChain`, `YmUse` for `UseTree`,
and `YmIfCondition`/`YmElsifCondition` for conditions. It never opens a nested
public root, Statement, or declaration dispatch, and never appears in raw
fences, `YmDocArg`, or text nodes.

All recovery nodes remain generic `Missing`/`Error`. Typed identity is:

```text
GrammarRole::Yumark(YumarkRole { owner, slot })

YumarkOwner ::= DocComment | Section | List | ListItem | Quote | CodeFence
              | InlineGroup | InlineLink | InlineImage | InlineApply
              | InlineReference | Emphasis | Strong | Command | My | Use
              | DocArgument | DoCapture | IfChain | IfBranch | ElsifBranch
              | ElseBranch
YumarkSlot ::= Starter | Name | Head | Arguments | Condition | BodyIntroducer
              | Body | Destination | BranchPredecessor | ClosingDelimiter
             | SectionClose | QuoteForm | ExpressionBody | Route | Terminator
```

One committed record yields exactly one generic recovery node and diagnostic in
source order. AST/direct have equal recovery count/range/remainder and exact
ParseLocal restoration except documented committed diagnostic-id/lexical deltas.

## 9. Recovery table

`Missing` is zero-width. `Error` is non-empty and maximal only within its
active Yumark frame. Safe stops are newline, active close, block-doc close,
quote dequote/close, list sibling/dedent, fence close, command-body boundary,
or EOF. A frame returns a safe boundary unconsumed unless its row owns it.

| accepted owner and failure | one committed recovery | retained boundary / continuation |
| --- | --- | --- |
| `--` at EOF or before newline | valid line doc; no recovery | EOF/newline |
| block-doc opener without physical newline | no opener commit; bytes are paragraph/ordinary Statement text | current line |
| block doc EOF | `Missing(DocComment, ClosingDelimiter)` at EOF | EOF |
| raw fence EOF in block doc | `Missing(CodeFence, ClosingDelimiter)`, then doc Missing at same EOF, inner-to-outer | EOF |
| emphasis/strong/group missing matching close | `Missing(Emphasis|Strong|InlineGroup, ClosingDelimiter)` | active parent boundary |
| link/image `(` missing `)` | `Missing(InlineLink|InlineImage, ClosingDelimiter)`; raw destination stays owned | active parent boundary |
| committed image missing adjacent `(` | `Missing(InlineImage, Destination)` at image `]`.end | later text stays parent-owned |
| heading colon without newline/deeper body | `Missing(Section, Body)` | parent boundary |
| committed `:` body with nondeeper first line | `Missing(exact Command|My|If|Elsif|Else, Body)` | dedent/line returned |
| braced doc body missing `}` | `Missing(exact body owner, ClosingDelimiter)` | parent hard stop; empty `{}` is valid |
| general/reference or inline-apply Yulang `(` missing `)` | outer wrapper emits `Missing(Command|InlineReference|InlineApply, ClosingDelimiter)`; canonical payload emits no duplicate close | Yumark parent boundary unconsumed |
| `my` parenthesized head, `use(...)`, or `if`/`elsif` condition missing `)` | outer wrapper emits `Missing(My|Use|IfBranch|ElsifBranch, ClosingDelimiter)`; canonical payload emits no duplicate close | boundary unconsumed |
| committed `[` DocArgument missing `]` | `Missing(DocArgument, ClosingDelimiter)` at parent boundary/EOF | boundary unconsumed; command remains a command |
| malformed inner canonical expression/pattern/UseTree | its existing canonical record(s) only; Yumark wrapper adds no duplicate inner record | bridge returns parent hard stop |
| `\my` before any head | `Missing(My, Head)` | local boundary unconsumed |
| completed `\my` head with no `=`, braced body, or strict colon body | `Missing(My, BodyIntroducer)` | local boundary unconsumed |
| committed `\my ... =` without an expression | `Missing(My, ExpressionBody)` | Yumark body delimiter/boundary retained |
| completed inline `\my ... = expr` missing required `;` | `Missing(My, Terminator)` | newline/document boundary unconsumed |
| `if`/`elsif` immediate `)` | canonical required-expression parser emits its one missing condition; Yumark consumes `)` | no wrapper duplicate |
| completed `if`/`elsif` condition before parent boundary without `)` | `Missing(IfBranch|ElsifBranch, ClosingDelimiter)` | body/parent boundary unconsumed |
| `else` with condition | maximal `Error(Else, Condition)` over condition bytes | its body still parses |
| parenthesized `\use()` | `Missing(Use, Route)` before `)`; Yumark consumes `)` | no terminator required |
| parenthesized `\use(` at boundary/EOF | `Missing(Use, Route)`, then `Missing(Use, ClosingDelimiter)` | boundary unconsumed |
| parenthesized `\use(route` at boundary/EOF | `Missing(Use, ClosingDelimiter)`; inner route recovery remains canonical | boundary unconsumed |
| bare `\use ;` | `Missing(Use, Route)`; Yumark consumes `;` | following boundary unconsumed |
| bare `\use` immediately at line/document boundary | `Missing(Use, Route)` only | no speculative terminator cascade |
| completed bare `\use route` missing required `;` | `Missing(Use, Terminator)` | newline/document boundary unconsumed |
| bare malformed `\use` route before `;` | canonical recovery owns route bytes; Yumark consumes `;` | no duplicate route record |
| recovery-committed `(do` at line boundary/EOF | `Missing(DoCapture, ClosingDelimiter)`; capture disabled | boundary unconsumed |
| `(do H+ )` | `Error(DoCapture, Arguments)` over the nonempty horizontal trivia; Yumark consumes `)`; capture disabled | later blocks stay parent-owned |
| recovery-committed `(do H+` at hard boundary/EOF | `Error(DoCapture, Arguments)` over the nonempty horizontal trivia, then `Missing(DoCapture, ClosingDelimiter)`; capture disabled | boundary unconsumed |
| `(do x)` or `(do, x)` | one `Error(DoCapture, Arguments)` over unexpected interior; Yumark consumes its `)`; capture disabled | later blocks stay parent-owned |
| recovery-committed `(do x` or `(do, x` at hard boundary/EOF | `Error(DoCapture, Arguments)` over unexpected interior, then `Missing(DoCapture, ClosingDelimiter)`; capture disabled | boundary unconsumed |
| orphan `elsif`/`else` | one `Error(IfChain, BranchPredecessor)` over backslash plus builtin word; its committed body parses as that node's child | next block item |
| explicit quote EOF | `Missing(Quote, ClosingDelimiter)`, then outer explicit misses | EOF |
| list dedent/sibling or prefix dequote | no recovery | exact next line |
| malformed structural run | maximal frame-local Error; no cross-frame scan | first safe boundary |

Implicit sections, prefix quotes, and do captures close normally at parent
terminator. Explicit unclosed frames emit one Missing each from inner to outer.
No recovery invents/scans for a following declaration.

## 10. User-approved completion of written-spec gaps

The written source is non-total at these points. The following completions were
explicitly selected on 2026-09-01 and are part of this Draft's proposed final
surface, not deferred implementation choices.

| gap | approved completion |
| --- | --- |
| block-doc opener | line-start exact `--- H* PhysicalNewline`; no same-line/post-semicolon opener |
| list middle indentation `item.indent <= col < item.content` | close current item/list and return the line to parent |
| link/image destination | raw same-line bytes through first `)`; no escape/nesting |
| `![doc]` without destination | Image plus `Missing(InlineImage, Destination)` |
| `my` head | `YumarkBindingHead` in §6, including bare `\my f x` and parenthesized function-head groups |
| `my` body | `= expr;`, `= newline deeper-expr`, braced Doc, or `:` indented Doc; inline equality semicolon is mandatory |
| `use` | preserve `\use(UseTree)` and allow existing-tree `\use UseTree;` |
| `do` arguments | exact sole `(do)` only; no mix with ordinary Yulang arguments; local Doc body remains allowed |
| semicolon after `\ident(args)` | allowed only as the inline-reference lexical terminator; it never promotes a line-start invocation to a command |
| blank lines before `elsif`/`else` | do not break a same-level if-chain; a nonblank sibling does |
| explicit quote | marker-only `>{3,}` line; equal active width closes, any other width nests; content-bearing line is prefix quote |
| fence/explicit quote indentation | strict close at opener base column |
| empty heading title | valid |

## 11. Performance, gates, and approval

Every document/fence/command has one forward path:
`O(bytes + structural nodes + embedded Yulang argument work)` time and
`O(structural nesting)` frame memory. AST owns structural vectors; direct
streams CST without an AST mirror. Required static evidence: no opaque full-body
call/public-recursive parse; no duplicated AST/direct scanner; source-range raw
fence/text emission; and a deep nested section/list/quote/group/command
fixture. Timing is not justified unless implementation adds a materially
uncertain loop/allocation beyond this plan.

1. Add inert syntax/AST/recovery vocabulary and test-only full-state snapshot;
   no dispatch edge.
2. Add isolated marker/strict-close/line-doc/chunk/frame-stack judges with
   transaction tests; no dispatch edge.
3. Add isolated inline/paragraph/section/list/quote/raw-fence grammar and
   exact local recovery/state/CST tables.
4. Add isolated general/special command grammar, Yulang ownership, do/if-chain
   layout, and nested recovery table.
5. Add isolated doc declaration AST/direct adapters with losslessness,
   recovery-node/record identity, range/remainder, state restoration, and
   no-opaque-reparse evidence.
6. Atomically promote root/canonical Statement dispatch and prove marker-vs-
   operator priority, header stop, field nonreachability, and comment negatives.
7. Run compact public matrix for every form/recovery class/deep frame/direct
   topology/static performance ledger.

This is M3 new public grammar work. Independent review must cover written-spec
coverage and divergences; frame/terminator/recovery ownership and AST/direct
state; CST/dispatch/field boundaries; and single-pass/no-rescan evidence.
After all findings are adjudicated, the draft may become `Reviewed` and must
then return to the user for explicit `Authoritative` approval. No Rust
implementation begins beforehand.
