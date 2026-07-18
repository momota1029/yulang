# Yumark structural blank lines and line-doc continuation

Date: 2026-07-18

Status: **implemented and verified**. This note is the source of truth for the two
boundary-semantics changes below. The decisions were confirmed by the user on 2026-07-18 after
investigation of the parser, lowering, standard-library renderers, doc-comment association,
fixtures, and history. Section 5 preserves the pre-change characterization as historical evidence;
section 7 records the completed implementation.

The converged Yumark design remains historically intact. Its dated amendment cross-references this
note rather than silently rewriting the pre-amendment record.

## 1. The two mismatches

### 1.1 Ordinary blank lines currently render as content

The parser represents the blank source line in `first\n\nsecond` as `YmBlankLine`. Current
lowering turns that node into the public `blank_line` algebra operation. Consequently the blank
line is rendered in addition to the spacing already supplied by the two `paragraph` operations.
For the Markdown backend, the current production result is:

```text
source:   first\n\nsecond
current:  first\n\n\n\n\nsecond\n\n
target:   first\n\nsecond\n\n
```

This is an algebra-lowering artifact, not the desired distinction between paragraph continuation
and paragraph separation. By contrast, `first\nsecond` is one paragraph whose logical newline is
preserved within that paragraph.

### 1.2 Contiguous line docs currently parse as independent documents

Each physical `--` line currently parses as its own `DocCommentDecl` containing its own `YmDoc`.
The module map subsequently associates adjacent declarations as sibling `DocCommentUnit`s, and the
static renderer renders each sibling independently before concatenating the strings. Thus:

```text
-- first
-- second
```

currently renders as two paragraphs (`first\n\nsecond\n\n`) rather than one continued paragraph.
More importantly, inline syntax cannot span the physical boundary. For example:

```text
-- [link
-- here](add)
```

cannot parse `[link\nhere](add)` as one link because the first `YmDoc` has already ended before the
second line is parsed. Current incomplete-inline recovery also duplicates buffered text/trivia:
the CST text for this fixture becomes `-- [linklink\n\n-- here](add)...`, and the static renderer
produces `[linklink\n\n\nhere](add)\n\n`. Merging source fragments in the module map or rendering
layer would be too late to recover the syntax or the original bytes.

## 2. Approved source semantics

### 2.1 Paragraph continuation and separation

- Consecutive non-blank logical lines belong to one paragraph. Their logical newline remains part
  of that paragraph, as it does in an ordinary Yumark block literal today.
- An ordinary blank source line ends the preceding paragraph and permits the next paragraph to
  begin. It is a structural separator, not independently rendered content.
- Every parser-generated `YmBlankLine` is structural during lowering, regardless of position or
  multiplicity. This includes blank lines between paragraphs, leading and trailing blank lines,
  multiple consecutive blank lines, and blank lines inside quote structures.
- Lowering a parser-produced blank line emits no `blank_line`, `text`, or other algebra operation.
  Two paragraphs separated by source blank lines lower as two `paragraph` operations joined by
  ordinary `cons` only.
- The CST stays lossless and may retain `YmBlankLine` nodes. This change is in semantic lowering,
  not in the parser's representation of source trivia.

### 2.2 Contiguous `--` lines

- A contiguous run of line-doc source lines parses as one `DocCommentDecl` containing one logical
  `YmDoc`, not as one declaration per physical line.
- The opening `--` remains the document delimiter. Each later `--` in the run is a structural,
  lossless continuation-prefix token, analogous to a quote continuation prefix.
- A continuation prefix is separate from the logical newline. The parser therefore presents the
  body as ordinary consecutive Yumark lines, allowing paragraphs and inline constructs to cross a
  physical `--` boundary.
- Delimiter decoration is not logical document content. Its CST token nevertheless preserves the
  exact source bytes and ranges.
- An empty `--` continuation line contributes a logical blank line. It therefore separates
  paragraphs structurally under section 2.1, without producing a visible spacer operation.
- Both LF and CRLF remain lossless and denote one logical line boundary.
- A real blank source line terminates the contiguous line-doc run. A block doc delimiter (`---`)
  is not a line-doc continuation and keeps the existing non-stacking association rule.

The parser is the required implementation layer. Joining already-parsed sibling units in
`module_map` or in lazy-render input construction would leave cross-line inline syntax broken and
would duplicate parsing responsibility downstream.

## 3. Explicit visible spacers remain available

The public `blank_line` algebra operation and its HTML and Markdown implementations remain in
`lib/std/text/yumark.yu`. Direct builder code may still call, for example,
`blank_line("\n")`, when it deliberately wants the operation's visible rendering.

Ordinary Yumark literal and doc-comment syntax will no longer produce that operation. This effort
adds no new source syntax for manual spacers.

## 4. Required invariants

The implementation must preserve all of these properties:

1. Parser CST text and source ranges remain byte-lossless for LF and CRLF input.
2. A contiguous `--` run has one `DocCommentDecl`/`YmDoc`, and its structural continuation tokens
   remain inspectable in the CST.
3. Inline syntax may begin on one `--` line and finish on a later contiguous `--` line.
4. Parser-generated `YmBlankLine` nodes never reach the runtime algebra.
5. Direct calls to the retained `blank_line` builder keep their current behavior.
6. Static doc rendering and production Yumark rendering agree on paragraph continuation and
   structural separation.

## 5. Characterized pre-change baseline

Slice 1 deliberately pins the behavior that later slices will replace:

- `first\nsecond` renders as one paragraph, while `first\n\nsecond` additionally invokes the
  visible `blank_line` operation.
- adjacent `-- first` / `-- second` source lines produce two parser declarations and two rendered
  paragraphs;
- a link split across adjacent `--` lines closes at the physical declaration boundary, duplicates
  its buffered CST text/trivia during recovery, and does not parse as one inline construct;
- an empty `--` declaration becomes an independent empty/boundary unit rather than the logical
  blank line of one document; and
- LF and CRLF take the same old declaration-per-physical-line path while preserving their bytes.

These characterization assertions are intentionally expected to change or be replaced during the
parser and lowering slices. They are evidence for the migration, not the final specification.

## 6. Non-goals

- Do not remove or rename the public `blank_line` builder.
- Do not add explicit spacer syntax.
- Do not merge block doc comments with neighboring line docs.
- Do not perform the line-doc merge in `module_map`, the static renderer, the lazy-render mapping,
  or the future hover cache.
- Do not resume language-server integration until these source semantics and parity are complete.

## 7. Implementation record

The boundary migration landed in five independently verified commits:

1. `9a241468` (`test: characterize Yumark structural boundaries`) documented the approved target
   and pinned the old parser and rendering behavior before the semantic switch.
2. `a6886e28` (`feat: identify structural Yumark blank boundaries`) added the sequence-level CST
   normalizer which recognizes a parser-generated `YmBlankLine` and its duplicated adjacent
   newline boundary as one structural span.
3. `3e1d4947` (`feat: make Yumark source blank lines structural`) wired that normalizer into
   production lowering and static doc rendering. Parser-generated blank lines now emit no algebra
   operation, while direct `blank_line(...)` builder calls retain their original rendering.
4. `fa076484` (`feat(parser): parse line doc continuations structurally`) made contiguous `--`
   lines one lossless `DocCommentDecl` / `YmDoc`, with subsequent `--` markers represented as
   structural `LineDocPrefix` tokens. Cross-line inline syntax now parses before any downstream
   doc association or rendering.
5. `9f61e04e` (`fix(infer): align line doc rendering with continuations`) taught doc consumers to
   discard `LineDocPrefix` as structural syntax and re-pinned static rendering, owned render input,
   cache identity, and lazy-evaluation parity around one logical line-doc unit.

The final behavior satisfies section 4: ordinary source blank lines are structural at every
position; contiguous line docs preserve exact LF/CRLF source while sharing one logical Yumark
document; split inline syntax crosses continuation prefixes; block docs and real blank source lines
still terminate a line-doc run; static and lazy Markdown rendering agree byte-for-byte; and the
explicit public spacer builder remains visible and unchanged.

The retained real-literal workload
`tests/yulang/regressions/cache/yumark_shadow_literal_performance_workload.yu` now lowers to 128
static Yumark algebra calls and no `blank_line` call. Its historical “more than 70 operations” scale
claim therefore remains accurate after this amendment.
