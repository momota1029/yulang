# LS recovery audit

Date: 2026-11-08. Status: audit observations and task proposals, **not a grammar decision**.
Parser: `caa1dab986e1699b7e237215a11526d9936b2d49`, branch `ls/recovery`.
No parser implementation, existing tests, fingerprints, `spec/`, or `lean/` changed.

**Conclusion:** the CST is a useful, lossless foundation, but recovery alone is not
adequate for the requested LS availability contract. Malformed Yumark can panic;
unmatched delimiters can move subsequent code into another construct; a single
edit can cause 21–27 diagnostics. Most ordinary typing prefixes work substantially
better. The new postfix `if` passed the inspected syntax-level typing states.
Actual completion, hover, definition, and semantic-token results are unverified:
the current checkout has no semantic/editor layer implementing them.

## Requirement source and checklist

`main` is absent locally. All historical inspection used the available local
`origin/main`, commit `a58eefc31e22141574b6f20c6a5748151c6d79f1`; no fetch/network.
Historical paths/lines below refer to that commit, not this checkout.

* `crates/yulang/src/source/mod.rs:923–973,2951–3002`: member context was detected
  by scanning identifier characters around the cursor and checking the preceding
  dot. `x.` did not produce a usable selection, so completion replaced the member
  text with `yulang__completion__probe`, reparsed/lowered/checked, then matched its
  exact selection span to retrieve receiver type/effect/local method scope
  (`:3360` onward). It did **not** obtain this context from a node-at-offset API.
* The same file `:3149,3755,4039,4402`: hover/definition used resolved definition,
  reference, local and selection spans, choosing the smallest containing span.
  Nonempty spans are half-open; empty spans match their exact position.
  Completion's local-scope enumeration instead includes the interval end (`:3288`).
  Thus reliable byte ranges, preserved name occurrences and binder/scope structure
  matter even when an adjacent expression is broken. CST shape alone cannot
  supply the resolved symbols or types.
* `crates/yulang-editor/src/semantic_tokens/mod.rs:54–76,95–107,182–188,741–755`:
  lexical tokens were collected before parsing, parser panics were caught, raw
  invalid fragments were relexed, and an empty `InvalidToken` under `PathSep`
  caused lexical recovery of its enclosing path. Tests `:312–365` require tokens
  to survive `f(`, `struct point {`, `[1, 2`, `foo.bar.`, unterminated strings and
  `std::foo::`. The old parser used empty **InvalidToken**, not today's `Missing`.
* `crates/yulang/src/source/mod.rs:2870–2919` diagnosed each `InvalidToken`, mapping
  an empty node to “unexpected end of input” and adjusting trailing-space ranges.
  `crates/yulang-editor/src/text/mod.rs:37–118` supplies byte/UTF-16 conversion and
  exact empty-range containment; `hover/mod.rs:24–48` selects diagnostic hover by
  these ranges.
* `notes/todo/language-server.md:15–20,58–63,69–130` records the sentinel workaround,
  keyword-only fallback (empty for member context), no last-good-analysis fallback,
  missing local completions in trivia/arrow positions, and absent cursor-to-source-
  order mapping. It explicitly records **two** diagnostics for `my x =` (parser
  plus lowering). The old LS therefore did not solve duplicate-cause diagnostics.
  `docs/yulang3-architecture.md:527–531` says to preserve partial semantic facts,
  rather than carrying forward buffer rewriting and full-pass probes.

The acceptance checklist combines those concrete needs with the task's standard
editor-availability requirements. A PASS below is scoped to the measured corpus,
not a proof over arbitrary strings.

| ID | Required parser contribution | Result | Evidence |
| --- | --- | --- | --- |
| A1 | Any UTF-8 text yields a CST without panic/abort, with bounded work | **FAIL** | 20 caught panics / 91,310 calls; 19 corpus mutations plus one small reproducer. 4,096 nested parentheses abort during parse. No observed 5 s timeout. E1. |
| A2 | Exact source reconstruction and token byte ranges | **PASS, returned CSTs** | 91,290 returned CSTs: zero text mismatches, zero token/source-slice mismatches. Includes incomplete calls, strings, sigils and stray closes. No CST exists for A1 failures. |
| A3 | Resynchronize at statement, dedent and caller-close boundaries; retain unaffected scopes | **FAIL** | Root suffix changes: deletion 410/4,181; inserted opener 8,995/22,248; stray token 503/29,664. Declarations fare better than expression/loop statements. E2/E3. |
| A4 | Preserve completed prefix statements; expose incomplete slots/expectations | **PARTIAL** | 2/8,322 eligible root-prefix comparisons changed; 0/8,280 scalar-sample comparisons changed. 5,784 prefixes have terminal recovery, but only 783 expose schema expectations. Sigil prefixes retain raw Error only. E4/E5. |
| A5 | Identify call/record/pattern/type/condition context at cursor, including trivia | **PARTIAL** | 54 handwritten states: 53 return trees, one panics. Call/pattern/type owners survive; `x. ` and `say:\n` put the cursor token at Root. Bare sigils lose their intended primary kind. E5 and typing table. |
| A6 | Keep diagnostics near their independent root causes | **FAIL** | One deleted token yields up to 21 syntax diagnostics; one inserted opener 27; stray token 11. Missing close + missing operand can reasonably be distinct, but E3 reinterprets a whole companion as fields. |
| A7 | Small edits preserve unaffected structure suitable for cached analysis | **PARTIAL** | Large structural changes measured; even earlier roots change (138/4,026 deletion comparisons). No incremental parse/reuse API tested. SourceNodeKey is explicitly snapshot-local. E2/E4. |
| A8 | Postfix `if` retains operand/condition and surrounding owners while typing | **PASS, syntax only** | `x if`, `x if `, `x if c`, `say: a if`, `say: a if c`, invalid colon/else, suffix declaration and call-comma cases retain proposed ownership. Missing condition still lacks mapped expectation (A4). |

## Existing coverage and the new measurement

Read the architecture's recovery/CST sections, the postfix-if addendum, and the
expression, fixed-tail, delimited, indented, string, pattern, type and declaration
recovery tests. They contain concrete range/owner/remainder/losslessness assertions,
not merely “parse succeeds.” `recovery_mutation_tests` protects valid full-CST
fingerprints and checks declaration recovery, nested/mismatched delimiters,
comments/strings, matching-block shielding and indentation. Its
`wp18_dedent_requires_a_declaration_and_uses_the_enclosing_statement_indent`
explicitly expects an ordinary name or `for` line **not** to close an unmatched
group. This is an intentional existing policy, insufficient for the stronger A3.

The existing `examples/recovery_mutation.rs` deletes closers, inserts openers at
all scalar boundaries and truncates inside lines. It asserts losslessness, measures
exact later **root-child** fingerprints, and counts the removed suffix as lost in
its truncation metric. It does not compare preserved prefix statements, enumerate
all token deletions, test cursor contexts/expectations, or count diagnostics.
Its shared corpus omits `syntax-reference/`, filters nonclean Markdown examples,
and uses a stand-in prelude. Neither that harness nor protected fingerprints were
changed or regenerated.

New reusable tool: [`ls_recovery_audit.rs`](../../crates/yu-syntax/examples/ls_recovery_audit.rs).
Full input manifest, exclusions, panic inputs, typing trees, expectation histogram,
and five worst structural/cascade cases per mode are in
[`ls-recovery-results.txt`](ls-recovery-results.txt). These are observations, not
new regression expectations.

| Source group | Candidates | Clean with chosen syntax environment | Unique additions |
| --- | ---: | ---: | ---: |
| `spec/` Yulang fences | 147 | 134 | 134 |
| `tests/contracts/phase2-parser/` `.yu` files | 13 | 8 | 8 |
| `web/playground/examples/` `.yu` files | 10 | 9 | 9 |
| `syntax-reference/` examples/fragments | 4,527 | 3,337 | 554 |
| `syntax-guide/` Yulang fences (supplementary) | 114 | 110 | 45 |
| Total | 4,811 | 3,598 | 750 |

Extraction recursively includes both reference languages: Yulang fences, whole
reference `text` fences, source reconstructed from reference XML `text` attributes,
and inline backtick fragments. Whole `text` grammar blocks are tried, not assumed
to be programs. Opening-fence indentation is removed. Duplicates are eliminated
by exact source plus environment mode, in deterministic traversal order; translated
examples are not independent samples. The 750 unique clean sources total 33,491
bytes and include many short fragments. This is not 750 representative modules.

All 4,811 candidates are parsed and integrity-checked. Exhaustive mutations use
the 750 clean sources, not rejected candidates. `.yu` files use the empty imported
environment; Markdown uses the existing corpus helper's prelude, with local
operator declarations respected. The five rejected contract files are intentional
malformed/undeclared-operator cases. The rejected playground file is
`yulang2-named-defaults.yu`. The 13 rejected spec blocks include placeholders and
environment-dependent forms (e.g. `>=` is absent from the stand-in prelude).
“Clean” is parser-observed acceptance, **not an independent validity oracle**;
coverage of every semantically valid example under its real import environment
cannot be certified. Rejected inputs remain visible in the results.

Token-boundary means every start/end of every full-CST token, including trivia,
string pieces and EOF (positions deduplicated per source). Scalar sampling covers
every UTF-8 scalar boundary, including EOF, in 40 sources: first 24 plus subsequent
non-ASCII sources until 40. Every byte is covered for ASCII; slicing inside a
multibyte character is not a valid Rust `str` and was not attempted.

Statement comparison uses root children and nested `Statement` wrappers, their
significant-token start, ancestor kinds, and full significant CST shape/spelling.
Trivia ownership is ignored for this comparison only; losslessness is checked
separately. Eligible earlier statements end **strictly before** the edit/cut;
eligible later statements start strictly after the removed range. Offsets are
shifted for insertion/deletion. The active containing statement is excluded.
Root and nested units overlap, so their combined count is not a count of
independent user statements. A changed signature is structural evidence, not
proof that a particular hover result is wrong.

| Probe | Attempts | Panics | Earlier root changes/comparisons | Later root changes/comparisons | Multi-diagnostic parses | Maximum diagnostics |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Every CST token boundary, prefix | 10,639 | 0 | 2/8,322 | N/A | 1,233 | 4 |
| Every scalar boundary, sample prefixes | 5,181 | 0 | 0/8,280 | N/A | 294 | 4 |
| Delete each nontrivia CST token | 5,902 | 1 | 138/4,026 | 410/4,181 | 552 | 21 |
| Insert each `(`, `[`, `{` at interior token boundaries | 27,417 | 3 | 635/23,475 | 8,995/22,248 | 12,206 | 27 |
| Insert each `@`, `)`, `]`, `}` at those boundaries | 36,556 | 15 | 21/31,300 | 503/29,664 | 11,106 | 11 |

Counts exclude panics from shape/diagnostic comparisons. Mutation sources can
become valid programs: 2,477 clean deletions, 1,640 clean opener insertions and
2,331 clean stray insertions. Of these, 239 deletions change an eligible unit;
no clean insertion does. The aggregate damage rates are therefore not pure
recovery-failure rates. Reported worst malformed examples do have diagnostics.
Maximum collateral is 13 combined units for deletion, 14 for opener insertion,
and 4 for stray insertion. Combined prefix comparisons change 2/11,499 units.

Of 10,639 token prefixes, 5,808 have diagnostics; 5,784 have a diagnostic at EOF
or before trailing whitespace. Only 783 of the latter (13.5%) have any mapped
expected syntax. The histogram includes 6,337 terminal diagnostic occurrences
with `slot=None, expected=None`. Diagnostics absent from an otherwise valid
prefix are not counted as missing recovery: a completed identifier, for example,
does not require a fabricated error. This metric does not decide all possible
continuations or prove that every genuinely incomplete prefix is marked.

## Five concrete problem groups

**E1 — no CST for malformed Yumark; stack exhaustion.** Minimal reproducer:

```yulang
---
\if@(c){yes}
---
```

This panics at `src/declaration/doc_comment.rs:111`, the unconditional
`parse_block_document_direct(...).expect(...)`. The message is
`selected yulang fence convergence is outside Gate 6: SelectedYulangFenceBody { range: 3..12 }`;
the reproducer contains no code fence. Nineteen other panics result from one
deletion/insertion in the accepted `yumark-document.md:139` example's `\if`.
There is no partial returned tree for any of them. A second independent failure:
`"(" * 4096 + "x" + ")" * 4096` (8,193 bytes) aborts with stack overflow before
the probe prints its post-parse marker. Depth 2,048 succeeds; this is an
environment-specific observation, not an exact maximum safe depth. `catch_unwind`
cannot recover from this abort.

**E2 — declaration-only resynchronization loses executable siblings.**

```yulang
my a = (1
say: 2
my c = 3
```

Tree: `Binding(a, ParenthesizedExpression(1, say: 2, Missing))`, then `Binding(c)`.
`say` becomes a parenthesized item, not a root statement. Similarly,
`my a = [1\nfor x in xs: x\nmy c = 3\n` puts `for`, `x`, `in`, `xs` in an ordinary
identifier/ML-argument chain inside the list; no `ForStatement` remains.
`my a = (1\n2\n3\n` and `my a = {1\n2\n3\n` also absorb both later expressions.
Conversely `my a = 1\n)\nmy b = 2\nmy c = 3\n` retains all three bindings with
one local Error, and broken `x.` between bindings retains both neighbors.
Deleting the first `}` from the eight-expression record/block example in
`spec/03-expressions.md:27` absorbs seven later roots (13 overlapping units).
Thus lossless text and one diagnostic can still hide substantial LS structure.

An unterminated ordinary string, `my a = "oops\nmy b = 2\nmy c = 3\n`, retains
the suffix as `StringText` plus one Missing and loses both later bindings. This
is lexical ambiguity, not evidence that newline termination is legal: a repair
must preserve the language's accepted multiline strings.

**E3 — one missing delimiter causes a diagnostic cascade.** Delete `}` just
before `with` from the accepted `spec/04-types.md:151` example:

```yulang
struct point { x: int, y: int  with:
    our p.norm2 = p.x * p.x + p.y * p.y
```

There are **21** syntax diagnostics. The tree repeatedly constructs
`StructField(with: TypeExpression(our p))`, `StructField(Error("."))`, fields
named `norm2`, `x`, `y`, and separator Missing nodes. The companion never
survives as a companion. Inserting `(` between `struct` and `point` in the
colon-layout example at `spec/02-declarations.md:121` yields **27**, consuming its
`with:` body as fields. Deleting interpolation `}` at byte 13 of
`spec/03-expressions.md:62` yields **19**, reinterpreting later quoted examples
as statements inside interpolation. These are single edits of clean baselines.

**E4 — EOF can change a previously completed statement.**

```yulang
my a = 1
my b = 2
---
```

The final `---` is not a block-doc opener until a following physical newline
exists. In this typing state the preceding binding's body becomes
`OperatorChain(2, InfixOperatorUse("-"), Error("-"), Error("-"))`.
The corpus truncation at `doc-comment-declaration.md:129`, byte 35, changes the
same preceding binding shape. The other mismatch is the whitespace example,
byte 46: `not f x\n-` gains an infix minus and Missing in the preceding root
chain. Continuing to the full file makes the last line a different construct.
This is concrete prefix instability; choosing a tentative-doc/operator policy
would require a language-owner decision, not an audit-time parser fix.

**E5 — structure often survives, but completion needs CST-specific inference.**

| Typing state | Retained CST / cursor observation | Diagnostics / expectation |
| --- | --- | --- |
| `x.`, `x::`, `use a::` | FieldTail / PathTail / UsePath containing Missing | one each; no mapped slot or expectation |
| `x. ` | FieldTail still exists, but EOF token is whitespace directly under Root | Missing at byte 2, cursor byte 3 |
| `'`, `$`, `&` | root Error token only | one raw error; no intended primary/Missing |
| `my '`, `my $`, `my x = &`, `type T = '` | containing declaration/pattern survives; partial sigil is raw Error | no mapped expected identifier/expression/type |
| `x \|`, `for x in`, `if`, `if c:` | infix operand / ForIterable / Condition / IfArm Missing | one each; generic diagnostics |
| `case v:`, `catch x:` | arm with Pattern(Missing), then another Missing | two each at the same EOF; generic |
| `case v: x ->`, `catch x: p ->` | binder pattern and arrow survive; body Missing | one generic diagnostic |
| `say:\n` | ColonApplicationTail(Missing); EOF newline under Root | Missing before newline, not at cursor |
| `(`, `[`, `f(`, `f(a, ` | respective delimiter/call owner survives | one mapped closing-parenthesis/bracket expectation |
| `{`, `{ name = ` | braced statement/record syntax survives; assignment owner retained | one/two generic Missing diagnostics |
| `my { name, `, `my (x, `, `my x: `, `type T = ` | RecordPattern / ParenthesizedPattern / TypeExpression preserved | one generic Missing each |
| `"unterminated`, `"abc\` | StringLiteral survives; latter also StringEscape | one/two generic Missing diagnostics |

The old sentinel workaround's original syntactic problem is improved by
FieldTail(Missing): receiver `x` is now directly recoverable from the tree.
However, a completion implementation still needs a cursor policy that searches
relevant zero-width slots and adjacent nontrivia tokens, rather than taking only
the token at EOF. Generic diagnostics are deliberate in
`structural_diagnostic.rs:9–12`; an LS could interpret owner/ordered-child shape
itself, but the public expectation API currently does not cover these slots.

Postfix controls: `x if` and `say: a if` retain a `PostfixIfExpression` around the
whole operand, with `Condition(OperatorChain(Missing))`. Adding `c` fills that
condition and removes the diagnostic. `f(x if, y)` retains comma, `y`, and `)`;
`my before = 0\nx if\nmy after = 1\n` retains both bindings. `x if c:` and
`x if c else y` keep the guard and diagnose the invalid suffix as one Error group.
The empty condition has no mapped `ExpectedSyntax::Condition` payload.

## Ranked, separate follow-up tasks (not implemented)

1. **P0: remove malformed-Yumark panic paths.** E1 should return a lossless
   DocCommentDeclaration with bounded recovery and preserve the following
   declaration. Cover the minimal command and the 19 recorded single edits;
   do not solve this with an LS-only panic catcher.
2. **P0: bound recursive expression parsing.** The 8 KB parentheses input must
   not abort an LS worker/process. Choose iterative construction or an explicit
   recoverable nesting limit; preserve text in any limited region. Test balanced
   and unbalanced nesting in isolated subprocesses, including normal LS thread
   stacks. Existing iterative Yumark/drop tests do not establish this property.
3. **P1: contain declaration-field recovery at companion/layout boundaries.**
   Start with E3's missing `}` and `with:`; retain the companion and replace its
   21 field diagnostics with a local close failure. Then handle inserted `(` and
   the interpolation-close example as separate owner-specific tasks.
4. **P1: extend unmatched-delimiter resynchronization beyond declarations.**
   Use E2's `say` and `for` lines, caller closes and nested indentation. The
   grammar admits multiline items, so the owner must approve the ambiguity policy;
   do not simply stop every delimited expression at newline. Keep the matched-
   delimiter shielding and valid multiline controls already tested.
5. **P1: map ordinary completion slots into the existing expectation schema.**
   First FieldTail/PathTail/UsePath, then operator operands, ForIterable,
   Pattern/TypeExpression, case/catch, strings and postfix Condition. E5 provides
   small examples. Each task can add mapping without changing accepted syntax.
6. **P2: preserve partial-sigil context.** For `my '`, `type T = '`, `$`, `&`,
   determine how to retain native sigil intent plus a missing required component.
   Keep invalid complete tokens invalid; any admission change needs approval.
7. **P2: add a CST cursor-context accessor.** Define whitespace, zero-width,
   between-token and empty-file behavior using `x. `, `say:\n`, call/pattern/type
   controls. Expose source range, owner and expected slot; semantic receiver type
   and symbol enumeration remain semantic-layer responsibilities.
8. **P2: decide tentative EOF doc/operator handling.** E4 motivates an explicit
   decision and two prefix regression controls. Until then, consumers must allow
   reanalysis of earlier roots when these suffixes change. Cross-revision cache
   identity is a separate task: `SourceNodeKey` (`full_parse.rs:114–141`) includes
   a parse brand, and diagnostics also promise only snapshot-local identity.

## Commands, exit codes and limits

Run from this clone's root. Final evidence commands:

```sh
rustfmt --edition 2024 --check crates/yu-syntax/examples/ls_recovery_audit.rs
# exit 0
cargo run -p yu-syntax --example ls_recovery_audit --release --offline > notes/audit/ls-recovery-results.txt 2> /tmp/ls-recovery-audit.stderr
# exit 1: expected audit failure, 20 caught parser panics
RUST_TEST_THREADS=2 cargo test -p yu-syntax --offline > /tmp/ls-recovery-tests.txt 2> /tmp/ls-recovery-tests.stderr
# exit 0: 1,657 unit + 11 integration tests passed; one existing manual performance test ignored
git diff --check
# exit 0
```

Additional executed probes: initial `cargo run ... -- --typing` exited 0 before
the panic reproducer was added; two development full sweeps exited 1 (first
90,546 calls/19 panics, then 91,310/20 after fence dedenting and added controls).
`cargo test -p yu-syntax --offline -- --list` exited 0. These development sweeps
were for probe corrections, not independent statistical repetitions.

For individual trees or failures, put the input in a UTF-8 file and run:

```sh
RUST_BACKTRACE=1 target/release/examples/ls_recovery_audit --file /tmp/ls-recovery-panic.yu
# executed with E1: exit 1, panic captured; --file with E3: exit 0, tree + 21 diagnostics
target/release/examples/ls_recovery_audit --typing
# reusable subset; final version exits 1 because E1 is included
```

Depth checks used this bounded subprocess recipe (Python wrapper exit 0):

```python
import resource, subprocess
resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
for depth in (2048, 4096):
    p = subprocess.run(
        ['target/release/examples/ls_recovery_audit', '--stress', str(depth)],
        capture_output=True, text=True, timeout=5)
    print(depth, p.returncode, p.stdout, p.stderr)
```

Final rerun: 2,048 exited 0 (`parsed`, `ok`); 4,096 returned Python `-6`
(SIGABRT, shell equivalent 134), no `parsed` marker. Preliminary isolated depths
32–1,024 also exited 0; 8,192 and 16,384 aborted. No child timed out.
Environment: Linux x86-64, release Cargo profile, default process stack; no
`RUST_MIN_STACK` tuning. The full audit took 8.382 s after compilation; maximum
timed parse-plus-header/prelude/integrity-check call was 2,539 μs, zero above
100 ms. These are availability observations, not parser-only benchmarks or an
asymptotic bound. A 5 s watchdog terminates the sweep on a stuck parse/integrity
check (exit 124), identifying its case/edit. It does not isolate a stack abort,
bound diagnostic traversal, or continue beyond a timeout.

Unverified: arbitrary-text totality beyond this finite corpus; invalid UTF-8;
real import/operator environments for all examples; every Rust test string or
unfenced prose example; byte sampling beyond the selected 40 sources; timeout
recovery in a live LS; UTF-16 adapter behavior for these new trees; actual semantic
availability, cross-layer diagnostic suppression, completion relevance, hover and
definition correctness, resolved token classes, incremental node reuse and cache
invalidation. Parser requirements for those semantic consumers are preserved
names/binders/owner ranges, explicit incomplete slots and recoverable siblings;
the tree cannot itself verify the missing semantic computation.
