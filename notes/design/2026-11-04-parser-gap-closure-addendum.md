# Parser gap closure: forms promised by `spec/` that yu-syntax does not yet read

Status: Authoritative

Drafted-by: primary (Claude), from two read-only investigations of `crates/yu-syntax` and a run of 80 `spec/` examples through `parse_file`

Reviewed-by: none yet. Each work package is reviewed independently before it lands.

Approved-by: user, 2026-11-04 (approval of the plan "パーサ修正計画" and of the scope answers recorded below)

Supersedes: in scope only, the following earlier decisions (all from tag `archive/proof-sprint-2026-11-04` or this tree):

- unary-only lambda admission (`2026-10-15-unary-lambda-parser.md` §2, tag only), for WP-10;
- the qualified-constructor-only pattern application rule (`2026-10-22-r280-y2-qualified-constructor-pattern-application.md`, tag only), for WP-9.

Scope: grammar, CST and recovery ownership for eleven forms that `spec/` promises and the parser rejects (`Error` / `Missing`). It does not change production dispatch, HIR, name resolution, or any semantics. The meaning of each form is in `spec/`.

## 1. User decisions (fixed)

1. All eleven forms are fixed in this round, including doc comments.
2. Multi-parameter lambda admits **identifiers and parenthesized patterns** as parameters.
3. In a `case` / `catch` arm, a parser pattern is written `~"..."`, as in expression position.
4. `spec/` is the authority for the intended forms. When the parser and `spec/` disagree, `spec/` wins unless this memo says otherwise.

## 2. Common rules

- `SyntaxKind` is append-only. `LambdaExpression` was moved to the end (commit `77fe5a69e`) to restore the pinned discriminants. New kinds go after it.
- A new NUD token kind must be added both to the NUD scan (`lexical/lexer.rs`) and to `operator_chain.rs` (`is_normal_core_item` and the NUD dispatch). A kind in the scanner without a dispatch arm reaches `unreachable!` and is a defect.
- Existing expected values are protected (`rules/testing.md`). Only the two pins named in §4 WP-9 and WP-10 change, with the rationale written there.
- Every package ends with: fixtures in `crates/yu-syntax/src/tests/`, the `syntax-reference/{ja,en}/src/` page updated, the `spec/parser-gaps.md` row removed, and `cargo test -p yu-syntax` green.
- A package that needs a decision not written here stops and reports. It does not decide locally (`rules/parser-chasa.md`).

## 3. Decisions per package

### WP-1 `mod helper;`

Measure first. The existing tests pin `mod test;` clean, yet `mod helper;` yields `Missing` in a direct run. Find the cause. If the form is already valid and the test input differs, correct the ledger only. Otherwise fix at the owning responsibility and add a fixture.

Result (2026-11-04): the root path of `parse_file` passes `STOP_SEMICOLON`; `mod_decl` treated the module's own `; { :` body starter as an outer boundary. The module's own body starter now wins over caller stops. The old `mod test;` pins used a direct harness with no stops, which is why they stayed clean.

### WP-2 type annotation on an arm pattern (`x: int -> 1`)

`->` and the guard keywords (`if`, `where`) belong to the arm owner. The annotation's type stops at them. This is the existing contract in `syntax-reference/ja/src/patterns/type-annotation.md` §6; the implementation did not map `PATTERN_STOP_ARROW` into the type caller stops. A function-typed annotation needs parentheses: `(x: int -> int) -> body`.

Result (2026-11-04): the type parser now receives the arm arrow (`STOP_ARROW`) and the `if` / `where` guard keywords (`TypeOuterBoundary::ARM_GUARD_IF` / `ARM_GUARD_WHERE`) as caller boundaries.

### WP-3 `struct` type parameters

`struct pair 'a 'b { fst: 'a, snd: 'b }`. The header reuses `DeclarationTypeParameterList`. The four duplicated parameter helpers are merged into one shared helper (`declaration/type_parameters.rs`) with an explicit mode: `type` / `enum` / `error` keep `SigilOrIdentifier` (unchanged CST and recovery); **`struct` accepts only sigil parameters (`SigilOnly`)**, because `spec/` writes type variables only as `'a` and the existing pin `struct S Foo` (a bare identifier is not a parameter) must stay. Parameters must not consume `derives`, `with`, `(`, `{`, `:` or `;`. `struct s 1 { ... }` keeps the struct header's own recovery (the struct body protects an integer as a type starter); it is not made equal to `enum`'s. (Decision recorded 2026-11-04 after the first implementation hit the `struct S Foo` pin.)

### WP-4 float literal and positional field

- Float: `\d+\.\d+` and `\d+[eE][+-]?\d+`. The dot must be followed by a digit. `..` is never part of a float, so `0..10` is unchanged. New kind `FloatLiteral`.
- Positional field: after a `Dot` tail, an adjacent integer token is read as an integer only, never as a float. So `x.0.1` is two field tails. The tail reuses `FieldTail` with an integer in the field position (no new kind unless a fixture shows an ambiguity).
- Float patterns are out of scope.
- Kinds (decided 2026-11-04): `FloatLiteral` is the node and `Float` the token, appended in that order after `LambdaExpression`, mirroring `IntegerLiteral` / `Integer`.

### WP-5 `$x` and `&x`

In operand position (NUD), `$name` and `&name` adjacent to an identifier are `SigilIdentifier`. After an operand (LED), `&` stays an operator, so a user-declared infix `&` keeps working. `&count = value` is the existing `AssignmentTail` with a sigil operand. Implemented as: the NUD scan and the ML-argument position (LED after trivia) read an adjacent `$name` / `&name` as a `SigilIdentifier` wrapped in the existing `IdentifierExpression`; a declared infix `&` is tried first in LED position, so `a & b` is unchanged. A reference read is an `IdentifierExpression`-like node over `SigilIdentifier`, as the declaration side already uses.

### WP-6 labels in expressions

`'name` is accepted in operand position and as an ML argument. `'done.return 42`, `last 'outer`, `return 'done 42`, `sub 'done:` all follow from this. The existing head probes (`case 'c`, `catch 'c`, `for 'c`) run first so their behavior does not change. The label's meaning (`'done.return` as a method-like operation, and the recursion call form of M2 in `spec/03c-control.md`) belongs to later phases; the parser records structure only.

Result (2026-11-04): the WP-5 sigil scan also accepts a leading `'` in NUD and ML-argument positions (`scan_expression_sigil_identifier`), reusing `IdentifierExpression(SigilIdentifier)`. One pre-existing test changed its incidental expectations with the user-delegated approval of the primary: `nested_statement_blocks_do_not_enable_declaration_where_prefixes` (`where 'a: Display` in a nested block). Its contract, that no `WhereClause` is built in a nested block, is unchanged and still asserted; the old pins (text stops at `where`, pending Unknown `'`) only recorded that an expression-position `'a` was unsupported, and now the whole line parses as the ordinary expression `where 'a` followed by a colon application.

### WP-7 list literal

`[]`, `[1, 2]`, `[1, ..xs, 3]`. A new `ListExpression` kind with `[` `]` as its delimiters, built like `ParenthesizedExpression` with a new `DelimitedOwner::List`. A spread item is a new kind appended at the end (`ListExpressionSpreadItem`), following `ProjectionRecordSpreadItem`. Recovery follows the existing delimited-sequence authority (`cross-cutting/layout-aware-separator-authority.md`).

Result (2026-11-04): `[` is now a list-literal expression start (NUD and ML argument). Kinds `ListExpression` and `ListExpressionSpreadItem` were appended after `Float`. Inside a list each item is read in `MlMode::All`, so `[1 2]` is one item (the ML application `1 2`), exactly like `(1 2)`; it is not a missing-separator case.
Ten pre-existing tests used `[` as the canonical 'token that cannot start an expression'. With the design authority's approval: seven keep their contract and had their probe token replaced (`[` became `)`, `]@`, `?`, or `else`, each marked with a WP-7 comment); in three `case_like` tests the contract 'an unread pattern-only opener reaches the next arm's pattern owner' cannot occur any more, because every pattern start is now also an expression start. There the `n -> [tail] -> yes` rows were removed (one test was rewritten as `case_arm_body_list_literal_replaces_the_old_unread_opener_contract`, pinning one arm with a list body plus the leftover `-> yes`).

### WP-8 `~"..."` in an arm

The pattern opener also accepts `~"`. `rule_literal_normalized` is shared with the expression form. Whether a bare `"..."` stays valid in an arm is measured first. If it stays, it keeps meaning a rule literal; the result is recorded here by the package. `rule { ... }` in a pattern is unchanged.

Result (2026-11-04): measured before the change, the bare `"..."` arm pattern was already a clean `RuleLiteral` in both `case` and `catch`; it stays accepted (no CST change). `~"` is now a Pattern NUD opener sharing `rule_literal_normalized`; in Pattern tail position `x ~"a"` is unchanged (not a primary), and `~name` keeps its recovery.

### WP-9 bare-name pattern application (`just x`, `op x, k`)

A pattern head that is a bare identifier followed on the same line by an argument is a `PatternMlApplicationTail`, when the arm stop set is active. The parser decides structure only; whether the head is a binding or a variant is name resolution's decision (`spec/03b-patterns.md` §3b.2).
Not applications: a binding header (`my x y = ...`); a name followed by `as`, `|`, `if`, `where`, `in`, `:` or the arm arrow; a name followed by a newline.
Pins that change, with this memo as the rationale: `crates/yu-syntax/src/tests/case_like.rs` (`case x: name value -> value` now has an ML tail and no structural fact) and the `"f x"` case under `PATTERN_STOP_ITEM` in `tests/pattern.rs`.

Result (2026-11-04): implemented with a `bare_identifier_head` state in the pattern parser, active only when the whole arm stop set (`PATTERN_STOP_ITEM`, arrow, `if` guard, `where` guard) is on; so binding headers (`my x y = 1` keeps its own application), `for`, lambda and non-arm nested patterns are unchanged. A same-line contiguous `:symbol` after a bare head or qualified constructor is an argument, not a type annotation. The contextual word `in` is never an argument.
Pins changed with the design authority's approval (WP-9 comments in the tests): the R280 unqualified-application pin in `case_like.rs` and the `"f x"` row in `pattern.rs` (re-expressed as a positive test with arm stops); and the stand-in `yes` in three rows of `case_arrow_body_facts_are_exact_at_source_offsets` / `case_schema_arm_and_block_slots_keep_distinct_direct_occurrences` (including the catch twin) was replaced by the contextual word `in`, which keeps the old 'missing arrow right after the pattern' facts; the new truth for `case x: n yes` is pinned separately.

### WP-10 multi-parameter lambda

`\x y -> body`, `\(a, b) -> body`, `\x (a, b) -> body`. The lambda token is emitted only when the **whole header** matches: `\`, one or more parameters, exact `->`. A parameter is an identifier or a parenthesized pattern; the lookahead balances parentheses over source text without recursion into the parser. If the header does not match, no lambda node is made and a user-declared `\` operator keeps working, as before.
CST: `LambdaExpression` holds `Backslash`, parameters, `Arrow`, body. A bare identifier parameter stays a direct `Identifier` child (the unary shape is unchanged). A parenthesized parameter is a `Pattern` node. Currying is semantics and does not appear in the CST.
Pins that change: the non-matching `\x y ->` case in `tests/unary_lambda.rs` becomes a matching case. The old expectation encoded the unary-only decision that this memo supersedes.

Result (2026-11-04): `scan_lambda_backslash` now looks ahead over one or more parameters (identifier, or a source-balanced `( ... )` group that skips literals, line comments and nested block comments) followed by the exact arrow, still emitting the `Backslash` token only for a complete header; parenthesised parameters are parsed by the real pattern parser into direct `Pattern` children. `\x -> body` keeps its exact CST. The only pre-existing test changed is the `\x y ->` row of `nonmatching_headers_do_not_create_lambda_nodes` (flipped to matching, with a WP-10 comment; its negative control became `\x y`). `\(a, b)(c) -> a` is a lambda with one `Pattern` containing a `PatternCallTail`, following the existing adjacency rules. A new reference page `expressions/lambda-expression.md` (ja/en) documents the form.

### WP-11 doc comments

Implemented exactly as the approved `2026-09-01-doc-comment-yumark-addendum.md`: a doc comment is a standalone `DocCommentDeclaration`, not trivia; `---` wins over `--` at canonical statement start; expression NUD/LED positions keep the operator path. The reserved kinds (`DocCommentDeclaration`, `DocLinePrefix`, `DocBlockOpen`, `DocBlockClose`, `Ym*`) are used. The work follows that addendum's staged plan (§11) and stops after each stage for the primary's review. A temporary opaque body is not allowed unless the user consents to the stage.

## 4. Order

WP-1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11. Packages touch shared files (`syntax_kind.rs`, `operator_chain.rs`), so they are sequential. One Codex session per package, reviewed before the next.

## 5. Verification

- `cargo test -p yu-syntax` after every package.
- All 80 `spec/` example snippets, with operator declarations prepended, parse with no `Error` / `Missing` / `Invalid` once WP-11 lands.
- `cargo xtask check-graph` and `cargo check --workspace --all-targets` at the end.

## 6. WP-11 progress and gate-level decisions (2026-11-04)

Authority: the design authority (primary) decided the following where the approved Yumark documents left a gap or conflicted. Each is recorded so a later gate can cite it.

- Gate 2 is committed (`yumark/{mod,judge,frame}.rs`): marker, strict close, line-doc, chunk judges, explicit frame stack with persistent transaction storage and a test-only full-state snapshot.
- **Neutral event contract (Gate 3).** The base addendum section 4 requires a neutral driver but does not define an event representation. Decision: a crate-private `Sink` trait driven by the grammar with node Enter(kind), Token(kind, byte range), node Exit, Recovery(kind/slot, byte range). Production never stores events; only test sinks record. Gate 5 AST and direct adapters are further sinks over the same driver.
- **Selected `yulang` fence.** Per the parsed-yulang-fence addendum sections 1 and 7, Gate 3 emits only opener, info and boundary facts; body events wait for the convergence gate.
- **Recency rule.** When two Authoritative documents conflict and the later one explicitly corrects or defers the earlier, the later wins. Applied: parsed-fence section 1/7 over base sections 7/8 (selected fence body); the prefix-trailing-whitespace amendment over the parsed-fence full-prefix wording; T2a sections 2-3 over Gate-3b section 6 (T2 embedded AST/direct equality and 'Gate 3 complete' certification are deferred to O6; no embedded facts are fabricated).
- **Allocation of what Gate 3 could not do.** Argument-bearing `InlineReference` / `InlineApply` (they need Yulang argument ownership) move to Gate 4. The canonical recovery matrix rows and the adoption of recovery output into the current transport move to Gate 5 (adapters with recovery-node and record identity). Equality and completion certification stay at O6.
- **Gate 4 committed.** Commands, `\my`, `\use`, if-chains, `do` capture, argument-bearing `InlineReference` / `InlineApply`, and embedded-Yulang delimiter ownership drive the same Sink. To let the existing Yulang parsers feed it, the parser output was generalised from `rowan::GreenNodeBuilder` to a crate-private `SyntaxOutput` trait object (`cursor.rs`); behaviour is unchanged (all pre-existing tests pass unedited) and a `yumark_use_tree_normalized` entry was added to `declaration/use_decl.rs`. **Open performance question for Gate 7:** the trait-object dispatch sits on the output path of every token; Gate 7 must measure the ordinary Yulang parse before and after (one repeated parse of a large `.yu` corpus is enough) and either keep it, or specialise the common `GreenNodeBuilder` case.
- **Gate 5 committed.** `yumark/adapter.rs` adds the AST structural-vector sink and the direct rowan sink over the same grammar run; envelope, EOF Missing, close-suffix remainder, losslessness, recovery record/node identity (adopted into the current structural-diagnostic transport) and non-embedded AST/direct topology equality are proved. Append-only vocabulary additions: `RecoveryOwner::DocComment`; `GrammarSlotRole` +15 (`Starter` .. `Terminator`); `ExpectedSyntax` +13 (`Identifier` .. `Terminator`); no `SyntaxKind` added. Still deferred to O6: canonical embedded AST/direct equality (T2 ArrowRhs fact) and completion certification; the selected `yulang` fence body.
- **Gate 6 committed (dispatch promotion).** `DocCommentDeclaration` is promoted into root and canonical Statement dispatch (`declaration/doc_comment.rs`, `root_statement.rs`, `statement.rs`, `header.rs` cutoff, braced/indented/inline sequences); role/act owner fields explicitly do not reach it. Two reference pages per language (`statements/doc-comment-declaration.md`, `statements/yumark-document.md`). No pre-existing test was edited or probe-replaced.
- **Bug found by the primary after Gate 6 and fixed in the same change.** With a declared infix `-`, `my y = f` followed by `-- doc` was read as `f - -` because a line-start infix operator continues the previous expression. Rule recorded: a marker accepted by the Gate-2 judge at the enclosing sequence's base column is a canonical Statement start; it ends the previous expression and wins even over declared `--` / `---`; a deeper-indented `--` and a mid-line `--` keep the operator path. New append-only `SequenceOwner::{IndentedOwnerField, BracedOwnerField, OwnerField}`.
- **Gate 7 committed.** A 94-row public `parse_file` matrix (line 7, block 11, commands/special 15, recovery 46, markers/remainders/placement 10, deep 5; the deep rows are 10,000 levels each) and the static performance ledger in `yumark/mod.rs`. The matrix exposed two real bugs, both fixed iteratively with regression tests: a braced command swallowing an outer `---`, and stack overflow on construction/drop of very deep trees.
- **Performance question from Gate 4 answered by measurement (2026-11-04, primary).** Parsing 68 `.yu` files (90,183 bytes: repo fixtures, playground examples and the std library copy under `.temp/`) 100 times, best of 5, release build: commit `2a12340d6` (before the `SyntaxOutput` trait object) 912.8-939.9 ms; head 921.0-933.1 ms, i.e. no measurable difference (about 9.7 MB/s both). The trait-object output path is kept.
- **Left open on purpose:** the body of a selected `yulang` Yumark fence; canonical embedded AST/direct equality and 'Gate 3/4 complete' certification (O6).

