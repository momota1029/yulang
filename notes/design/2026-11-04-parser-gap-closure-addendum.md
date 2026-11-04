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

### WP-7 list literal

`[]`, `[1, 2]`, `[1, ..xs, 3]`. A new `ListExpression` kind with `[` `]` as its delimiters, built like `ParenthesizedExpression` with a new `DelimitedOwner::List`. A spread item is a new kind appended at the end (`ListExpressionSpreadItem`), following `ProjectionRecordSpreadItem`. Recovery follows the existing delimited-sequence authority (`cross-cutting/layout-aware-separator-authority.md`).

### WP-8 `~"..."` in an arm

The pattern opener also accepts `~"`. `rule_literal_normalized` is shared with the expression form. Whether a bare `"..."` stays valid in an arm is measured first. If it stays, it keeps meaning a rule literal; the result is recorded here by the package. `rule { ... }` in a pattern is unchanged.

### WP-9 bare-name pattern application (`just x`, `op x, k`)

A pattern head that is a bare identifier followed on the same line by an argument is a `PatternMlApplicationTail`, when the arm stop set is active. The parser decides structure only; whether the head is a binding or a variant is name resolution's decision (`spec/03b-patterns.md` §3b.2).
Not applications: a binding header (`my x y = ...`); a name followed by `as`, `|`, `if`, `where`, `in`, `:` or the arm arrow; a name followed by a newline.
Pins that change, with this memo as the rationale: `crates/yu-syntax/src/tests/case_like.rs` (`case x: name value -> value` now has an ML tail and no structural fact) and the `"f x"` case under `PATTERN_STOP_ITEM` in `tests/pattern.rs`.

### WP-10 multi-parameter lambda

`\x y -> body`, `\(a, b) -> body`, `\x (a, b) -> body`. The lambda token is emitted only when the **whole header** matches: `\`, one or more parameters, exact `->`. A parameter is an identifier or a parenthesized pattern; the lookahead balances parentheses over source text without recursion into the parser. If the header does not match, no lambda node is made and a user-declared `\` operator keeps working, as before.
CST: `LambdaExpression` holds `Backslash`, parameters, `Arrow`, body. A bare identifier parameter stays a direct `Identifier` child (the unary shape is unchanged). A parenthesized parameter is a `Pattern` node. Currying is semantics and does not appear in the CST.
Pins that change: the non-matching `\x y ->` case in `tests/unary_lambda.rs` becomes a matching case. The old expectation encoded the unary-only decision that this memo supersedes.

### WP-11 doc comments

Implemented exactly as the approved `2026-09-01-doc-comment-yumark-addendum.md`: a doc comment is a standalone `DocCommentDeclaration`, not trivia; `---` wins over `--` at canonical statement start; expression NUD/LED positions keep the operator path. The reserved kinds (`DocCommentDeclaration`, `DocLinePrefix`, `DocBlockOpen`, `DocBlockClose`, `Ym*`) are used. The work follows that addendum's staged plan (§11) and stops after each stage for the primary's review. A temporary opaque body is not allowed unless the user consents to the stage.

## 4. Order

WP-1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11. Packages touch shared files (`syntax_kind.rs`, `operator_chain.rs`), so they are sequential. One Codex session per package, reviewed before the next.

## 5. Verification

- `cargo test -p yu-syntax` after every package.
- All 80 `spec/` example snippets, with operator declarations prepended, parse with no `Error` / `Missing` / `Invalid` once WP-11 lands.
- `cargo xtask check-graph` and `cargo check --workspace --all-targets` at the end.
