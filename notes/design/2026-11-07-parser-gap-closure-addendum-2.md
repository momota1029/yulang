# Parser gap closure, part 2: three forms found by the syntax-guide example check

Status: Authoritative

Drafted-by: primary (Claude), from `syntax_guide_check` over `syntax-guide/ja/src/` and a read of `crates/yu-syntax/src/expression/lambda.rs`

Reviewed-by: none yet. Each work package is reviewed independently before it lands.

Approved-by: user, 2026-11-07 (decision to fix the three gaps; the three answers in §1)

Extends: `2026-11-04-parser-gap-closure-addendum.md` (same common rules, §2 there, apply unchanged).

Scope: grammar and CST for three forms (WP-12 to WP-14) and one layout boundary (WP-15) that `spec/` promises and the parser rejects. Recorded in `spec/parser-gaps.md` on 2026-11-07. This memo changes no semantics, name resolution or HIR. The meaning of each form is in `spec/03-expressions.md` (3.1, 3.4, 3.7).

## 1. User decisions (fixed)

1. A brace item that is only a spread (`{..rest}`, no name, no comma) is a **record**, not a block. Reason: a spread has no meaning as a statement. The CST does not distinguish record from block, so this fixes the reading in `spec/03-expressions.md` 3.1 and is not visible in the CST.
2. The spread item inside braces is a new kind, **`RecordExpressionSpreadItem`**, appended at the end of `SyntaxKind` (append-only), paired with `ListExpressionSpreadItem`.
3. `case:` without a scrutinee has **no `CaseScrutinee` node**: `CaseExpression("case" CaseBlock(":" ...))`. The absence of the node is the signal.

## 2. Common rules

Those of §2 of the earlier addendum apply. In particular: append-only `SyntaxKind`; a new NUD or admission change reaches both the scanner and the dispatch; protected expected values change only where this memo names the pin and its reason; every package ends with fixtures in `crates/yu-syntax/src/tests/`, the `syntax-reference/{ja,en}/src/` page updated, its `spec/parser-gaps.md` row removed, and `cargo test -p yu-syntax` green; a decision not written here means stop and report.

Also each package must make the corresponding block in `syntax-guide/ja/src/expressions.md` pass `syntax_guide_check` and remove the "current parser cannot read this" note from that page and from `syntax-guide/ja/src/checking.md`.

## 3. Packages

### WP-12 record parameter of a lambda

`\{x, y} -> x + y`. A lambda parameter may begin with `{`, and the parameter is a record pattern.
CST: unchanged shapes. The parameter is a direct `Pattern` child holding `RecordPattern(...)`, exactly as `\(a, b)` holds `Pattern(ParenthesizedPattern(...))`. No new kind.
Admission: `scan_lambda_backslash` balances braces over source text (skipping literals and comments, as it does for parentheses) and admits the lambda only when the whole header ends with the exact arrow. If it does not match, no lambda node is made, as before.
Pins that may change: any test that pins `\{...} ->` as a non-lambda header. Name each such test and its reason.
Out of scope: refutable record parameters are a semantic error (spec 3.4), not a parse error; the parser reads the pattern.

### WP-13 spread item in a brace expression

`{x: 1, ..rest}`, `{..rest, x: 1}`, `{x, ..rest}`, `{..rest}`.
CST: inside the existing brace expression, an item that starts with `..` is `RecordExpressionSpreadItem(".." OperatorChain(...))`, built like `ListExpressionSpreadItem`. The brace node kind is unchanged.
The `..` at an item start is a spread, never an operator, in the same way as inside a list. Std's `..` (range, suffix) keeps its meaning elsewhere, including inside the spread's own expression: `{..(1..3)}` is a spread of a range expression.
Recovery follows the existing delimited-sequence authority, as WP-7 did.
Pins that may change: any test that pins `..` inside braces as an error. Name each such test and its reason.

### WP-14 `case:` without a scrutinee

`case:` followed by arms. `CaseExpression("case" CaseBlock(":" CaseArm ...))`; no `CaseScrutinee`.
Admission: after `case`, a `:` that follows immediately (or after layout trivia) with no scrutinee expression opens the arms. `case n:` keeps its exact CST. A missing scrutinee with no `:` after it (for example `case` alone, or `case` followed by an arm) stays a recovery case, as today.
Pins that may change: tests that pin `case:` as `CaseScrutinee` with a `Missing`. Name each and its reason. This memo does not extend the form to `catch:` (spec marks that as open).

### WP-15 an arm whose pattern starts with `-` or `+`

Found on 2026-11-07 by the syntax-guide example check. `case n:` with a first arm followed by a second arm that begins with a signed literal fails:

```yulang
case n:
    0 -> 1
    -1 -> 2
```

The second line is read as a continuation of the first arm's body (`1 - 1 -> 2`) and recovery follows (`RawError ">"`). `+1 -> 2` and `- 1 -> 2` fail the same way; `(-1) -> 2` parses. A statement line `-1` at the same indentation as the previous statement already starts a new statement, and a first arm `-1..5 -> "a"` parses, so only an arm line that follows an arm body is wrong.
Rule (not a new decision): `spec/01-lexical.md` 1.3 — a line at the same indentation as the block's baseline starts a new item, never a continuation. An arm line is a new arm even when its first token could also be an infix operator. A continuation needs a deeper indentation, as everywhere else.
CST: unchanged (`CaseArm(Pattern(...) "->" ...)`, the pattern holding the signed literal or range as it does for a first arm).
Scope: `case` arms first. Check the same position for `catch` arms and for any other arm-list owner that shares the arm-boundary logic; fix them together only if one shared boundary check is the cause, otherwise stop and report.
Pins that may change: any test that pins a same-indentation line beginning with `-` or `+` as a continuation of an arm body. Name each and its reason. A deeper-indented `- x` continuation line must keep continuing (`1\n        - 2` as a body).

## 4. Order

WP-12, WP-13, WP-14 and WP-15 are independent. Only WP-13 touches `syntax_kind.rs`. WP-15 was added after WP-12 to WP-14 had landed. Land them as separate commits.

## 5. Verification

For each package: the focused tests for the owning module, then `cargo test -p yu-syntax` once on the settled change, `cargo fmt --check`, and `cargo run --offline -p yu-syntax --example syntax_guide_check -- syntax-guide/ja/src/` (the gap's block must be `ok`; exit code 0). Report exact commands, results, and every changed pin.
