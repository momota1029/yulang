# Focused HIR unit command stopped on compile failure

Sprint `ordinary-hir-applied-conformance-repair-20261017` rev5,
contract SHA-256
`5c63c3829cd6275523b1799e0286837518e9fd7dd0213c13f3171d9d7b7a6125`.
Luna ran the first command once after CLEAN architect and pre-run regression
gates:

```text
cargo test -p yu-hir --features shadow --lib module::tests::
exit 101, elapsed 2.67s
```

Output:

```text
Compiling yu-hir v0.1.0 (/home/momota1029/rust/yulang/crates/yu-hir)
error[E0308]: mismatched types
    --> crates/yu-hir/src/lib.rs:2611:13
     |
2610 |               expression,
     |               ---------- this expression has type `AssociatedExpr`
2611 | /             HirExpr::Error {
2612 | |                 kind: SyntaxKind::Invalid,
2613 | |                 children,
2614 | |                 ..
2615 | |             } if matches!(children.as_slice(), [HirExpr::Error {
     | |_____________^ expected `AssociatedExpr`, found `HirExpr`
     |
help: you might have meant to use field `hir` whose type is `HirExpr`
     |
2610 |             expression.hir,
     |                       ++++
```

Only the focused unit command ran; both integration commands were not started.
Per rev5, timeout/compile failure stops the run. No retry, filter substitution,
expectation edit, code edit, formatter, additional build or test has run. The
compiler failed before any test discovery/assertion, so none of the three named
falsifiers has executed. Parent theorem conditions closed: 0.
