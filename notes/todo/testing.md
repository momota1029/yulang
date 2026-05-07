# Testing TODO

目的: Yulang の言語機能、標準ライブラリ、host capability を小さな単位で確かめられるようにする。
Rust 側の regression test だけでなく、Yulang code から自然に書ける test 体験も育てる。

## 目標の形

```text
Yulang test file
  -> compile / infer / run
  -> assertion result
  -> compact diagnostics
```

## 最初の設計上の問い

- test は通常の Yulang program として書くか、専用 syntax を足すか。
- assertion failure は value-level result、error effect、trap、test runner 専用診断のどれにするか。
- type error / parser error / runtime error を expected failure としてどう書くか。
- CLI、wasm playground、Rust fixture test のどこまで同じ test file を共有するか。
- examples をそのまま regression test にするか、test 用 entrypoint を別に持つか。

## 最小 API 候補

- `assert: bool -> unit`
- `assert_eq`
- `assert_some`
- `assert_none`
- `fail: str -> unit`
- test case を名前付きで集める仕組み

## Fixture と golden test

- CLI から Yulang test file をまとめて実行する runner を用意する。
- parser / type / runtime diagnostics は、必要なものだけ compact golden として固定する。
- playground example のうち重要なものは CLI regression に写す。
- "infers but does not run" は expected limitation ではなく failure として追う。
- host capability を使う test は native-only / wasm-unsupported の区別を明示する。

## 最初の slice

- `tests/yulang/` のような小さい fixture 置き場を決める。
- `1 + 2`、関数呼び出し、variant、role method、effect handler の smoke test を置く。
- `std::console` と `std::fs` は host policy が固まるまで smoke test を分ける。
- 既存 Rust test から同じ fixture を呼べるようにする。

## やらないこと

- 最初から property testing や snapshot 大量生成に広げない。
- diagnostics の全文を広く固定しすぎない。
- playground 専用 behavior を portable な test contract にしない。
