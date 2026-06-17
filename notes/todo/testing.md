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
- `fail_test: str -> unit` など、typed error `fail err` と衝突しない名前
- test case を名前付きで集める仕組み

## Fixture と golden test

- CLI から Yulang test file をまとめて実行する runner を用意する。
- parser / type / runtime diagnostics は、必要なものだけ compact golden として固定する。
- playground example のうち重要なものは CLI regression に写す。
- "infers but does not run" は expected limitation ではなく failure として追う。
- host capability を使う test は native-only / wasm-unsupported の区別を明示する。

## 2026-06-17 P0 regression set

playground 公開前に、最近壊れた境界を小さい fixture として固定する。

- list update:
  - `my $xs = [2 3 4]; &xs[1] = 6; $xs`
  - primitive `list` path の解決、ref_update payload union、VM boundary を同時に見る。
- nondet once triple:
  - `each 1..`, nested `each a<..`, `guard`, `.once`
  - playground std と通常 std の差、constructor display、range/int conflict を見る。
- labeled sub / callback residual:
  - `g: (int -> ['a & std::control::flow::loop::redo] any) -> ['a] int` のような上から押さえた型を再発させない。
  - `return` / `redo` / callback residual が shallow handler と同じ推論にならないことを見る。
- deep handler act method:
  - `std.control.nondet.nondet.#act-method:once` は `α [nondet; β] -> [β] opt α` 系で export される。
  - `[handled; 'e] -> ['e]` を普通の関数として forward した時に shallow handler 型へ潰れない。
- specialize2 function candidate effect variance:
  - 同じ arg/ret で `arg_effect` だけ違う関数候補。
  - 同じ arg/ret で `ret_effect` だけ違う関数候補。
  - effectful callback を pure expected へ渡すケースと、その逆。
- concrete subtype mismatch:
  - tuple length mismatch。
  - record required field missing。
  - polyvariant / enum constructor mismatch。
  - これらが coerce/runtime boundary ではなく subtype constraint として落ちること。
- optional record default:
  - `our box {width = 1, height = width} = width * height`
  - default field 間の依存が `int` 固定にならず、必要な role constraint だけ残ること。
- playground/editor surface:
  - `tok-type` / `tok-function` / `tok-property` の class drift を固定する。
  - CLI diagnostics と playground diagnostics が同じ原因を指すこと。

## 最初の slice

- `tests/yulang/` のような小さい fixture 置き場を決める。
- `1 + 2`、関数呼び出し、variant、role method、effect handler の smoke test を置く。
- 上の P0 regression set から、既に Rust test helper で動かせるものを先に移す。
- `std::console` と `std::fs` は host policy が固まるまで smoke test を分ける。
- 既存 Rust test から同じ fixture を呼べるようにする。

## やらないこと

- 最初から property testing や snapshot 大量生成に広げない。
- diagnostics の全文を広く固定しすぎない。
- playground 専用 behavior を portable な test contract にしない。
