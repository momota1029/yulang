---
title: native-undet-write27-f 実装レポート — once value-arm heap leak 修正
date: 2026-05-12
---

# native-undet-write27-f 実装レポート

## 結論

write27-f の主目的だった「Layer 3 が heap pointer を返す原因」は切り分けできた。

結果は次の通り。

```text
pure variant case: pass
once value-arm-only: 以前は heap pointer、修正後 pass
debugs_std_undet_once_skip_eval_layers: 修正後 pass
std::undet.once skips rejected first choice: 修正後 pass
```

原因は VariantPayload ではなく、JIT runtime の `SELECTED_HANDLER_META` が単一 slot だったこと。
入れ子の `Perform` が outer perform の selected handler meta を上書きし、outer `perform_finish`
が間違った handler prompt で value arm の `opt::just 2` を再度 `ScopeReturn` 化していた。

修正は、selected handler meta を stack 化して、`select_handler` で push、`perform_finish` で pop
する形。

## 追加した regression

### pure variant case

```yu
case std::opt::opt::just 2:
    std::opt::opt::nil -> 0
    std::opt::opt::just v -> v
```

これは最初から pass した。
つまり `VariantTagEq` / `VariantPayload` の基本 codegen は壊れていなかった。

### once value-arm-only

```yu
use std::undet::*

case (each [2]).once:
    std::opt::opt::nil -> 0
    std::opt::opt::just v -> v
```

修正前:

```text
VM=2
CPS repr Cranelift=<heap ptr>
```

trace では `opt::just 2` が作られたあと、さらに `opt::just (opt::just 2)` が作られ、
外側 case が 1 回だけ unwrap して `opt::just 2` を root に返していた。

修正後は pass。

## Trace で見えたこと

heap pointer の正体は `opt::just 2` だった。

修正前の重要 trace:

```text
variant_new: tag=just payload=2 result=ptr(...:variant just payload=2)
scope_return_set (perform_finish): prompt=2 value=ptr(...:variant just payload=2)
route_scope_return action=propagate
...
variant_new: tag=just payload=ptr(...:variant just payload=2)
...
outer case variant_payload: payload=ptr(...:variant just payload=2)
return_i64 value=ptr(...:variant just payload=2)
```

つまり outer case は実行されていた。
ただし `once` の value arm が返した `opt::just 2` が、間違った selected handler meta によって
もう一段 `just` で包まれていた。

## 実装内容

- `NATIVE_CPS_I64_SELECTED_HANDLER_META` を `NATIVE_CPS_I64_SELECTED_HANDLER_META_STACK` に変更
- `select_handler_i64` で selected meta を push
- `perform_finish_i64` で対応する meta を pop
- `set_resumption_anchor_from_selected_i64` / `scope_return_from_selected_handler_i64` は stack top を参照
- `YULANG_CPS_JIT_TRACE=1` 向けに runtime heap value describe を追加
  - `variant_new`
  - `variant_tag_eq`
  - `variant_payload`
  - `scope_return_set`
  - `route_scope_return`
  - `return_i64`
  - `continue_return_frame`

通常実行では trace flag が off なので、describe は呼ばれない。

## 本線に戻した test

次は pass したので ignore を外した。

```text
compares_std_undet_once_scalar_unwrapped_through_cps_repr_cranelift
compares_std_undet_once_skips_rejected_first_choice_through_cps_repr_cranelift
```

## 残 frontier

次はまだ fail する。

```text
compares_std_undet_once_returns_nil_when_all_rejected_through_cps_repr_cranelift
  VM=0
  CPS repr Cranelift=2

compares_std_undet_once_two_nested_choices_through_cps_repr_cranelift
  VM=21
  CPS repr Cranelift=2
```

ignore 理由は更新した。

```text
all-rejected:
  write27-f: backtracking after all rejected choices still accepts a later value

two-nested-choices:
  write27-f: nested choice backtracking still exits with the last scalar value
```

## 残 frontier の観察

all-rejected の trace では、heap leak ではなく、最終的に outer case が `opt::just 2` を正常に unwrap
して `2` を返している。

つまり write27-f で直した「`opt::just` が root に漏れる」問題とは別で、backtracking / guard /
queue replay 側が、拒否されるべき値を有効解として扱っている。

気になる trace:

```text
guard false 相当の経路で 0 が返ったあと、
inner once / queue replay が続き、
最終的に opt::just 2 が outer once まで伝播している。
```

`guard: n > 10` では 1,2,3 すべて拒否されるはずなので、期待は `opt::nil -> 0`。
現状 Layer 3 は最後の `2` を解として採用している。

## ChatGPT Pro への質問

1. all-rejected が `2` になる原因は、`guard` / `reject` の blocked guard stack が resumption replay
   後に復元されていないことを疑うべきか。それとも `std::undet.once` の queue replay で `k false`
   を呼ぶ際の selected meta / anchor / return_frames の merge が、reject 後の continuation を
   誤って natural return として扱っている可能性が高いか。

2. `effectful_apply_resumption.out` の `new_frames` に、caller 側 frame と captured frame がかなり
   重複して見える。write27-e で handler stack 膨張は直ったが、return_frames 側にも
   all-rejected / nested choices を壊す余分な frame merge が残っていないか。

3. 次の切り分けとして、`guard` を使わず明示的に `if n > 10: n else: reject()` にした source と、
   `each [1,2,3]` を使わず source-defined `choice` + hand-written `once_dfs_int` で all-rejected を
   再現する source のどちらを先に固定するのがよいか。

## 確認したコマンド

```text
RUSTC_WRAPPER= cargo test -q -p yulang-native compares_prelude_source_opt_just_case_through_cps_repr_cranelift
RUSTC_WRAPPER= cargo test -q -p yulang-native compares_std_undet_once_value_arm_only_through_cps_repr_cranelift
RUSTC_WRAPPER= cargo test -q -p yulang-native compares_std_undet_once_scalar_unwrapped_through_cps_repr_cranelift
RUSTC_WRAPPER= cargo test -q -p yulang-native compares_std_undet_once_skips_rejected_first_choice_through_cps_repr_cranelift
RUSTC_WRAPPER= cargo test -q -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored
RUSTC_WRAPPER= cargo test -q -p yulang-native --lib
```

最終確認:

```text
171 passed; 0 failed; 15 ignored
```
