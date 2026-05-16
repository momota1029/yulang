# render sink leak 修正後に残った `junction + undet` native CPS 値違い

`answer-1.md` の方針に沿って、まず runtime lowering の
`render / Display / Debug / statement sink` と semantic join の混線を切った。

## 入れた修正

runtime lowering の `implicit_cast_method_path(actual, expected)` で、次の場合は
`Cast` role method を runtime expr に即時挿入しないようにした。

```text
actual または expected が open
  - Any
  - TypeVar
  - Unknown を含む
  - type var を含む

actual と expected が相互 compatible
  - identity / no-op と見なせる
```

直接のデバッグログでは、失敗時にこういう adapter が入っていた。

```text
runtime implicit cast
  source   = JoinEvidence
  actual   = Var(t2988)
  expected = Var(t2988)
  cast     = std::prelude::&cast#765::cast
```

`std::prelude::&cast#765::cast` は `Cast path -> bytes` 由来の実装で、
open identity join に対して全く無関係な cast が選ばれていた。
その結果、`std::list::fold_impl__mono9` の match arm body に `bytes` が混ざり、

```text
branch result type mismatch: expected unit, got std::bytes::bytes
```

になっていた。

ただし、単に cast を挿入しないだけだと effectful branch arm が thunk のまま残り、
以前と同じ `["1"]` 系の値違いに戻った。そこで `JoinEvidence` は semantic value
boundary と見なし、expected が open (`Any` / `Var`) でも thunk branch arm は force
するようにした。

要するに今の切り分けはこう。

```text
open Cast:
  semantic cast evidence としてはまだ使わない

JoinEvidence:
  render/discard sink ではないので、effectful arm は値へ force する
```

## 追加した小さい regression

```yulang
my choose x = if true: x else: x
choose ()
```

これは以前、

```text
branch result type mismatch: expected unit, got std::bytes::bytes
```

で落ちていた。今は VM regression として通る。

## 通ったテスト

```bash
cargo fmt --check
cargo test -q -p yulang-runtime vm_keeps_open_identity_join_from_using_unrelated_cast -- --nocapture
cargo test -q -p yulang-runtime vm_selects_cast_by_annotation_target -- --nocapture
cargo test -q -p yulang-runtime vm_inserts_cast_at_if_branch_boundary -- --nocapture
cargo test -q -p yulang-compile runs_simple_undet_list_through_cps_repr -- --nocapture
cargo test -q -p yulang-compile runs_undet_once_open_range_guard_through_cps_repr -- --nocapture
cargo test -q -p yulang-compile runs_var_update_in_for_loop_through_cps_repr -- --nocapture
```

既存の annotation target cast / if branch cast は壊れていない。
`undet.list`、open range + `guard` の `.once`、for loop var update も通る。

## まだ落ちるテスト

```bash
cargo test -q -p yulang-compile runs_junction_method_undet_once_through_cps_repr -- --nocapture
```

ソースはこれ。

```yulang
use std::undet::*

struct point { x: int, y: int } with:
    our p.norm2: int = p.x * p.x + p.y * p.y

({
    my y = if all [1, 2, 3] < any [2, 3, 4]:
        each [3, 4, 5]
    else:
        2

    point { x: 3, y: y } .norm2
}).once
```

VM / interpreter 側は期待通り。

```text
[0] just 18
```

native CPS 系の compile test では runtime validation は通るようになったが、
最初の CPS eval display layer で次のように落ちる。

```text
unexpected CPS eval display result: ["1"]
```

trace tail は概ねこれ。

```text
HandlerEnvRead { layer: CpsEval, function: "std::junction::junction::any__mono7", handler: 4, entry: 18, values: [] }
HandlerEnvRead { layer: CpsEval, function: "std::junction::junction::junction__mono3", handler: 0, entry: 4, values: [] }
HandlerEnvRead { layer: CpsEval, function: "std::junction::junction::all__mono6", handler: 3, entry: 18, values: [] }
HandlerEnvRead { layer: CpsEval, function: "std::junction::junction::junction__mono3", handler: 0, entry: 5, values: [] }
```

## 質問

1. 今の `open Cast は即時 runtime adapter にしない`、かつ
   `JoinEvidence は open result でも thunk arm を force する` という切り分けは、
   `answer-1.md` の invariant として妥当か。

2. `runs_junction_method_undet_once_through_cps_repr` の残りの `["1"]` は、
   render-sink leak ではなく、`junction` handler と `undet.once` handler の合成における
   CPS eval / continuation capture の値違いと見てよいか。

3. `all [1,2,3] < any [2,3,4]` の `junction` handler と、
   then branch の `each [3,4,5]` を外側 `.once` が捕まえる構造で、
   shallow handler / `sub::return` / fold callback continuation のどの境界を
   まず疑うべきか。

4. この値違いを切るために、次に入れるべき trace / invariant は何か。
   候補としては次を考えている。

```text
- handler install prompt / handled effect / value arm result type
- perform capture 時の handler prompt と captured return segment
- resume 時に再導入される handler stack
- `std::flow::sub::return` がどの prompt に route されたか
- fold callback の thunk force / join result / continuation return value
```

5. `["1"]` という結果は、どの値が早く root へ漏れていると読むのが自然か。
   `junction` の boolean result が外側の `.once` の body result を短絡しているのか、
   それとも `each` の最初の値 `3` へ進む continuation が落ちているのか。
