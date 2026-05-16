うん、ここまで来ると **prompt ownership 修正で片づく層はほぼ抜けた** と見てよさそうだねぇ。残りは大きく 4 ファミリに分けるのがよさそう。

`3e038e1` は、prompt-exit frame の `owner_initial_frame_count` 分離、captured continuation の handler threshold rebase、RWH env 差し替え時の inherited escaped finish normal-value 扱い、unit root display hint を入れている差分だねぇ。commit message と README 追記もその意図に沿っている。

---

# 残り 5 件 + open range の分類

| 失敗                                                               | 主分類                                                                  | まず疑う場所                                                                                 |
| ---------------------------------------------------------------- | -------------------------------------------------------------------- | -------------------------------------------------------------------------------------- |
| `junction_condition_without_once` が `18` ではなく `1`                | **handled effect result が if condition continuation へ戻らず root へ漏れる** | `lower_handled_effect_condition_if` / `Perform` 後の normal result wrapping / value_cont |
| `recursive_effect_handler_tuple_result` が JIT だけ `(thunk@..., )` | **JIT の force boundary / aggregate materialization**                 | `ForceThunk` lowering、`yulang_cps_return_i64`、tuple item runtime-value conversion      |
| `undet_logic_each` が root plain conversion error                 | **root plainness ではなく queue/res env leak の可能性あり**                    | root return の実体が Thunk か List<Resumption> かを先に判定                                       |
| nested `.list` が JIT だけ `[11, 20]`                               | **JIT の resumption replay / handler env accumulation**               | RWH sibling env、captured frame/env overlay、JIT runtime helpers                         |
| nested `.logic` が CPS eval から `[11,10,20,3,20]`                  | **eval 層の resumption captured continuation 欠落 / replay 順序**          | `capture_continuation_inside_prompt`、return frame capture、anchor merge                 |
| open range + `last` が memory exhaustion                          | **non-local abort が fold recursion を止めていない**                         | `ScopeReturn` routed jump の消費タイミング、abort propagation                                   |

---

# 1. `junction_condition_without_once`: prompt ownership ではなく “condition continuation leak”

これは **eval 層から `["1"]`** だから JIT 以前。
`std::junction` は `any/all` が `sub::return` と `ret` effect を使い、`junction(x)` handler が `or/and/ret` を処理して bool を返す構造だねぇ。

`if all [2] < any [3]: 18 else: 2` で `1` が root に出るということは、

```text
junction handler が bool true を返す
↓
その bool が if condition continuation に渡らず
↓
root result として終わる
```

になっている。

これは `ScopeReturn` ownership というより、**handled expression が condition position にいるとき、handler result を `cond_cont` に入れて branch continuation を続ける不変条件** の破れ。

見るべき不変条件はこれ。

```text
effectful condition の値 result は、絶対に root / enclosing handler value arm へ直返ししない。
必ず condition continuation に渡して、その後 Branch が then/else を選ぶ。
```

最小 regression はこれがいい。

```yulang
act done:
    pub ret: bool -> never

my run(x: [done] bool): bool = catch x:
    done::ret b, _ -> b

if run: done::ret true:
    18
else:
    2
```

期待 `18`。
これが `1` なら junction 以前の “handled effect in condition” bug。

次に direct-call 版。

```yulang
act done:
    pub ret: bool -> never

my run(x: [done] bool): bool = catch x:
    done::ret b, _ -> b

my pred(): [done] bool = done::ret true

if run(pred()):
    18
else:
    2
```

こっちだけ落ちるなら `EffectfulCall` の post frame / condition value_cont 周り。

実装で見る場所は、`cps_lower.rs` の `lower_handled_effect_condition_if` と、`cps_eval.rs` の `Perform` 終了処理。`Perform` では handler arm の result を `ScopeReturn` に包む経路と、inherited + RWH の normal value 返し shortcut がある。この shortcut は RWH 差し替え用には必要だけど、condition continuation を飛ばすほど広くなっていないかを見るべきだねぇ。現行 `Perform` は resumption を作って handler arm を eval し、その後 `frame.install_eval_id != current_eval_id && handler_arm_uses_resume_with_handler(...)` なら plain result を返す分岐を持つ。ここが condition result を root に逃がしていないかが第一候補。

---

# 2. `recursive_effect_handler_tuple_result`: JIT の責務から追う

これは **JIT actual だけ `(thunk@..., )`** なら、CPS eval / CPS repr eval の意味論は一旦信用していい。
だから責務としては **JIT が既存の force 境界を再現できていない** 方向から追うのが自然。

`cps_lower.rs` の root lowering は、root result が non-thunk demand なら `ForceThunk` を入れる。さらに `force_if_non_thunk_demand` は “effectful helper が Thunk を返す場合に consumer 側で明示 ForceThunk を入れる” とコメントされている。

なので、切り分けはこう。

## A. CPS IR に `ForceThunk` があるか

`YULANG_TEST_DUMP_CPS=1` で failing test の CPS を見る。

* tuple item に入る前に `ForceThunk` がある
  → JIT の `ForceThunk` / return pre-force / tuple materialization が悪い。
* tuple item に入る前に `ForceThunk` がない
  → lowerer 側の semantic demand 境界が足りない。ただし CPS eval が通るなら、eval 側の implicit ForceThunk に救われている可能性もある。

## B. JIT の `ForceThunk` が result を normal value として戻しているか

JIT の `ForceThunk` stmt は `yulang_cps_force_thunk_i64` を呼び、abort / scope-return を処理してから dest に入れる形になっている。ここ自体は意図に沿っている。

疑うならこのへん。

```text
ForceThunk result が tuple item の value id に bind されず、元 thunk id を tuple に読んでいる
EffectfulCall / Return pre-force で thunk を value として返してしまう
tuple construction の read_runtime_value_i64 が ThunkPtr lane をそのまま runtime value として格納している
```

最小 regression は、recursive accumulation を抜いて **handler arm が `k ()` の値を tuple に入れるだけ** にする。

```yulang
act ping:
    pub p: () -> ()

my run(x: [ping] int): (int, int) = catch x:
    ping::p _, k -> (k (), 0)
    v -> (v, 0)

run:
    ping::p ()
    9
```

期待 `(9, 0)`。

これが JIT だけ `(thunk@..., 0)` なら、tuple item の force 境界/JIT materialization が確定。
これが通って recursive 版だけ落ちるなら、force ではなく RWH/env accumulation や recursive handler return path に戻る。

---

# 3. `undet_logic_each`: “root forcing” と決め打ちしない方がいい

`ExpectedPlainValue root_0 CpsValueId(MAX)` だけだと、root value が何だったか分からない。ここはまず **root value の実体を出す** のが大事。

`std::undet.logic` は `queue` に resumption `k` を入れて、`res` に plain value を貯める BFS っぽい構造だねぇ。`branch` で `k true` を走らせつつ `queue` に `k` を積み、`reject` や value arm で queue から `k false` を再生する。

だから root conversion error は 2 パターンある。

```text
A. root が Thunk のまま
   → root forcing / ForceThunk boundary 問題

B. root が List<Resumption> や Tuple/Record 内 Resumption を含む
   → queue が res として漏れた、handler env / pattern binding / continuation routing 問題
```

`undet.logic` は queue に resumption を持つので、B の可能性が高い。
特に `logic` だけが plain conversion errorで、`.list` は通るなら、root forcing より **queue/res env の取り違え** を先に疑う。

最初に instrument する場所は `eval_cps_module` の root conversion 手前。

```rust
let value = with_fresh_handler_env_overlay(|| eval_function(...))?;
eprintln!("root {} = {}", root.name, summarize_cps_value(&value));
```

判断:

| root summary                                | 次に見る場所                                                  |
| ------------------------------------------- | ------------------------------------------------------- |
| `Thunk(...)`                                | `lower_root` / `.logic` call result demand / ForceThunk |
| `Resumption(...)`                           | handler value arm or queue leak                         |
| `List(len=..., [Resumption...])`            | `logic` の queue が root に漏れている                           |
| `List(len=..., [Plain...])` だが conversion失敗 | list element の一部だけ opaque                               |

最小 regression は段階的に。

```yulang
use std::undet::*
(branch()).logic
```

期待 `[1, 0]` 相当。

```yulang
use std::undet::*
(each [1, 2]).logic
```

期待 `[1, 2]`。

`branch().logic` から plain conversion が落ちるなら、queue/res の基本経路。`each [1,2]` だけ落ちるなら `each` の fold/sub:return との合成。

---

# 4. nested undet は “resumption replay の捕獲 slice / env freshness” として分ける

nested `.logic` が CPS eval から壊れているので、JIT ではなく eval semantics。

`[11, 10, 20, 3, 20]` みたいに raw `10` / `20` / `3` が混ざるのは、かなり特徴的。
これは `x + y` の continuation が毎回再生されていない、または outer `x` / inner `y` の captured values が古い/欠けているサインだねぇ。

つまり疑う不変条件はこれ。

```text
branch の resumption k は、branch() の直後だけではなく、
branch value を使う残りの expression continuation を保持する。
例: each [1,2] + each [10,20] なら、
inner/outer の branch resumption は必ず “+ の残り” を含む。
```

現行の `Perform` では、handler match 後に `capture_continuation_inside_prompt(&handler_stack, &return_frames, frame)` で resumption の handler stack と return frames を作る。captured return frame slice は prompt-exit marker の直後からになり、handler stack threshold も rebase されている。

この方向自体は正しいけど、nested undet の raw value 混入は次のどちらか。

## A. capture slice が狭すぎる

`branch()` が `x + y` の途中で perform したのに、`+` の post continuation frame が `return_frames` に入っていない。

この場合 `k false` が `false branch value` だけ返して、`+ outer` まで戻らない。
`[11, 10, 20, 3, 20]` の raw `10/20/3` はこの匂いが強い。

見る点:

* `begin_resume_after_perform` で resume continuation が “rest of expression” を持っているか。
* `Primitive(IntAdd)` の引数内 effect (`each` / `branch`) を扱うとき、post-add continuation が return frame ではなく same continuation 内の local stmt として残っていないか。
* effectful direct/apply only で frame が積まれ、primitive arg effect では frame が積まれない、みたいな差がないか。

## B. captured values / handler env が古い

queue に入れた `k` を後から replay するとき、`x` や `queue/res` が capture 時点のままか、resume-site update と混ざりすぎている。

`merge_resumption_handlers` は anchor を使って current handlers を captured prefix と captured tail の間に入れる設計。コメント上は `[outer, H_inner, H_sub]` のような配置を狙っている。

ただし nested logic では queue に複数の `k` が入り、`res` も更新され続ける。だから handler env overlay が “最新 env を全 resumption に適用” しすぎると順序・値が崩れる。

最小 regression は 2 軸で分けるといい。

```yulang
use std::undet::*
(each [1] + each [10, 20]).logic
```

期待 `[11, 21]`。
これが壊れるなら inner branch replay が壊れている。

```yulang
use std::undet::*
(each [1, 2] + each [10]).logic
```

期待 `[11, 12]` か実装の BFS 順に合わせた結果。
これが壊れるなら outer branch replay が壊れている。

```yulang
use std::undet::*
(each [1, 2] + 10).logic
```

期待 `[11, 12]`。
これが壊れるなら nested 以前に single `each` の post-add continuation capture が壊れている。

---

# 5. nested `.list` が JIT だけ `[11, 20]`

これは `.logic` と同じ nested continuation 問題に見えるけど、JIT だけなら別ファイルに分けた方がいい。

`std::undet.list` は `branch(), k -> merge list(k true) list(k false)` で DFS 的に全部集める。

`[11, 20]` は「最初の `11` は作れたが、次の replay で `x + y` の `x +` 部分が抜けて raw `20` が出た」っぽい。つまり eval/repr eval が通るなら、JIT の resumption replayが captured return frame / env を完全には復元していない。

見る場所は JIT runtime helper 側。

* `yulang_cps_resume_i64`
* `yulang_cps_effectful_apply_resumption_i64_*`
* `yulang_cps_continue_return_frame_i64`
* `yulang_cps_capture_handler_env_mapped_i64`
* `yulang_cps_selected_handler_env_or_i64`

`3e038e1` では RWH sibling env source を検出して inherited escaped finish を normal value 扱いにする修正も入っている。JIT 側では `NATIVE_CPS_I64_SELECTED_HANDLER_USED_RWH_ENV` が追加され、`perform_finish_escaped_i64` で `meta.install_eval_id != current_eval && used_rwh_env` のとき normal value を返すようになっている。

この shortcut が nested undet `.list` に過剰適用されている可能性は見る価値あり。
特に JIT only なら、

```text
selected_handler_env_or_i64 が RWH sibling env を読んだ
↓
perform_finish_escaped_i64 が normal value として返した
↓
本来 ScopeReturn として戻るべき continuation chain が切れた
```

という形がありえる。

---

# 6. open range + `last`: threshold より abort 消費タイミングが濃い

trace で `x == 5` と `last` handler selection まで届いているなら、

```text
handler lookup
effect selection
guard / condition
```

までは通っている。

それでも fold recursion が止まらないなら、濃いのは **ScopeReturn / abort が caller chain を止める前に normal value として消費されている** ところ。

owner_initial / threshold が主因なら、もっと “後続 continuation が飛ばない/飛びすぎる” 形になりやすい。open range で memory exhaustion へ向かうのは、`last` が「loop を抜ける non-local exit」にならず、fold の recursive step が続いているということ。

見る順はこれ。

1. `last` arm result が `ScopeReturn` になるか。
2. `handle_scope_return` が matching handler に当たるか。
3. `JumpOrExit` 後、return frame を truncate した上で **outer fold caller へ normal value を返していないか**。
4. `arm_already_reached_escape` / inherited RWH normal value shortcut が `last` 系にも当たっていないか。
5. `continue_return_frames` が `ScopeReturn` / `Aborted` を untouched で返す不変条件を破っていないか。

finite 版を先に置くと見やすい。

```yulang
use std::flow::*;

{
    for x in 0..<10:
        if x == 5:
            last
        else:
            ()
    42
}
```

期待 `42`。

open 版だけ壊れるなら、`last` の non-local exitは一応動くが、open range fold の recursive thunk / tail recursion の force timing が別に壊れている。
finite 版も壊れるなら `last` abort propagation 本体。

---

# 次に直す順

おすすめはこの順。

## Step 1: `junction_condition_without_once`

理由: eval 層、snippet が小さい、undet より状態が少ない。
ここで “handled effect result must re-enter condition continuation” を直すと、undet nested の一部も改善する可能性がある。

追加 regression:

```yulang
act done:
    pub ret: bool -> never

my run(x: [done] bool): bool = catch x:
    done::ret b, _ -> b

if run: done::ret true:
    18
else:
    2
```

次に direct-call condition 版。

---

## Step 2: simple `.logic` の root value 実体判定

`ExpectedPlainValue` だけでは情報が足りないので、root conversion 直前に `summarize_cps_value` を出す。
Thunk なら root force、List<Resumption> なら queue/res leak。

追加 regression:

```yulang
use std::undet::*
(branch()).logic
```

```yulang
use std::undet::*
(each [1, 2]).logic
```

---

## Step 3: single `each + constant` で post-continuation capture を見る

nested に行く前に、branch の resumption が “残りの式” を持っているかを見る。

```yulang
use std::undet::*
(each [1, 2] + 10).logic
```

期待 `[11, 12]` 系。

これが raw `[1,2]` や `[11,2]` になるなら、`+ 10` continuation capture が足りない。

---

## Step 4: nested `.logic` eval 層

ここで初めて、

```yulang
use std::undet::*
(each [1] + each [10, 20]).logic
```

と

```yulang
use std::undet::*
(each [1, 2] + each [10]).logic
```

に分ける。

inner replay と outer replay を別々に見る。

---

## Step 5: JIT-only thunk tuple

eval/repr eval が通ることを確認してから JIT に限定。
最小はこれ。

```yulang
act ping:
    pub p: () -> ()

my run(x: [ping] int): (int, int) = catch x:
    ping::p _, k -> (k (), 0)
    v -> (v, 0)

run:
    ping::p ()
    9
```

これが JIT だけ thunk pointer なら、`ForceThunk` / tuple materialization / return pre-force のどれか。

---

## Step 6: JIT-only nested `.list`

eval/repr eval が安定してから JIT helper を見る。
`selected_handler_env_or_i64` の RWH sibling source と `perform_finish_escaped_i64` の normal-value shortcut を trace に出すとよさそう。

---

# まとめ

今の残りはこう見るのが一番きれい。

```text
prompt ownership:
  3e038e1 でかなり解決済み

condition handler result leak:
  junction_condition_without_once

root plainness / queue leak:
  undet_logic_each

resumption replay capture:
  nested undet logic

JIT env / replay parity:
  nested undet list

JIT force / aggregate materialization:
  recursive_effect_handler_tuple_result

non-local abort propagation:
  open range + last
```

次の一手は **junction の最小 “handled effect in if condition”** だねぇ。ここは undet よりずっと状態が少なくて、eval 層の “handler result をどの continuation に戻すか” を刺せる。これが直った後に `.logic` の root 実体を出すと、undet が root forceなのか queue/res leakなのか一気に分かるはず。
