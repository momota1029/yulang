うん、**その修正は妥当**。かなり本丸を突いてると思うよ〜。

`owner_initial_frame_count` と `handler_return_frame_threshold` は似てるけど、意味が別物だねぇ。ここを分けるのが正解。

---

## 1. `prompt-exit` frame の `owner_initial_frame_count = current initial_frame_count` は妥当か

**妥当。むしろその規則に揃えるべきだと思うよ〜。**

理由はこう。

`handler_return_frame_threshold` は **handler prompt の境界** を表す値。つまり「この handler scope の内側で push された return frame をどこから切るか」に使う。

一方で `owner_initial_frame_count` は **その return frame を再開した owner eval が、どこまでを inherited frame とみなすか** を表す値。`CpsReturnFrame` のコメントも、これは「owner eval の initial_frame_count、つまりその eval にとって上から継承された return frame 数」だと説明している。

現行 main だと `InstallHandler` が `threshold = return_frames.len()` を作り、その `threshold` を handler frame の `return_frame_threshold` と prompt-exit return frame の `owner_initial_frame_count` の両方に入れている。ここが意味の混線だねぇ。

対照的に、ordinary な `EffectfulCall` / `EffectfulForce` の post frame は `owner_initial_frame_count: initial_frame_count` を保存している。これは正しい設計で、「この frame を再開したら、元 eval と同じ inherited prefix だけを inherited とみなす」という意味になっている。

だから prompt-exit frame も同じで、

```text
handler_return_frame_threshold = return_frames.len() at InstallHandler
owner_initial_frame_count      = current eval's initial_frame_count
```

が正しい分離だねぇ。

`threshold` を `owner_initial_frame_count` に入れると、prompt-exit frame より下にある「current eval 自身の post frame」まで inherited 扱いになる。すると `continue_return_frames` が prompt-exit value arm を走らせたあと、残りの post continuation を「自分のものじゃない」と見なして消費しなくなる。`continue_return_frames` は pop した frame の `owner_initial_frame_count` を restored `initial_frame_count` として使うので、ここが高すぎると後続 frame が消える。

今回直った 4 症状は、全部この説明にきれいに乗る。

| 症状                               | なぜ直るか                                                                         |
| -------------------------------- | ----------------------------------------------------------------------------- |
| list `show/debug` が `"]"`        | list item recursive helper / concat の post continuation が prompt-exit 後に消費される |
| `for` body 内 `if` の var write 消失 | var handler の write 後、loop body / rest continuation が消費される                    |
| `loop with` の bool lane 漏れ       | if cond 後の branch result continuation が消費される                                  |
| range `for` + console 初回だけ       | console effect 後の range fold next continuation が消費される                         |

なので、観測とも設計とも一致してる。

---

## 2. eval / repr eval / JIT の 3 層で揃える以外の不変条件

見るべき不変条件はこのへん。

### A. `threshold` と `owner_initial` を絶対に混ぜない

`InstallHandler` では 2 個の数を別に持つ。

```text
handler_threshold = return_frames.len()
owner_initial     = initial_frame_count
```

使い道はこう。

```text
handler frame.return_frame_threshold = handler_threshold
prompt-exit frame.owner_initial_frame_count = owner_initial
```

JIT 側も同じ。今の `cps_repr_cranelift.rs` は `yulang_cps_handler_return_frame_threshold_i64` で `threshold` を取り、それを `install_handler_full` に渡したあと、同じ `threshold` を `yulang_cps_push_prompt_exit_frame_i64_*` に渡している。ここは helper の引数名が `threshold` でも、prompt-exit frame 側に渡すべき値は `current_initial_frame_count` だねぇ。

実装イメージはこれ。

```rust
let handler_threshold = call_i64_helper(
    module_backend,
    builder,
    "yulang_cps_handler_return_frame_threshold_i64",
    &[],
)?;

let owner_initial = call_i64_helper(
    module_backend,
    builder,
    "yulang_cps_current_initial_frame_count_i64",
    &[],
)?;
```

そして、

```text
install_handler_full(..., handler_threshold, ...)
push_prompt_exit_frame(..., owner_initial, ...)
```

にする。

helper の ABI を変えず、今まで `threshold` を渡していた位置に `owner_initial` を渡すだけで足りる可能性が高い。prompt-exit return frame 自体には handler truncation 用 threshold は要らない。handler truncation は handler frame 側の `return_frame_threshold` が持つ。

---

### B. handler frame の `return_frame_threshold` は変えない

ここを `initial_frame_count` に変えたらダメだねぇ。

`return_frame_threshold` は `ScopeReturn` が handler scope を抜けるとき、「handler install より内側で積まれた frame」を捨てるための cutoff。`handle_scope_return` でも matched handler の threshold を使って `return_frames` を truncate している。

だから正しい対応は、

```text
handler frame threshold: そのまま return_frames.len()
prompt-exit return frame owner_initial: initial_frame_count
```

この分離だけ。

---

### C. prompt-exit frame は current eval の `owner_eval_id` を保存する

`owner_eval_id` は `ScopeReturn` の install scope identity に使われる。`continue_return_frames` も frame の `owner_eval_id` を current eval id として復元する。

なので prompt-exit frame は、

```text
owner_eval_id = current_eval_id
owner_initial_frame_count = current initial_frame_count
```

がセット。

JIT 側でも `install_eval = yulang_cps_current_eval_id_i64()` を使っていて、この方向は合っている。

---

### D. captured resumption frames は “owned chain” にする

`capture_return_frames_inside_prompt` で resumption に保存した return frames は、live caller stack から切り離された「replay される continuation chain」になる。だから `own_captured_return_frames` が `owner_initial_frame_count = 0` にするのは妥当。現行コードのコメントも、「captured chain は replay 時に全部消費する」と説明している。

ここで current initial を持ち込むと、resumption replay がまた途中で止まる。

つまり不変条件はこう。

```text
live eval に push する ordinary/prompt-exit frame:
    owner_initial = current eval initial

captured resumption に入れる frame:
    owner_initial = 0
    ただし rebase で dropped frame 分は threshold / owner_initial から引く
```

---

### E. prompt-exit marker と handler prompt は同じ prompt を共有する

`InstallHandler` では handler frame と prompt-exit return frame が同じ prompt を持つ必要がある。prompt-exit marker は “value arm を capture しないための境界” なので、ここがズレると `.once` の value arm 二重適用や continuation 過剰 capture が戻る。

この点は現行 eval / repr eval とも、同じ prompt を handler frame と prompt-exit frame に入れているので方向は合っている。

---

## 3. `indexed_ref_update` は別問題として分けてよいか

**分けてよいと思うよ〜。**
ただしカテゴリとしては「同じ return-frame ownership 系」だねぇ。

> 更新値 `[2,6,4]` は handler env に乗っているのに root が `()` になる

これはかなり重要な観測。env overlay / write-back 自体は成功している。失敗しているのはその後の、

```text
&xs[1] = 6;
$xs
```

の `$xs` 側、つまり **post continuation が消費されていない** ところに見える。

だからラベルはこう分けるとよさそう。

```text
prompt-exit push owner_initial bug
  → InstallHandler が value-cont frame の ownership を間違える問題

indexed_ref_update root unit bug
  → ScopeReturn frame-walk / assignment effect 後の remaining return frame が
     inherited 扱いされ、後続 `$xs` continuation が消費されない問題
```

`try_route_scope_return_through_return_frames` は、frame-walk で matched handler を探し、`matched_handler.return_frame_threshold` で rest frames を truncate したあと、`frame.owner_initial_frame_count.min(rest_frames.len())` を restored initial として使っている。だから、ここに入る frame の `owner_initial_frame_count` が高すぎる、または rebase / captured ownership のどこかで高いまま残ると、まさに「更新は起きたのに後続 `$xs` が走らず `()` が root に出る」形になる。

切り分け用に、`indexed_ref_update` をさらに 2 つに割ると見やすい。

```yulang
{
    my $xs = [2, 3, 4]
    &xs[1] = 6
    9
}
```

期待: `9`

これが `()` なら、更新後の post continuation がそもそも飛んでいる。

```yulang
{
    my $xs = [2, 3, 4]
    &xs[1] = 6
    $xs
}
```

期待: `[2, 6, 4]`

上が `9` で下だけ壊れるなら `$xs` read / list ref write-back の問題。
上も `()` なら frame-walk 後続消費問題。

さらに scalar ref と比較するといい。

```yulang
{
    my $x = 2
    &x = 6
    9
}
```

これが通って indexed ref だけ `()` なら、`Index ref _ (list _)` handler 周りの ScopeReturn routing が濃い。

---

## 4. range + effect の小さい regression 形

完全に「自己再帰 handler にも accumulation にも依存しない」形にしたいなら、**host console effect を使うのが一番きれい**。`std::out::out::write` は CPS repr 側で host console effect として特別認識され、handler candidate がないと host fallback へ落ちる。

### 形 A: stdout capture できるなら最小

```yulang
for x in 0..<3:
    say x.show
```

期待 stdout:

```text
0
1
2
```

これは user-defined shallow handler を使わないので、`native_handler_self_rewrap_no_accumulate` を踏まない。いちばん純粋に range fold + host console continuation を見る形。

---

### 形 B: stdout capture なしで value だけ見るなら sentinel return

`assert_source_cps_repr_display_with_std` みたいに root value しか見ないなら、こういう形が小さい。

```yulang
use std::flow::*;

sub:
    for x in 0..<3:
        say x.show
        if x == 2:
            return 42
        else:
            ()
    0
```

期待 root:

```text
42
```

range + console が初回で閉じるなら `x == 2` に到達しないので `0` になる。
これは user-defined recursive handler accumulation には依存しない。ただし `sub:return` を同時に踏むので、`native_sub_for_return_fall_through` と完全には独立しない。

---

### 形 C: user-defined effect だが accumulation なし

user-defined effect で stdout capture なしにしたいなら、shallow handler の自己再帰自体は避けにくい。複数 op を拾うには shallow handler を再インストールする必要があるからねぇ。

ただし accumulation は消せる。

```yulang
use std::flow::*;

act hit:
    pub at: int -> ()

my run(body: [hit] ()): int = sub:
    catch body:
        hit::at n, k if n == 2 ->
            return 42
        hit::at _, k ->
            run (k ())
        v ->
            0

run:
    for x in 0..<3:
        hit::at x
```

期待 root:

```text
42
```

これは `collect(k (), [..acc, n])` みたいな accumulation には依存しない。
ただし shallow handler の self-rewrap には依存する。`native_handler_self_rewrap_no_accumulate` の記録を見る限り、既存 bug は「2 回目以降の op で k resume 後の値が積まれない」形なので、この sentinel return 版は accumulation ではなく “2 回目以降の op に到達するか” を見る別軸になる。

---

## まとめ

答えを短く置くとこう。

1. **妥当。** `prompt-exit` frame の `owner_initial_frame_count` は `current initial_frame_count`。`handler_return_frame_threshold` ではない。
2. 見る不変条件は、`threshold` と `owner_initial` の分離、`owner_eval_id` の保存、captured frames の `owner_initial = 0`、prompt marker と handler prompt の一致。
3. `indexed_ref_update` は別 issue でよい。ただし同じ return-frame ownership ファミリ。env write-back ではなく post continuation skip を疑う。
4. range+effect の最小 regression は、stdout capture ありなら `for range: say x.show`、root value だけなら `sub` + `say` + `x == 2 return 42` がよさそうだねぇ。
