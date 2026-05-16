# JIT で `last` が break しない — open range が無限ループ化する原因

## 縮約観察

ignored になっている
`runs_open_range_for_loop_last_through_cps_repr` は

```yulang
use std::flow::*

{
    for x in 0..:
        if x == 5: last
        else: ()
    5
}
```

を JIT で走らせて `[5]` を期待しているけれど、実機ではメモリ食い尽くしまで
帰ってこない。

縮約してみた結果、症状は二段の話に分かれていそう：

| バリエーション | JIT 結果 | 意味 |
| --- | --- | --- |
| `for x in 0..<7: if x==5: last else: ()` | ✅ `[5]`（〜0.8s） | 偶然成功（range が短いだけ） |
| `for x in 0..<7: ()` | ✅ `[5]` | 7 回ループは普通に通る |
| `for x in 0..<100: ()` | ✅ `[5]`（〜1.1s） | 100 回もまだ通る |
| `for x in 0..<1000: ()` | 🛑 ハング | 1000 回でアウト（last 抜き） |
| `for x in 0..<10000: if x==5: last else: ()` | 🛑 ハング | `last` で抜けないので 10000 回回ろうとする |
| `for x in 0..: if x==5: last else: ()` | 🛑 ハング | open range も同じ理由 |

つまり：

1. **`last` が JIT 上で実際には break しない**（fold は range exhaustion まで継続）
2. **1 iteration あたりの JIT 当たりコストが線形以上で重い**（〜1000 iterations で実用不能）

`0..<7` の test がたまたま通っていたのは、`last` の有無に関係なく 7 回ループしきって `5` が返るから。`last` のセマンティクスを検証していたわけではない。

新しく ignored regression `runs_finite_range_for_loop_last_breaks_in_jit` を 1 件追加した（`0..<10000` で `last` 抜けが効くか）。これで「実際 break するか」を直接刺せる。

## 関連の構造

`std::flow::for_in` の定義（`lib/std/flow.yu`）：

```yulang
our for_in(xs, f: _ -> [loop] _) =
    last::sub:xs.fold (): \() x -> next::sub:loop true with:
        our loop b = if b: loop:redo::judge:catch f x:
            last(), _ -> last::break()
            next(), _ -> next::break()
            redo(), _ -> redo::break()
            loop::last(), _ -> last::break()
            loop::next(), _ -> next::break()
            loop::redo(), _ -> redo::break()
```

階層:

```
last::sub { (outer, once per for_in call)
    fold ... \() x ->
        next::sub { (per iteration)
            loop true with: loop b =
                if b: redo::judge {
                    catch (f x) {
                        loop::last(), _ -> last::break()  (<- here)
                    }
                }
        }
}
```

ユーザコード `last` は `loop::last` を perform → 内側 catch arm が `last::break()` を呼ぶ → これは `last::break` effect で、`last::sub` が catch する。`next::sub` は break を catch しない（pass-through）。`last::sub` の arm `break(), _ -> ()` が catch して fold 全体が unit で終わる。

これは prompt-3 §6 の "open range + last: threshold より abort 消費タイミングが濃い" の話そのもので、当時の見立ては：

> ScopeReturn / abort が caller chain を止める前に normal value として消費されている

要は `last::break()` の scope return が、

- `frame.install_eval_id != current_eval_id` のとき
- normal-value shortcut（`perform_finish_escaped_i64` / `arm_already_reached_escape` / RWH sibling shortcut）

のどこかで普通の値として消費されて、escape continuation に届かないまま fold が
次イテレーションに進んでいる、という線。

`route_scope_return` の構造を再確認すると：

- Path 1 `cur_match`：active handler stack を逆走、`install_eval_id == current_eval_id` を要求 → iteration eval が outer eval と違うので **必ず外れる**。
- Path 2 `frame_match`：return frames を逆走、各 frame の `handlers` snapshot を見て `install_eval_id == owner_eval_id && escape_owner_function_id == owner_function_id` を要求。

`last::sub` の install snapshot を保持している return frame が捕まれば Path 2 で escape。捕まらなければ propagate → そのまま value として戻る。

## 仮説

iteration ごとに `next::sub` が install され、`f x` の catch arm が `last::break()` を呼ぶ。このとき：

- iteration eval = inner（fresh）
- last::sub の install_eval = outer（fold caller）

Path 2 が成立する条件は「フレーム F があって `h.install_eval == F.owner_eval`」。`last::sub` の install snapshot を持つ return frame が `owner_eval == last::sub.install_eval` で存在しなければ成立しない。

`last::sub` install 時点の return frame は fold caller の owner_eval を持つ。それが iteration の captured slice の中に残っていれば見つかる。

`recalibrate_inherited_handler_thresholds` で threshold を slice 局所値に正しく揃えた直近 fix は、Path 2 マッチ条件（install_eval / owner_eval）には触れていない。なので Path 2 のマッチが成功しても、その後の truncate 振る舞いだけ正常化される。マッチ自体が失敗していると無関係。

優先で見るべきは：

1. **Path 2 frame_match が `last::sub` install を見つけているか**を trace で出す。
2. 見つかっているのに escape が走らない（abort / normal value 経路に逃げている）なら、`escape_continuation == 0` 早期返しか、`current_initial > 0 && post_handlers.is_empty()` の Global abort 化が悪さしている可能性。
3. 見つかっていないなら、iteration 中 `last::sub` の handler snapshot が return frames から消えている。fold の resumption capture が `last::sub` の install ev/own を保持していないか、`merge_extras_into_frames_native` が snapshot を上書きしている。

## 1 iteration コストの重さ

`for x in 0..<1000: ()` も hang する。つまり `last` 関係なく fold-and-resume の per-iteration cost が JIT で大きい。各 iteration が

- `next::sub` 用 prompt install
- handler env / guard stack push
- captured continuation 構築（fold callback の resumption）
- catch arm の continuation 登録

をやって、回収（uninstall + resumption drop）が遅れているとリニアに溜まる。

正攻法は trace で iteration ごとの

```
NATIVE_CPS_I64_RESUMPTIONS / RETURN_FRAMES / HANDLER_STACK
```

の長さを追って、定常状態ではなく単調増加していないかを見ること。増えていれば
どこかで `Box::from_raw` / `NATIVE_CPS_I64_RESUMPTIONS.remove` の漏れがある。

Layer 2 (`cps_repr.rs`) は eval ごとに local state を作るので同じ leak 問題は持たないはず（finite range + last のレギュレッションは通っているので、構造的にはこの差が支配的）。

## 提案する次の手

1. `runs_finite_range_for_loop_last_breaks_in_jit` で trace を取り、
   `route_scope_return.scan` / `route_scope_return: action=*` 行で
   `last::break` の prompt にマッチしているかを見る。
2. マッチしていないなら fold 中の iteration capture を見直す（`Perform` 時の
   `capture_handlers / capture_frames` で `last::sub` の install snapshot を
   失っていないか）。
3. マッチしているのに escape が走っていないなら、`route_scope_return` の
   Path 2 末尾の `if current_initial > 0 && post_handlers.is_empty()` で
   Global abort に追い込まれていないか確認。
4. iteration cost の方は、`yulang_cps_make_resumption_i64_*` の Box 生成と
   `NATIVE_CPS_I64_RESUMPTIONS` の HashSet 増加を 100 iter ごとにダンプして
   定常か単調かを見る。

## 残しておいた regression（両方 #[ignore]）

`crates/yulang-compile/src/lib.rs`:

- `runs_open_range_for_loop_last_through_cps_repr`：元の症状そのまま。
- `runs_finite_range_for_loop_last_breaks_in_jit`（新規）：
  `for x in 0..<10000: if x==5: last else: ()` で `last` が実際に break
  していれば数 iter で終わるテスト。
