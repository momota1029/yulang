うん、これはかなり良い進捗だねぇ。
そして、**続きはある** よ〜。でも次は「さらに機能を足す」より、まず **この到達点を壊れない成果に固める** のが大事かなぁ。

GitHub 上でも最新コミットは、`MakeRecursiveClosure` の self-reference が `Rc` snapshot のせいで壊れていたのを、`recursive_self: Option<CpsValueId>` と `ApplyClosure` 時の self patch で直し、`std::undet.once` の scalar-unwrapped regression が CPS eval / CPS repr eval / Cranelift JIT の全レイヤーで通った、と説明しているねぇ。さらに、`force_if_non_thunk_demand` と `InstallHandler` env population も入ったと書かれている。

つまり、これは **大きな山を越えた** と見てよさそう。

---

# まず結論

## 今すぐ次にやるべきこと

優先順位はこれ。

```text
1. デバッグ出力・暫定 ignore・計画メモを整理する
2. 今回のバグを小さい regression として固定する
3. std::undet.once の分岐探索が本当に queue/resumption を使っているか追加テストする
4. Cranelift JIT だけでなく object / executable / native-run でも確認する
5. その後に std::undet.list / logic / non-scalar print へ進む
```

今はもう `std::undet.once scalar-unwrapped` が通ったので、次に `.list` や `.logic` に突っ込みたくなるけど、ここで少し固めたほうがいいよ〜。

---

# 1. まず cleanup するべきもの

最新コミットの diff に、`eval_cps_module` でこういう debug print が入っているように見える。

```rust
eprintln!("[debug] root {} returned {value:?}", root.name);
```

これはそのまま残さない方がいい。

## 対応

どちらか。

### ふつうに消す

```rust
// remove debug eprintln
```

### あるいは cfg/debug flag にする

```rust
if std::env::var_os("YULANG_DEBUG_CPS_EVAL").is_some() {
    eprintln!("[debug] root {} returned {value:?}", root.name);
}
```

りなは、今は **消す** でいいと思う。必要になったら debug helper を別で作ればいいねぇ。

---

# 2. 今回のバグを小さい regression にする

今回の本当の原因は、`std::undet.once` そのものではなく、

> `MakeRecursiveClosure` が self-reference を `Rc` snapshot 後に patch していたため、closure 内部では self が `Unit` のままだった

というバグだよねぇ。

これは `std::undet.once` でしか検出できないと、あとでまた見つけづらい。
だから **recursive closure self-reference 単独テスト** を足したほうがいい。

## 追加したいテスト案

Yulang surface で簡単に書けるなら：

```rust
#[test]
fn compares_recursive_closure_self_reference_through_cps_repr_cranelift() {
    run_with_large_stack(|| {
        compare_source_cps_repr_i64(r#"
my sum_down n = if n == 0:
    0
else:
    1 + sum_down (n - 1)

sum_down 3
"#).expect("recursive closure self-reference");
    });
}
```

ただしこれが direct recursive function として lower されて `MakeRecursiveClosure` を踏まないなら、より local recursive closure っぽい形にする。

たとえば `with:` / `our loop` が必要なら：

```yulang
loop 3 with:
    our loop n = if n == 0:
        0
    else:
        1 + loop (n - 1)
```

実際の構文に合わせて調整。

## 目的

`std::undet.once` が通ることとは別に、

```text
MakeRecursiveClosure
ApplyClosure
recursive_self patch
```

だけを固定する。

このテストはかなり重要だよ〜。

---

# 3. `std::undet.once` の追加 regression

今通ったのはおそらくこれ。

```yulang
case (each [1, 2, 3]).once:
    nil -> 0
    just x -> x
```

これは大事だけど、`once` の queue が本当に機能しているかを見るには、**最初の枝を reject して次の候補へ進む** テストが必要。

`std::undet.once` の実装は、`branch(), k -> loop(k true, append queue [k])` で `k` を queue に入れ、`reject` したら `uncons queue` で `k false` を再開する構造だよねぇ。
だから、queue fallback を通すテストを追加する。

## 3.1 最初の候補を reject して 2 を返す

```rust
#[test]
fn compares_std_undet_once_skips_rejected_first_choice_through_cps_repr_cranelift() {
    run_with_large_stack(|| {
        compare_source_cps_repr_i64(r#"
use std::undet::*

case ({
    my x = each [1, 2, 3]
    guard (x > 1)
    x
}).once:
    std::opt::opt::nil -> 0
    std::opt::opt::just x -> x
"#).expect("std undet once skips rejected first choice");
    });
}
```

期待値は `2`。
これは `k true` で `1` を試して `guard false -> reject`、queue から `k false` を取り出して次へ、という経路を踏むはず。

## 3.2 解なし

```rust
#[test]
fn compares_std_undet_once_returns_nil_when_all_rejected_through_cps_repr_cranelift() {
    run_with_large_stack(|| {
        compare_source_cps_repr_i64(r#"
use std::undet::*

case ({
    my x = each [1, 2, 3]
    guard (x > 10)
    x
}).once:
    std::opt::opt::nil -> 0
    std::opt::opt::just x -> x
"#).expect("std undet once nil when all rejected");
    });
}
```

期待値は `0`。
これは queue を最後まで消費する経路を見る。

## 3.3 複数 choice

```rust
#[test]
fn compares_std_undet_once_two_choices_through_cps_repr_cranelift() {
    run_with_large_stack(|| {
        compare_source_cps_repr_i64(r#"
use std::undet::*

case ({
    my x = each [1, 2]
    my y = each [10, 20]
    guard (x + y > 12)
    x + y
}).once:
    std::opt::opt::nil -> 0
    std::opt::opt::just z -> z
"#).expect("std undet once with two choices");
    });
}
```

これは探索順に依存するけど、VM compare なら期待値を手で書かなくていいので安全。

---

# 4. `ListAppend` / `ListUncons` はまだ確認する

`std::undet.once` が通ったなら、現経路では必要な list 操作はどこかで動いている。
でも最新の first-class container commit では、`ListEmpty`, `ListSingleton`, `ListMerge` が CPS value list を直接構築する、と説明されていて、`ListAppend` / `ListUncons` は明示されていなかった。

だから確認してほしい。

## 確認ポイント

```bash
rg "ListAppend|ListUncons|list_append|list_uncons|yulang_cps_list" crates/yulang-native/src
```

見るべきこと:

```text
- CPS eval 側で ListAppend / ListUncons が CpsRuntimeValue::List を扱うか
- CPS repr eval 側も同じか
- Cranelift runtime 側で List に resumption pointer が入っても壊れないか
- VM primitive fallback に resumption を渡していないか
```

`std::undet.once` が通っているなら、おそらく `append` / `uncons` は std lib の関数経由で `ListMerge` / `ListIndex` / `ListLen` などに展開されている可能性もある。
でも、**resumption を含む list を VmValue に戻していないこと** は確認したほうがいいねぇ。

---

# 5. Cranelift JIT だけでなく object / executable も見る

最新コミットでは「all three eval layers」と書かれているけど、ここでいう三層は CPS eval / CPS repr eval / Cranelift JIT だねぇ。

次に確認すべきは object / executable。

## 5.1 object compile

既存の

```rust
compiles_std_undet_once_through_cps_repr_object
```

が復活しているなら、それは良い。
ただし object bytes が出るだけでは「実行」は見ていない。

## 5.2 CLI native-run-cps-repr-exe

scalar-unwrapped なら実行可能ファイルでも出力できるはず。

```bash
RUSTC_WRAPPER= cargo run -q -p yulang -- --native-run-cps-repr-exe <<'YU'
use std::undet::*

case (each [1, 2, 3]).once:
    std::opt::opt::nil -> 0
    std::opt::opt::just x -> x
YU
```

期待: `1`

これが通るなら、JIT だけでなく generated executable runtime でもかなり信用できる。

## 5.3 `--native-run`

fallback policy も見る。

```bash
RUSTC_WRAPPER= cargo run -q -p yulang -- --native-run <<'YU'
use std::undet::*

case (each [1, 2, 3]).once:
    std::opt::opt::nil -> 0
    std::opt::opt::just x -> x
YU
```

期待: CPS repr backend に fallback して `1`。

可能なら `--verbose-native` 的な backend 表示もほしいけど、まだなければ TODO に置く。

---

# 6. docs / plan の更新

`native-undet-plan.md` は更新したほうがいい。
今の GitHub 上の plan は、まだ「次は Phase B: first-class resumptions / closures flow through containers」と書いている状態に見える。
でも最新では、first-class containers と `std::undet.once scalar-unwrapped` まで進んでいる。

## 更新内容案

```text
Completed:
- Phase B/C/D: CPS evaluators have first-class List/Tuple/Variant containers.
- Resumptions can flow through CPS lists; resumption-in-list regression passes.
- Phase F: std::undet.once scalar-unwrapped passes through CPS eval, CPS repr eval, and Cranelift JIT.
- Recursive closure self-reference is fixed by deferred self patching at ApplyClosure time.

Open:
- Add queue-behavior regressions: rejected first choice, no solution, multiple choices.
- Confirm object/executable native-run-cps-repr path for std::undet.once scalar-unwrapped.
- Non-scalar CPS executable printing for opt/list results.
- std::undet.list and std::undet.logic.
```

`docs/native-backend.md` も同じように更新。

---

# 7. 次の大きい機能は `.list`

`once` の scalar-unwrapped が固まったら、次の自然な target は `.list`。
ただし `.logic` はまだ後回し。

標準実装では `.list` はこういう形。

```yulang
branch(), k -> std::list::merge list(k true) list(k false)
reject(), _ -> []
v -> [v]
```

`std::undet.yu` にその形があるねぇ。

`.list` は queue は使わないけど、結果が `list` なので non-scalar return / print に絡む。
まずは scalar に潰して確認するといい。

## `.list` scalar test

```rust
#[test]
fn compares_std_undet_list_len_through_cps_repr_cranelift() {
    run_with_large_stack(|| {
        compare_source_cps_repr_i64(r#"
use std::undet::*

({ each [1, 2, 3] }).list.len
"#).expect("std undet list len");
    });
}
```

期待値は `3`。
VM compare なので手書き不要。

次に sum できるなら、

```yulang
({ each [1, 2, 3] }).list.fold 0: \acc x -> acc + x
```

で `6`。

---

# 8. `.once` を non-scalar のまま返す

今は scalar-unwrapped。

```yulang
case (each [1,2,3]).once:
    nil -> 0
    just x -> x
```

次はこれ。

```yulang
(each [1,2,3]).once
```

これは `opt int` を native executable が print できる必要がある。
`cps_runtime.rs` には heap `Tuple` / `Variant` / `List` の print があるので、かなり近いはず。

ただし、この段階では root result が `RuntimeValuePtr` なのか `CpsHeapValuePtr` なのかをちゃんと扱う必要がある。
`compare_source_cps_repr_i64` は scalar 比較なので使えない。別の compare helper が必要。

## 新 helper 案

```rust
compare_source_cps_repr_value_debug(source)
```

または最初は executable 出力比較でもいい。

---

# 9. 彼に伝えるべきこと

そのまま渡すなら、こう。

```text
std::undet.once scalar-unwrapped が通ったのは大きい。次は新機能へ進む前に固めてください。

優先順位:
1. cps_eval.rs の debug eprintln が残っていれば消す。
2. MakeRecursiveClosure self-reference bug の小さい regression を追加する。
   std::undet.once 以外で recursive_self patch を検出できるようにする。
3. std::undet.once の追加 regression を入れる:
   - first choice rejected -> second result
   - all rejected -> nil branch
   - two choices -> VM compare
4. ListAppend / ListUncons が CpsRuntimeValue::List を扱っているか確認する。
   resumption を含む list を VmValue primitive fallback に渡していないこと。
5. JIT だけでなく object/executable/native-run-cps-repr-exe で scalar-unwrapped once を確認する。
6. native-undet-plan.md と docs/native-backend.md を更新する。
7. その後に std::undet.list の scalar projection、さらに non-scalar once printing へ進む。

禁止:
- すぐ logic に行かない。
- debug print を残したままにしない。
- std::undet.once だけで検出される recursive closure bug のままにしない。
- non-scalar print へ行く前に scalar-unwrapped queue behavior tests を飛ばさない。
```

---

# りなの判断

**続きはある。けど、次は攻めすぎない方がいい。**

今やるべきなのは、

```text
std::undet.once が「たまたま通った」から
std::undet.once が「ちゃんと壊れにくい」へ変える
```

ことだねぇ。

特に、今回の修正は `MakeRecursiveClosure` の self-reference というかなり根の深いバグだった。
これは `std::undet.once` 以外でも将来踏むので、小さい regression に切り出しておくのが一番価値が高いと思うよ〜。
