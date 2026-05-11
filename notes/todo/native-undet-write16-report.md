# native-undet-write16 実装レポート

## 実装したこと（write16 指示ベース）

### Step 1: trace 機構の追加

`cps_eval.rs` に env var (`YULANG_CPS_TRACE_FRAMES`) ガード付き trace を追加。
`Perform` / `Return` / `EffectfulApply` で `function`, `cont`, `return_frames.len`,
`initial_frame_count`, `active_handlers` を出力。

### Step 4: `once` 内の ApplyClosure を無条件 EffectfulApply 化

`FunctionLowerer` に `force_effectful_apply: bool` フラグを追加。
`std::undet::undet::once` 系統で true に設定。

`lower_apply` で:
```rust
if self.force_effectful_apply
    || (self.higher_order_helper && matches!(expr.ty, runtime::Type::Thunk { .. }))
```

これで `once__mono4` の cont 6 の `k true` / `loop k_thunk` / `(loop k_thunk) queue+[k]`
すべてが EffectfulApply terminator になった。
ダンプで cont 6, 9, 14, 18 の applies がすべて EffectfulApply に置き換わったことを確認。

### Step 5: EffectfulApply の Resumption frame order を修正

write16 §5 の指摘通り、`continue_return_frames` は末尾から pop するため、
post-call frame を末尾に置くと先に消費されてしまう。

修正前:
```rust
let mut combined_frames = resumption.return_frames.as_ref().clone();
combined_frames.extend(new_frames);  // F_post が末尾 = 先に pop
```

修正後:
```rust
// new_frames は parent_frames + [F_post]
let mut combined_frames = new_frames;
combined_frames.extend(adjusted_res);  // res_frames を末尾 = 先に pop
```

これで pop 順は: res_frames innermost → ... → res_frames outermost → F_post →
parent_frames。post-EffectfulApply の F_post が captured frames の完了後に実行される
ようになった。

---

## テスト状況

### 通った

- **既存 167 通常テスト** PASS（regression なし）
- **`debugs_local_choice_caller_rest_eval`** (write12) PASS
- **`debugs_local_choice_callback_rest_eval`** (write13 Test A) PASS

### まだ通らない

- **`debugs_std_undet_once_skip_eval_layers`** 引き続き `cps:3 vs vm:2`
  - write15 後と同じ結果。
  - Step 4-5 適用後、once の applies は EffectfulApply 化された。
  - しかしバックトラックは依然として 3 まで進む。

---

## 深掘りで判明した本質的な問題

write16 §3 の判定表に当てはめると、これは「**`x=2` の branch が `Perform` を起こしていない**」(分類 A) に該当する。trace で確認した branch Perform は **1回だけ** で、後続のイテレーションでは branch Perform が起きない。

### Trace 観察

```
Perform: branch ... return_frames.len=1 initial=0   ← 第1イテレーション
EffectfulApply: once cont 6 ...                      ← once branch arm
Return: ... List([Resumption(...)]) ...              ← queue + [k]
EffectfulApply: once cont 9 ...                      ← loop_k apply
Perform: sub::return ... return_frames.len=1         ← 第1イテレーションで sub::return
Return: each cont 2 value=Plain(Int("3"))            ← x=3 が返る！
```

**第1イテレーションで `sub::return` のはずが、なぜか値が `3` で返ってくる**。

### 根本原因の読み

`each` の `EffectfulCall fold_impl` で push される `F_each_post_fold` (= each cont 12)
は、fold_impl が `MakeThunk + Return` (cont 0) で「実体のない Thunk」を即座に Return
することによって、auto-Return-trigger で**すぐに消費される**。

その結果:
- fold_impl cont 12 (post-call cont) が `frames=[]` で動く
- cont 12 の `ForceThunk(thunk)` は sync stmt なので、thunk body の eval も
  `frames=[]` を継承する
- thunk body 内で実行される fold_impl の実体は `F_each_post_fold` を見ない
- したがって callback の `branch` Perform 時、resumption に
  `F_each_post_fold` (= reject() への分岐情報) が入らない
- これにより resumption replay が正しく動かない

### `EffectfulForce` で直す試み（失敗）

`EffectfulCall` 直後の force を sync `ForceThunk` から `EffectfulForce` terminator
に変えれば、thunk body の eval が post-force frame を継承するはず — と考えて修正
してみたところ、**cps:3 → cps:0 と悪化**した。

これは別の不変条件を壊した結果と思われ、`EffectfulForce` を導入するなら
return_frames の inheritance と handler frame の threshold 管理を更に詰める必要が
ある。今回は revert して cps:3 ベースラインに戻した。

---

## 触ったファイル

- `crates/yulang-native/src/cps_eval.rs`:
  - `trace_cps` ヘルパと env var guard
  - `Perform` / `Return` / `EffectfulApply` に trace
  - `EffectfulApply` Resumption case の frame order 修正
- `crates/yulang-native/src/cps_lower.rs`:
  - `FunctionLowerer.force_effectful_apply` フィールド
  - `std::undet::undet::once` で `force_effectful_apply = true`
  - `lower_apply` の判定に `force_effectful_apply` を追加

---

## りなに渡す質問

1. **`EffectfulCall` + `MakeThunk+Return` のパターン**:
   `each` が `EffectfulCall fold_impl` する → fold_impl は cont 0 で
   `MakeThunk + Return` → push された `F_each_post` が即座に consume される。
   このパターンは正しい？それとも `MakeThunk + Return` を避けるべき？

2. **`F_each_post` を thunk body に伝播させる方法**:
   - 案 A: 全てのこの種の sync `ForceThunk` を `EffectfulForce` 化（試したが回帰）
   - 案 B: EffectfulCall の eval で「callee が Thunk を返したら自動的に Force しつつ
     frame を保持」する特殊化
   - 案 C: `lower_root` で higher_order_helper には MakeThunk + Return ラップを
     しない
   - 案 D: 別の解

3. **trace の見方**:
   write16 §3 では「A: branch Perform が無い」「B: false が誤用」「C: ScopeReturn
   truncate が原因」を分類。実測は A だが、A の修正策（once での EffectfulApply 化）
   を入れても改善しなかった。これは A の中でも別種類の問題？

---

## コミット予定

write16 partial。
- 既存 167 通常テスト PASS（regression なし）
- write12/13 local tests 継続 PASS
- once の curried apply はすべて EffectfulApply に。Resumption frame order 修正。
- trace 機構追加（env var guard 付き）
- `debugs_std_undet_once_skip_eval_layers` は依然として cps:3 vs vm:2
  - 原因は EffectfulCall + MakeThunk+Return が F_each_post を即時消費するため
  - 次の write17 で「F_each_post を thunk body の eval に伝播させる」設計が必要
