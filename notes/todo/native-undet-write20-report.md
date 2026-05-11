---
title: native-undet-write20 実装レポート
date: 2026-05-11
---

# native-undet-write20 実装レポート

## 結論（先に）

write20 で本命と提示された **case A（recursive loop に渡す `k true` が eager
replay されている）**は、trace と lowering audit の両方で **完全に否定された**。

write20 §case A の「最有力修正」（`lower_apply` で thunk-typed param に
`lower_expr_as_thunk_value` を使う）は **既に施されており、trace でも機能している**。
コードに加える修正は今回ない。

残バグは write19 で報告した **case D 派生（intermediate handler eval destruction）**
が真因。`sub::return` の ScopeReturn propagation が、本来生きているべき
inner once eval（recursive loop の handler scope, prompt=2）を巻き込んで破壊
している。これは構造的問題で、write21 で semantics レベルの設計判断が必要。

---

## baseline 確認（step 0）

```text
cargo test -p yulang-native                                  => 167 pass
cargo test -p yulang-native debugs_local_choice_caller_rest_eval -- --ignored
  => pass
cargo test -p yulang-native debugs_local_choice_callback_rest_eval -- --ignored
  => pass
cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored
  => fail: ValueMismatch { vm: Int("2"), cps: Int("0") }
```

write18 後の期待値どおり。

---

## trace 観察（step 1, step 3 実行）

`YULANG_CPS_TRACE_FRAMES=1` で取得した trace（`/tmp/write20_trace.log`、62 行）の
重要部分を時系列で整理。

```text
L26  InstallHandler  fn=once__mono4 handler=#1 prompt=0 escape=cont5 threshold=1   ← outer once
L34  InstallHandler  fn=each__mono1 handler=#0 prompt=1 escape=cont2 threshold=1   ← H_sub
L46  Perform branch  fn=each__mono1 cont=5 active_handlers=[(0,T,1),(1,T,0)]
L47  EffectfulApply  fn=once__mono4 cont=6
       callable=Closure(loop, entry=cont2, recursive_self=Some)
       arg=Thunk(owner=once, entry=cont8)                                          ← ★ k true は Thunk
L48  Return          fn=once cont=2 value=Closure(loop_partial)
L50  PrimitiveList   ListSingleton -> List(len=1, [Resumption])
L51  PrimitiveList   ListMerge     -> List(len=1, [Resumption])
L54  EffectfulApply  fn=once__mono4 cont=9
       callable=Closure(loop_partial, entry=cont3)
       arg=List(len=1, [Resumption])                                               ← queue2
L55  InstallHandler  fn=once__mono4 handler=#1 prompt=2 escape=cont5 threshold=1   ← ★ 再帰 once 起動
L56  Perform sub::return fn=each cont=8 active_handlers=[(0,T,1),(1,T,0),(2,T,1)]
L58-63 ScopeReturnDispatch prompt=1 を 6 frames Propagate
       fn=each   Propagate
       fn=once   Propagate    ← inner once eval (prompt=2) を貫通
       fn=once   Propagate
       fn=each   Propagate
       fn=fold_impl Propagate
       fn=each   matched=yes owner_match=yes threshold=1 JumpOrExit
L64  Return          fn=each cont=2 value=Plain(Int("1"))
L65-68 work で gt(1,1)=false 計算
L69  Perform reject  fn=guard cont=4 active_handlers=[(0,T,1)]                     ← ★ outer once しか残ってない
L70  PrimitiveList   ListLen [List(len=0,[])] -> Int("0")                          ← uncons の入力 queue=[]
L73  Return          uncons -> Variant(nil)
L74  Return          once cont=5 (reject arm) value=Variant(nil)
L77  ScopeReturnDispatch fn=once prompt=0 matched=yes JumpOrExit
L81  Return          root cont=2 value=Plain(Int("0"))
```

### 確定事実

1. **`k true` は Thunk として渡されている**（L47）— case A 否定
2. **recursive loop は起動し、handler を install している**（L54, L55）— case A/B 否定
3. **queue2 は `List(len=1, [Resumption])` で正しく構築されている**（L51）— case B 否定
4. **`sub::return` propagation が 6 frames を貫通する間に、prompt=2 の
   inner once eval frame が `Propagate` されて消滅する**（L58-63）
5. **その後の `reject` Perform 時点で active_handlers から prompt=2 は失われ、
   outer once しか残っていない**（L69）
6. outer once の reject arm が env queue=`[]`（初期値）で動き、uncons nil → 0

---

## case A の lowering audit（step 3）

write20 §case A の修正手順「`lower_apply` で第一引数型を見て Thunk なら
`lower_expr_as_thunk_value` を呼ぶ」が **既に実装されている**ことを確認した。

### `cps_lower.rs::lower_apply` (L1582-1619)

```rust
fn lower_apply(...) -> ... {
    let closure = self.lower_expr(callee)?;
    let arg = self.lower_expr_as_call_arg(&callee.ty, arg)?;  // ★
    if self.force_effectful_apply
        || (self.higher_order_helper && matches!(expr.ty, runtime::Type::Thunk { .. }))
    {
        // ... EffectfulApply terminator (引数 lowering には touch しない)
    }
    // ... ApplyClosure stmt path
}
```

### `cps_lower.rs::lower_expr_as_call_arg` (L1625-1640)

```rust
fn lower_expr_as_call_arg(&mut self, callee_ty: &runtime::Type, arg: &runtime::Expr)
    -> CpsLowerResult<CpsValueId>
{
    let param_ty = match callee_ty {
        runtime::Type::Fun { param, .. } => Some(param.as_ref()),
        _ => None,
    };
    let param_is_thunk = matches!(param_ty, Some(runtime::Type::Thunk { .. }));
    if param_is_thunk {
        self.lower_expr_as_thunk_value(arg)  // ★ MakeThunk wrapper
    } else {
        self.lower_expr(arg)
    }
}
```

### `cps_lower.rs` direct_apply path (L1280-1334)

```rust
let args = args.into_iter().enumerate().map(|(idx, arg)| {
    if matches!(info_params.get(idx), Some(runtime::Type::Thunk { .. })) {
        self.lower_expr_as_thunk_value(arg)  // ★ MakeThunk wrapper
    } else {
        self.lower_expr(arg)
    }
}).collect::<_>()?;
```

### `force_effectful_apply` の影響範囲

`lower_apply` 内で `force_effectful_apply` が分岐するのは **L1596-1608 の
terminator 化判定のみ**で、`lower_expr_as_call_arg` の呼び出し前後で
引数 lowering を変えていない。write20 が懸念した「`force_effectful_apply` が
引数 thunking を潰す」現象は **存在しない**。

trace の L47 で `arg=Thunk(owner=once, entry=cont 8)` が確認できることも、
この経路が実際に機能している証拠。

---

## case 判定（step 2）

| Case | 説明 | trace との一致 | 状態 |
|------|------|--------------|------|
| A | k true が eager replay されて recursive loop が呼ばれない | ✗ trace L47 で Thunk 確認 / L55 で recursive loop install 確認 | 否定 |
| B | recursive loop は呼ばれるが queue=[] | ✗ trace L50-54 で queue=[Resumption] 構築・伝達確認 | 否定 |
| C | queue=len1 だが uncons nil（List primitive bug） | ✗ trace L70 で `uncons([])` 入力 list が既に空 | 否定 |
| D | queue replay は正しいが sub::return 2 後に戻り先違い | △ 派生形 | 部分一致 |
| **D'** | **sub::return propagation が intermediate handler eval を破壊し、queue が消える** | **✓ trace L58-63 で 6 frames propagation 観測** | **確定** |

write20 の case D は「queue replay が **走った後**に戻り先が違う」想定だったが、
実際は「**queue replay が走る前に** queue 自体が intermediate eval と一緒に消える」
という派生（case D'）。

---

## なぜ inner once eval が壊れるか（semantics 観点）

algebraic effect の正しい意味論では：

```
sub::return n は H_sub のスコープ（prompt=1）から抜ける。
H_sub は each__mono1 の中で install される（L34）。
inner once（prompt=2）は H_sub の外側で install される（L55）。
→ sub::return の prompt=1 jump は inner once を貫通すべきだが、
   inner once の eval / handler scope を破壊してはいけない。
```

現在の CPS eval `handle_scope_return` は `Propagate` するとき
**当該 eval frame を unwind して終了させてしまう**ため、その eval が install
していた handler frame（prompt=2）も一緒に消える。

trace L58-63 の 6 段 Propagate は、それぞれ独立した eval frame で、
sub::return 探索のために順番に破壊されている。本来は **handler stack を独立に
保ち**、prompt=p に match する handler の continuation へジャンプするだけで、
他の prompt の handler は残すべき。

これは delimited continuation の prompt-based scoping の問題で、
yulang の CPS eval は eval frame と handler scope を一体化させていることが
根本原因。

---

## write21 で取るべき方向（提案）

### 方針 A: handler stack を eval frame から独立させる

- `CpsHandlerFrame` の lifecycle を eval frame から切り離す
- ScopeReturn match 時、target prompt の handler に直接 jump し、
  途中の他 prompt の handler は touch しない
- eval frame の unwind は handler match 後の Return 経路で行う
- **大規模 refactor だが、algebraic effect の正しい semantics**

### 方針 B: Propagate 時に handler frame を「再保存」

- `handle_scope_return` の `Propagate` 分岐で、self が install した handler
  frame を ScopeReturn value に attach
- 上位の eval が ScopeReturn を消費する際、attach された handler を復元
- 動作は方針 A に近いが、データ伝播経路で実現
- 中規模

### 方針 C: prompt → eval frame の写像を持つ

- handler install 時に `(prompt, eval_frame_id)` を登録
- ScopeReturn match は eval frame stack を走査せず、写像から直接 target eval を選ぶ
- それ以外の eval / handler は touch しない
- 中規模だが、resumption invoke 時の handler 復元と整合させる作業が必要

---

## 触ったファイル

なし。

write19 の trace 強化（`summarize_cps_value` + InstallHandler/PrimitiveList trace 等）
が write20 でそのまま使えたので、追加の trace コードは不要だった。

---

## りなに渡す質問

1. write20 §case A の「最有力修正」は **既に実装されており trace でも機能している**。
   `lower_apply` / `direct_apply` / `lower_expr_as_call_arg` のいずれも、
   param が Thunk なら必ず MakeThunk wrapper を介する。trace でも
   `arg=Thunk(owner=once, entry=cont 8)` が見えており、recursive loop は
   handler install まで到達している。

   これ以上 case A の角度で見るべき場所があるか？ 私の判定では case D' に
   方針切り替えるのが妥当に見える。

2. case D' の修正方針として方針 A/B/C を挙げた。yulang の algebraic effect
   semantics として、どれが整合するか？

3. ScopeReturn propagation の現在のコード（`handle_scope_return` + `cps_eval` の
   eval loop の unwind）を「handler stack 独立化」する規模感を見積もりたい。
   現在の `inherited` フラグ / `escape_owner_function` / `return_frame_threshold`
   は方針 A 採用時にどう統合される？

---

## コミット予定

write20 完了。
- baseline 確認（167 + local_choice pass、once cps:0 vs vm:2 のまま）
- trace で case A 否定、case D' 確定
- `cps_lower.rs` audit で case A 修正が既に施されていることを確認
- 修正コードは無し（write21 設計判断待ち）
