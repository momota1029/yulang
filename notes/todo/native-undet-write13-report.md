# native-undet-write13 実装レポート

## このセッションでやったこと

write13.md の指示（特に「ApplyClosure も EffectfulApply 化」と「callee type-based 判定」）に
従って、handler scope 内の `Let { pattern, value }` で value が `Apply` のとき、
callee の型に effect potential があれば `EffectfulApply` terminator を出すようにした。

### コード変更

- `cps_lower.rs::callee_type_may_perform`: callee 型から effect 可能性を判定する helper。
  `Fun { ret }` の ret が Thunk か Unknown なら effectful 扱い。
- `cps_lower.rs::lower_handled_block`: `Let { value }` で value が `Apply` かつ
  callee の型に effect potential があれば `lower_handled_effectful_apply_let`
  を呼ぶ追加経路。
- `lower_handled_effectful_apply_let`: callee/arg を lower、`EffectfulApply` terminator
  を発行、post-cont で `EffectfulForce`（必要なら）して pattern に bind。

### Stmt::Expr は今回は **入れなかった**

write13 step 2 では `Stmt::Expr` も effectful terminator split することになっているが、
これを入れると **既存の `_through_cps_repr_cranelift` テスト 3 件が落ちる**。原因:

- `std::undet.once` 経路で `each`/`sub::return` などが `Stmt::Expr` 位置の direct call
  として現れる
- これらを `EffectfulCall` terminator に変えると、Cranelift backend が
  `todo!("Effectful{{Call,Apply,Force}} in cps_repr Cranelift backend")` で停止
- ↑ は write13 が「Cranelift は CPS eval semantics が固まってから」と明示しているとおり
  予定通りの未実装箇所

なので Stmt::Expr 経路は **コード自体は残してある**（`lower_handled_effectful_call_expr`,
`lower_handled_effectful_apply_expr` を private dead code として保持）が、
呼び出し箇所はコメントアウト相当の状態。`#[allow(dead_code)]` を付けてある。

---

## テスト状況

### 通った
- **既存 170 テスト** すべて PASS（regression なし）
- 写経済みの local minimal test `debugs_local_choice_caller_rest_eval` も継続して PASS

### 通らなかった
- **`debugs_local_choice_callback_rest_eval`** (Test A, write13 で追加)
  - 期待: `2`、実測: `cps:1`, `vm:2`
  - `call_callback(f) = f 0` の `f 0` 経路で caller の post-call cont を捕まえられていない
  - `call_callback` の lowering 時点で `active_handler` がなく、`f 0` は
    `Apply` だが `lower_root` を経由するため `lower_handled_block` の経路に乗らない
- **`debugs_std_undet_once_skip_eval_layers`** 引き続き未通過

---

## 残課題 — Test A を通すための設計議論

### 問題の本質

`call_callback` のような helper 関数は、lowering 時点で handler scope を持っていない。
`f 0` という ApplyClosure stmt が普通に出る。実行時には handler scope の下で動くが、
ApplyClosure stmt は eval 側で `Vec::new()` の return_frames を callee に渡しているので、
callee 内の Perform が caller の rest を捕まえられない。

### 候補解 A: lowering で Apply を terminator 化（書き換える）

`lower_apply` / `lower_root` を変更して、callee の型から effectful と判定したら
`EffectfulApply` terminator を出す。

問題: 既存 Cranelift backend が EffectfulApply に未対応。
広範に triger すると test regression。
保守的判定（callee type で見る）でも、`std::undet.once` の経路では
effectful な ApplyClosure が頻出し、結局 Cranelift で落ちる。

### 候補解 B: eval で stmt ApplyClosure が caller frames を伝搬

ApplyClosure stmt 経由でも callee に parent の `return_frames` を渡し、
Perform で resumption に含まれるようにする。ただし、callee の `Return` は
**inherited frames を auto-consume しない** 設計が必要（parent eval は生きているから）。

実装案: `eval_continuations` に `initial_frame_count: usize` を追加。
`Return` で `frames[initial..]` のみ consume。sync stmt 呼び出しは
`initial = parent.len()` で「親の frames は inherited、own push なし」を表現。
EffectfulCall terminator は push 後の eval に `initial = pre_push_count` を渡し、
push した F_self は callee の own として消費されるようにする。

これは **eval の中核 refactor** で、波及範囲が大きい。
ただし IR は無変更なので Cranelift backend は影響を受けにくい。

### 候補解 C: write14 で受ける

write13 をここで一区切りとして、Test A / std::undet.once は write14 で
「eval の `initial_frame_count` refactor」として実装する。

---

## りなに渡す質問

1. **候補解 B (eval の `initial_frame_count` 化)** は方向として正しいか？
2. ApplyClosure stmt が parent frames を **inherit** する一方で **consume しない** という
   分離は IR 上どこに表れるべきか？ stmt と terminator の区別だけで十分か？
3. `Resume(k, val)` の入口での frame consumption 方針:
   - 現状の auto-trigger（Return が consume）+ extras injection
   - 候補解 B（明示的に Resume が continue_return_frames 呼ぶ + initial=0）
   どちらが Cranelift 移植時に楽か？
4. `EffectfulForce` を sync stmt の代わりに使う対象を広げると、Test A は
   通る可能性があるか？ (`call_callback`'s `f 0` を `EffectfulApply` ではなく
   `EffectfulForce` で扱うのは違うか？)

---

## コミット予定

write13 partial（Apply for Let with type check + callee_type_may_perform helper +
Test A test source + write13 関連ノート）。Stmt::Expr 用 helper は dead code として保持。

170 既存 + 1 新規 ignore = 171 ignored/passed の状態を維持。
