# native-undet-write12 実装レポート

## 実装したこと（write12.md 指示ベース）

### 1. Return frame 機構の導入

`CpsResumption` に `return_frames: Rc<Vec<CpsReturnFrame>>` フィールドを追加。
Perform が起きたとき、その時点で生きている caller 継続をすべてキャプチャするようになった。

```rust
struct CpsReturnFrame {
    owner_function: String,
    continuation: CpsContinuationId,
    values: Rc<Vec<Option<CpsRuntimeValue>>>,
    active_handlers: Vec<CpsHandlerFrame>,
    guard_stack: Vec<CpsGuardEntry>,
}

struct CpsResumption {
    // ... 既存フィールド ...
    return_frames: Rc<Vec<CpsReturnFrame>>,
}
```

### 2. 新しい terminator IR ノード

handler scope 内で effectful な call/apply/force を「terminator」として表現する。

```rust
pub enum CpsTerminator {
    // ... 既存 ...
    EffectfulCall { target, args, resume },
    EffectfulApply { closure, arg, resume },
    EffectfulForce { thunk, resume },
}
```

これらは「post-call cont」を return frame として push して callee を呼び、
eval frame が `return` で終了する形になる。

### 3. `resume_continuation` / `continue_return_frames`

`eval_continuations` は handlers に `into_inherited` を適用する従来通りのエントリポイント。
新規追加した `resume_continuation` は `into_inherited` を**呼ばない**版で、
return frame を再開するとき（caller 側の状態をそのまま復元したい時）に使う。

`continue_return_frames` は inject された extras を含む frame を pop して
`resume_continuation` を呼ぶヘルパ。

### 4. `Return` 時の自動 frame 消費

`CpsTerminator::Return` が return_frames を非空で受けると、自動的に
`continue_return_frames` を呼んで次の frame を実行する。これにより
EffectfulCall → callee Return → caller post-call cont のチェーンが繋がる。

### 5. Resume / RWH 時の extras injection

`Resume(k, arg)` / `ResumeWithHandler` / `ApplyClosure(Resumption)` で、
resume site の `active_handlers` のうち `k.handlers` にないもの（= 内側で
インストールされた新しい handler、once の H2 とか）を `extras` として収集。

`inject_extra_handlers(frames, extras)` で各 frame の `active_handlers` に
extras を merge してから resume する。これで auto-trigger された
`continue_return_frames` が extras を保持した状態で post-call cont を実行できる。

### 6. lowering: handler scope 内の DirectCall を EffectfulCall に

`lower_handled_block` の `Let { pattern, value }` で、
`active_handler.is_some() && direct_apply(value)` が成立するときに
新メソッド `lower_handled_effectful_call_let` を呼ぶ。

このメソッドは:
1. args を lower（既存の stmt のまま）
2. EffectfulCall terminator を生成（resume = post-cont）
3. post-cont 内で、call_ty が非 Thunk なら更に EffectfulForce terminator
   を入れて (= force 操作も terminator に split)、forced 値を pattern に bind
4. rest を post-(post-)cont で再帰 lower

ポイント: 単に EffectfulCall するだけでは callee が返した Thunk を
synchronous な `ForceThunk` stmt で展開してしまい、その内側の Perform が
return_frames を失う。だから force も EffectfulForce terminator にする。

### 7. その他

- `cps_capture.rs`: 新 terminator の use 集合を追加
- `cps_validate.rs`: 新 terminator の検証を追加
- `cps_repr.rs` / `cps_repr_cranelift.rs`: 新 terminator は `todo!()` /
  `UnsupportedTerminator` でスタブ（CPS eval が動けば足りるので今は未実装）

---

## テスト状況

### 通った

- **170 既存テスト** すべて PASS（regression なし）
- **`debugs_local_choice_caller_rest_eval`** PASS（新規）
  - 局所 `choice` effect で、`work()` が `choose()` を呼んだ後 reject する最小ケース
  - 期待値: 2、実測: 2（VM と一致）
  - これが通ったということは「resumption が caller の post-call cont を
    正しくキャプチャしている」という根本セマンティクスが動いている

### まだ通らない

- **`debugs_std_undet_once_skip_eval_layers`** FAIL（cps:0, vm:2）
  - `std::undet.once` 経由（`each [1,2,3]` + `guard`）
  - stdlib の `each` / `sub::return` / `list<resumption>` キューなど、
    より複雑な構成を通る経路で破綻している
  - 原因はまだ詳細特定していない（次セッションで深掘り）

---

## 設計上の発見

### 「sync な呼び出し」と「effectful terminator」の区別

`DirectCall` stmt (sync) と `EffectfulCall` terminator (eval ending) で
return_frames の扱いを変える必要があった。
- sync: callee に `Vec::new()` を渡す（caller の eval は生きているので
  callee の Return が caller の frames を勝手に消費してはいけない）
- terminator: caller frames + new_frame を渡す

これは write12.md ではあまり強調されていなかったが、Return での
auto frame consumption と組み合わせて初めて整合性が取れる。

### EffectfulForce の必要性

`choose` のような effectful helper は内部で `MakeThunk + Return` する
ことで「呼び出し結果が Thunk」となる。caller 側で sync `ForceThunk` stmt
で展開すると、その内側の Perform は return_frames=[] になり、caller の
post-call cont が resumption に入らない。

EffectfulForce terminator を新設して force 操作も「caller を suspend して
callee（= thunk body）を呼ぶ」形にすることで解決。

write12.md にも書かれていたが、当初は EffectfulCall だけで足りると思って
いて、テストを通す過程で必要性が見えてきた。

### `inherited` flag は維持

write11 で導入した `inherited: bool` は今回も活きていて、
- callee に渡す handler stack: into_inherited で全部 inherited に
- return frame の active_handlers: 復元時に元の inherited 状態を保つ
- resume site で injected extras: そのまま non-inherited で frame に注入

という3層構造で運用している。

---

## 次回への引き継ぎ

### 残課題

1. **`std::undet.once` の通過**
   - `each [1,2,3]` 経由の reject backtrack
   - `sub::return` で early-exit するパス
   - `list<resumption>` キュー（write9-11 で対応済みのはずだが return frame
     導入で再検証が必要）

2. **CPS repr eval (Phase 7)**
   - `cps_repr.rs` の eval にも同じ return frame 機構を移植
   - 現在は `todo!()` スタブ

3. **Cranelift (Phase 8)**
   - return frame を Cranelift IR で表現
   - 現在は `UnsupportedTerminator` エラーで停止

### 想定される `std::undet.once` 問題

local test と違い、`std::undet.once` では:
- `each` が `fold` を使った再帰
- `branch` の resume が `sub::return` でショートサーキット
- 失敗時の `reject` が outer の once まで bubble up

このどこかで return_frames の伝播が切れている可能性が高い。
- `fold` 内部の closure apply
- `sub::sub` ハンドラの内部
- `loop` 関数（once の本体）の再帰呼び出し

これらが全部 handler scope 内の呼び出しになっているか確認が必要。

特に注意すべき点: `lower_handled_effectful_call_let` は **DirectCall のみ**
対応。ApplyClosure や `Stmt::Expr` の direct call は未対応。
`each` や `fold` は closure application を多用するので、それを
`EffectfulApply` で扱うようにする必要があるかも。

### りなに聞いたら良さそうなこと

1. **ApplyClosure も EffectfulApply にすべき範囲**
   - 全 ApplyClosure を effectful にすると過剰? 静的型で判別?
2. **`Stmt::Expr` (non-binding effectful call) も terminator にする必要は?**
   - 結果を捨てる pattern では post-cont が空? 
3. **`each.fold` のような higher-order closure を含む chain での return frame 伝播**
   - 期待される挙動の概念モデル
