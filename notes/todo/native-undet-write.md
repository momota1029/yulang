もちろんだよ〜。
以下は **別のLLにそのまま渡せる作業メモ** として書くねぇ。かなり細かくしておく。
目的は「作業者が勝手に広げず、段階的に `undet` へ近づく」ことだよ〜。

---

# Yulang Native Backend / `std::undet` 完成へ向けたリファクタリング作業メモ

## 0. 現在地

Yulang の native backend は、すでにかなり進んでいる。README 上では、native backend はまだ active development であり、interpreter / VM が semantic oracle、native paths は明示された subset のみで有効、という位置づけになっている。value backend は基本値・list・tuple・record・variant などを扱える一方、general pattern matching / general multi-block control flow / closure allocation は未対応。CPS representation backend は effect / handler / resumption / guard stack / mutable ref までかなり進んでいるが、general thunk values、general closures、non-scalar CPS executable printing はまだ未完成と整理されている。

`native-undet-plan.md` では、`std::undet.once` は最初の実装対象ではなく統合 target として扱う方針が明記されている。理由は、`std::undet.once` が branch/reject、multi-shot resumption、saved resumption queue、`list<resumption>`、recursive handler loop、`opt` non-scalar return、`fold` / `sub::return`、handler stack / guard stack snapshot、thunk callback crossing handler boundaries を全部同時に踏むから。

最新コミットでは、DFS `once` kernel と finite-list nondeterministic choice without `fold` / `sub` は進んだが、**function-returned effectful thunk が caller の active handler frame を reliably に持てない** ことが open blocker とされている。

---

# 1. 最終目標

最終的には、以下が native path で動くようにする。

```yulang
use std::undet::*

(each [1, 2, 3]).once
```

ただし、最初からこれを直接 target にしてはいけない。
これは統合テストであり、途中段階ではより小さい local `choice` effect を使う。

最終的な成功条件は以下。

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-native undet
```

に加えて、CLI で少なくとも次が動く。

```bash
RUSTC_WRAPPER= cargo run -q -p yulang -- --native-run <<'YU'
use std::undet::*

case (each [1, 2, 3]).once:
    std::opt::opt::nil -> 0
    std::opt::opt::just x -> x
YU
```

最初は `opt` をそのまま print しなくてよい。
`case ... nil/just` で scalar `int` に戻して比較する。

---

# 2. 絶対に守る方針

## 2.1 VM を semantic oracle にする

native 側の semantics を勝手に作らない。
必ず VM と比較する。

良いテスト:

```rust
compare_source_cps_repr_i64(source).expect("...");
```

または、

```rust
let vm = runtime VM result;
let native = CPS repr Cranelift result;
assert_eq!(native, vm);
```

悪いテスト:

```rust
assert_eq!(native, 1);
```

だけで終わるもの。
これは VM との差分を見逃す。

## 2.2 `std::undet.once` にすぐ戻らない

`std::undet.once` は Phase 6 以降。
まずは local `choice` effect を使う。

## 2.3 value backend と CPS repr backend を混ぜない

`undet` は CPS repr backend の問題。
value backend に resumption / thunk / handler frame を入れない。

## 2.4 `RuntimeValuePtr`, `ThunkPtr`, `ResumptionPtr`, `OpaqueI64` を混ぜない

`ThunkPtr` や `ResumptionPtr` を `VmValue` の list に雑に入れない。
control object と user-visible value は分ける。

## 2.5 fallback は構造化された unsupported reason だけで起こす

「なんとなく失敗したから別 backend」禁止。
fallback の理由は enum / structured error で残す。

---

# 3. 今の open blocker

現在の blocker はこれ。

> **source-defined direct call が返す effectful thunk が、caller の active handler frame を失う。**

例として、次のような helper が難しい。

```yulang
my each_head(xs): [choice] int = ...
once_dfs { each_head [1, 2, 3] }
```

`each_head` の中で作られた `[choice] int` thunk が caller 側の `once_dfs` handler の中で force されたとき、`choice::branch` / `choice::reject` が caller の handler に届かなければならない。

`native-undet-plan.md` でも、Phase 4 は function-shaped finite `each` であり、source-defined `each_head` / `each_list` returning `[choice] int` の caller handler frames が direct function boundary を越えて見える必要がある、と整理されている。

---

# 4. リファクタリング全体のマイルストーン

## Milestone 0: 状況固定と安全網

### 目的

作業前に現在の通る範囲と ignored regression を確認する。

### やること

```bash
git status
git log --oneline -5

rg "ignore|each_head|once_dfs|choice::reject|native-undet" crates/yulang-native notes
cargo test -p yulang-native -- --list | rg "undet|once|each|thunk|cps"
```

### 実行するテスト

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-native cps_repr -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-native once -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-native each -- --nocapture
```

### 成功条件

* 既存テストが悪化していない。
* ignored regression の名前と理由が分かる。
* 作業対象を `each_head` / function-returned effectful thunk に限定できる。

### 禁止事項

* `std::undet.once` を直接修正し始めない。
* value backend に手を入れない。
* CLI fallback をいじらない。

---

## Milestone 1: ignored `each_head` regression を単独テスト化

### 目的

「function-returned effectful thunk が handler frame を失う」問題だけを見るテストを作る。

### テスト形

`crates/yulang-native/src/source.rs` などに、まず ignored でよいので以下のような test を作る。

```rust
#[test]
#[ignore = "Phase 4: function-returned effectful thunk must retain caller handler frame"]
fn compares_source_each_head_helper_through_cps_repr_cranelift() {
    run_with_large_stack(|| {
        compare_source_cps_repr_i64(r#"
pub act choice:
  pub branch: () -> bool
  pub reject: () -> never

my once_dfs(x: [choice] int): int = catch x:
    choice::branch (), k ->
        catch k true:
            choice::reject (), _ -> k false
            v -> v
    choice::reject (), _ -> 0
    v -> v

my each_head(xs): [choice] int = case std::list::uncons xs:
    std::opt::opt::nil -> choice::reject ()
    std::opt::opt::just (x, rest) ->
        if choice::branch ():
            x
        else:
            choice::reject ()

once_dfs { each_head [1, 2, 3] }
"#).expect("each_head helper CPS repr compare");
    });
}
```

必要なら syntax は実際の Yulang に合わせて調整する。

### 期待

結果は `1` でよい。
`k true` で head を返す。
失敗したら `k false` に行くが、まずは false 側の探索は最小でよい。

### 成功条件

* テストが現在失敗する。
* 失敗理由が `MissingHandler` / wrong handler frame / thunk force error / unsupported thunk のどれかに分類できる。
* 失敗が `std::undet` 由来ではなく、local `choice` 由来で再現する。

---

## Milestone 2: CPS eval で先に通す

### 目的

Cranelift ではなく、CPS evaluator で semantics を先に合わせる。

### やること

`compare_source_cps_repr_i64` の前に、CPS lowering + CPS eval + CPS repr eval を分けて見るテストを作る。

```rust
let module = runtime_module_from_source_with_options(source, native_default_source_options())
    .expect("runtime module");

let cps = crate::cps_lower::lower_cps_module(&module)
    .expect("CPS lowering");

crate::cps_validate::validate_cps_module(&cps)
    .expect("valid CPS");

let cps_values = crate::cps_eval::eval_cps_module(&cps)
    .expect("CPS eval");

let repr = crate::cps_repr::lower_cps_repr_module(&cps);
let repr_values = crate::cps_repr::eval_cps_repr_module(&repr)
    .expect("CPS repr eval");

assert_eq!(cps_values, repr_values);
```

### 見る場所

* `crates/yulang-native/src/cps_lower.rs`
* `crates/yulang-native/src/cps_capture.rs`
* `crates/yulang-native/src/cps_eval.rs`
* `crates/yulang-native/src/cps_repr.rs`

### 成功条件

* CPS eval が VM と一致する。
* CPS repr eval が CPS eval と一致する。
* まだ Cranelift は通らなくてもよい。

---

## Milestone 3: thunk の handler frame capture rule を明文化する

### 目的

今の混乱を止める。
コードを書く前に rule をコメントまたは design note にする。

### 推奨ルール

以下を `notes/design/native-undet-plan.md` または新規 `notes/design/cps-thunk-handler-invariants.md` に書く。

```text
Effectful thunk invariant:

1. A thunk stores:
   - entry continuation
   - lexical/captured CPS values required by the thunk entry
   - optionally, handler frame environment snapshots that were available at thunk creation

2. A thunk does not blindly freeze all dynamic handler state forever.
   Force-site active handler stack remains semantically important.

3. If a thunk is produced by a handler wrapper or direct helper and later forced
   under a caller handler, the force operation must be able to route Perform
   through the caller handler stack.

4. ResumeWithHandler is used when a resumption must be re-entered under a newly
   installed handler frame. The reinstalled frame must carry handler arm envs.

5. RuntimeValuePtr, ThunkPtr, and ResumptionPtr are distinct lanes.
   Do not force arbitrary OpaqueI64 or RuntimeValuePtr as a thunk.
```

### 成功条件

* 次に実装する人が「thunk は作成時 stack なのか force-site stack なのか」で迷わない。
* `MakeThunk` と `ForceThunk` の責務が明文化される。

---

## Milestone 4: `MakeThunk` / `ForceThunk` の env capture を整理

### 目的

`ResumeWithHandler` だけでなく、thunk が handler env を失わないようにする。

### 現状の観察

最新コミットでは `fill_resume_handler_envs` が入り、`ResumeWithHandler` の `envs` を continuation captures から埋める方向に進んでいる。

しかし open blocker は、function-returned effectful thunk が caller の handler frame を reliably に持たないこと。

### 検討する変更

必要なら `CpsStmt::MakeThunk` を拡張する。

現状イメージ:

```rust
CpsStmt::MakeThunk {
    dest,
    entry,
}
```

候補:

```rust
CpsStmt::MakeThunk {
    dest,
    entry,
    envs: Vec<CpsHandlerEnv>,
}
```

または、

```rust
CpsStmt::MakeThunk {
    dest,
    entry,
    captured_handler_envs: Vec<CpsHandlerEnv>,
}
```

### 実装方針

1. `cps_ir.rs` で `MakeThunk` に envs を足す。
2. `cps_capture.rs` で `MakeThunk` の entry captures と handler arm captures を埋める。
3. `cps_eval.rs` で `MakeThunk` 時に envs を実値 snapshot する。
4. `ForceThunk` 時に、thunk の envs と force-site active handler stack をどう組み合わせるか明示する。
5. CPS repr evaluator に同じ rule を入れる。
6. Cranelift は最後。

### 注意

全部の handler stack を thunk 作成時に凍結しない。
それをすると、caller 側で handler をつけて thunk を force するケースが壊れる。

---

## Milestone 5: `each_head` ignored regression を unignore

### 目的

Phase 4 を実際に完了させる。

### 条件

以下が通ること。

1. CPS eval
2. CPS repr eval
3. CPS repr Cranelift JIT
4. VM 比較

### コマンド

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-native each_head -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-native once_dfs -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-native native_undet -- --nocapture
```

### 成功条件

* `#[ignore]` を外せる。
* `native-undet-plan.md` の Phase 4 を Completed に移せる。
* 新しい regression が `std::undet` を使わずに通る。

---

## Milestone 6: `each_list` に進む

### 目的

`each_head` から、finite list を少しだけ探索できる helper へ進む。

### テスト形

```yulang
pub act choice:
  pub branch: () -> bool
  pub reject: () -> never

my once_dfs(x: [choice] int): int = ...

my each_list(xs): [choice] int = case std::list::uncons xs:
    std::opt::opt::nil ->
        choice::reject ()
    std::opt::opt::just (x, rest) ->
        if choice::branch ():
            x
        else:
            each_list rest

once_dfs { each_list [1, 2, 3] }
```

### 期待値

`1`

### 注意

まだ `std::undet.each` は使わない。
まだ `fold` / `sub::return` は使わない。

### 成功条件

* recursive helper が通る。
* resumption / thunk / handler frame が再帰を越えて壊れない。
* scalar root のまま VM と一致する。

---

## Milestone 7: `std::undet.each` に戻す

### 目的

標準ライブラリの `each` を使う。

### テスト形

```yulang
use std::undet::*

case (each [1, 2, 3]).once:
    std::opt::opt::nil -> 0
    std::opt::opt::just x -> x
```

ただし、これはまだ現在の標準 `once` を使うので重い。
先に `each` だけを local `once_dfs` に渡せる形があれば、それを優先する。

### 注意

`std::undet.each` は `fold` と `sub::return` を使う。`native-undet-plan.md` でも、`std::undet.once` は hard cases を同時に踏む統合 target とされている。

### 成功条件

* `fold` / `sub` machinery が native CPS repr で壊れない。
* scalar root に潰して VM と一致する。

---

## Milestone 8: queue-backed `once`

### 目的

標準 `std::undet.once` に必要な resumption queue を設計する。

### 問題

標準 `once` は queue に resumption `k` を保存して、あとで `k false` する。
これは `list<resumption>` または equivalent opaque control queue が必要。

### 推奨方針

最初は `VmValue::List` に resumption を入れない。
CPS runtime 専用 queue を作る。

候補 API:

```text
cps_queue_empty() -> QueuePtr
cps_queue_push(queue, opaque_i64) -> QueuePtr
cps_queue_uncons(queue) -> (is_empty, head, tail)
```

または Rust 側 helper:

```rust
yulang_cps_queue_empty
yulang_cps_queue_push_i64
yulang_cps_queue_uncons_i64
```

### 成功条件

* queue に resumption pointer を保存できる。
* `k false` で再開できる。
* queue は user-visible `list` と混ざらない。

---

## Milestone 9: `std::undet.once` scalar-unwrapped

### 目的

標準 `.once` を scalar root に潰して native で動かす。

### テスト

```yulang
use std::undet::*

case (each [1, 2, 3]).once:
    std::opt::opt::nil -> 0
    std::opt::opt::just x -> x
```

### 成功条件

* VM と CPS repr Cranelift が一致する。
* `--native-run` でも同じ結果が出る。
* backend selection が見える。

### 追加で欲しい CLI 表示

```text
native-run backend: cps-repr
native-run reason: value backend unsupported: algebraic effect
```

---

## Milestone 10: `.list` / `.logic`

### 目的

最終的に nondeterminism collector を広げる。

### 順番

1. `.list` with finite list
2. `.once` with finite list
3. `.logic` with finite small list
4. infinite range は最後

### 注意

`.logic` は breadth-first scheduling なので queue と result list の両方が必要。
`once` より重い。絶対に早く触らない。

---

# 5. 作業者向け禁止事項

以下は禁止。

```text
- std::undet.once を最初に直接直す
- VM と比較せず native expected value だけでテストする
- RuntimeValuePtr と ThunkPtr と ResumptionPtr を混ぜる
- VmValue::List に resumption を雑に入れる
- value backend に handler/resumption/thunk を入れる
- fallback を文字列エラーや偶然の失敗で判定する
- ignored regression を増やすだけで終える
- source.rs に巨大テストを足すだけで support matrix を更新しない
- Cranelift から先に直して CPS eval / CPS repr eval を見ない
```

---

# 6. 変更時に必ず見るファイル

```text
crates/yulang-native/src/cps_ir.rs
crates/yulang-native/src/cps_lower.rs
crates/yulang-native/src/cps_capture.rs
crates/yulang-native/src/cps_eval.rs
crates/yulang-native/src/cps_repr.rs
crates/yulang-native/src/cps_repr_cranelift.rs
crates/yulang-native/src/cps_runtime.rs
crates/yulang-native/src/source.rs
notes/design/native-undet-plan.md
README.md
tasks/current.md
```

---

# 7. テスト戦略

## 7.1 まず CPS eval

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-native cps_eval -- --nocapture
```

## 7.2 次に CPS repr eval

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-native cps_repr -- --nocapture
```

## 7.3 最後に Cranelift

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-native cps_repr_cranelift -- --nocapture
```

## 7.4 source-level regression

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-native source -- --nocapture
```

## 7.5 undet 関連だけ

```bash
RUSTC_WRAPPER= cargo test -q -p yulang-native undet -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-native once -- --nocapture
RUSTC_WRAPPER= cargo test -q -p yulang-native each -- --nocapture
```

---

# 8. 期待する最終成果物

作業が進んだら、以下を更新すること。

## `notes/design/native-undet-plan.md`

Phase ごとの status を更新。

```text
Completed:
- Phase 4: function-returned effectful thunk carries caller handler frame
- Phase 5: finite each_list
```

## `README.md`

Native Backend Progress を更新。

```text
CPS representation backend status:
- [x] Function-returned effectful thunks preserve handler routing across direct calls.
- [x] Finite local each_list works through CPS repr Cranelift.
```

## `tasks/current.md`

次の blocker を明記。

```text
Next blocker:
- queue-backed once needs a CPS opaque resumption queue.
```

---

# 9. 次回の作業者への最初の指示文

以下をそのまま別LLに渡すとよい。

```text
Yulang native backend の `std::undet` 対応を進めます。

重要:
- std::undet.once は直接触らない。
- native-undet-plan.md の Phase 4 だけを進める。
- open blocker は「source-defined direct call が返す effectful thunk が caller の active handler frame を reliably に持たない」こと。
- each_head / once_dfs / local choice::branch/reject の ignored regression を探して、それだけを通す。
- まず CPS eval、次に CPS repr eval、最後に CPS repr Cranelift JIT。
- RuntimeValuePtr / ThunkPtr / ResumptionPtr を混ぜない。
- VmValue::List に resumption を雑に入れない。
- value backend には触らない。
- VM comparison を必ず使う。

作業順:
1. rg "ignore|each_head|once_dfs|native-undet" crates/yulang-native notes
2. ignored each_head regression を単独で確認
3. cps_lower / cps_capture / cps_eval を読む
4. thunk returned across direct call が handler frame/env を失う箇所を特定
5. 必要なら MakeThunk に handler env capture を追加
6. CPS eval を通す
7. CPS repr eval を通す
8. CPS repr Cranelift を通す
9. ignore を外す
10. native-undet-plan.md / README.md / tasks/current.md を更新

ゴール:
- local choice + once_dfs + each_head [1,2,3] が VM と CPS repr Cranelift で一致する。
- std::undet.once にはまだ進まない。
```

---

# 10. りなの見立て

次に一番やるべきことは、**`each_head` の ignored regression を unignore すること**。
これが通れば、`std::undet.each` に戻る道がかなり見える。

逆に、ここを飛ばして queue-backed `once` や `.logic` に行くと、また全部が絡んでつらくなると思うよ〜。

今はかなり進んでいるけど、ここからは「機能追加」よりも **handler / guard / thunk / resumption の invariant を守るリファクタリング** が大事だねぇ。
