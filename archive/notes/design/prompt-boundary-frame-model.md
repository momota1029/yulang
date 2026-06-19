# Prompt Boundary Frame Model

設計案 (2026-05-17 起案 / Phase 1)。
shallow handler の subcontinuation 境界を、現在の `return_frame_threshold + active_handlers snapshot` という implicit encoding から、`prompt_exit` を first-class frame marker として扱う形に整える。

関連: `notes/bugs/native_recursive_handler_for_last_tail_skips_value_arm.yu`,
`notes/bugs/index.md` の round-6 後半（`PromptBoundary(P)` / `PromptExit(P)` の WIP 整理）.

---

## 1. 背景・最小再現

```yulang
pub act out:
    pub say: str -> ()

our listen(x: [_] _, log: str): (_, str) = catch x:
    out::say o, k -> listen(k(), log + o + "\n")
    v -> (v, log)

listen({
    for x in [0]:
        out::say x.show
    5
}, "")
```

- 期待 (interpreter): `(5, "0\n")`
- 実際 (native, 2026-05-17): `5`

`for ... last` も `last` 自体も本質ではない。最小は **「2引数 listen + 1要素 for + 1 say + tail value」** で起きる
（このターンで切り分け済）。

trace では `(0, "0\n")` (≒ `((), "0\n")` の unit→0 表示) が一度作られて
`scope_return_set / route_scope_return / abort mode=2` のシーケンスで発火される。
しかしその abort が outer listen の value-arm の代わりに consume されないまま、
無関係な `5` が root に上ってくる。

---

## 2. 現状の encoding

### 2.1 InstallHandler で push されるもの (cps_eval.rs:1246-1269)

```rust
CpsStmt::InstallHandler { handler, envs, value, escape } => {
    let pushed_prompt = fresh_prompt();
    let threshold = return_frames.len();
    active_handlers.push(CpsHandlerFrame {
        prompt: pushed_prompt,
        return_frame_threshold: threshold,   // ← 暗黙の境界
        escape: *escape,
        install_eval_id: current_eval_id,
        ...
    });
    return_frames.push(CpsReturnFrame {
        prompt_exit: Some(CpsPromptExitFrame { prompt: pushed_prompt }),  // ← 明示マーカー
        continuation: *value,  // value arm への continuation
        ...
    });
}
```

両方を同時に push しているので、当面は **不変条件**:

> handler frame `H` (prompt=P) が `active_handlers[i]` にある時、
> `return_frames[H.return_frame_threshold]` は `prompt_exit == Some(P)` を持つ frame である。

逆に言うと、`return_frame_threshold` は `prompt_exit == Some(P)` を満たす frame の index に等しい。

### 2.2 これを読む 2 系統

- **Capture (resumption 作成時)**: `prompt_exit` を rposition で探して slice 境界とする
  (cps_eval.rs:2081 `captured_prompt_frame_start`).
- **Routing**:
  - `handle_scope_return` (cps_eval.rs:352): `active_handlers` から prompt 一致を rposition、
    その handler frame の `return_frame_threshold` で truncate.
  - `try_route_scope_return_through_return_frames` (cps_eval.rs:2389):
    各 return frame の `active_handlers snapshot` から prompt 一致を rposition、
    matched handler の `return_frame_threshold` で truncate.

つまり capture は marker ベース、routing は threshold ベース。
**書き手 (InstallHandler) は両方を同期して set** しているが、
ロジック 2 系統が違うルールで読むため、frame stack が動く間に乖離が出ると壊れる。

### 2.3 乖離はいつ起きるか

shallow handler の `k v` resumption が、その capture 時の return frame stack を
復元してから resume する流れで、`merge_extras_into_frames` 等で resume-site の
extra frames を挿入する。挿入された frame は元の threshold には数えられていない。

`rebase_captured_handler_frame` (cps_eval.rs:2119) が
`return_frame_threshold -= dropped_frames` で再計算しているが、
inherit/snapshot されたコピーは多数あり、どこか 1 つでも更新を漏らすと
そのコピーが指す threshold が古いままになる (= 別の prompt の境界を踏む)。

`prompt_exit` は frame 自身に貼り付いているので、frame が移動しても識別子としては動かない。

---

## 3. 仮説と検証可能性

- 仮説: routing 側を threshold ではなく `prompt_exit` ベースの rposition に
  揃えれば、shallow handler の境界がブレなくなる。
- 検証: routing 側を変更したあと、`captured_prompt_frame_start` と
  同じ rule で動くため、capture と routing が常に一致する不変条件が成立する。

ただし `prompt_exit` が**ない** frame が混ざるケース (Perform/EffectfulCall 用に
push される ordinary frame、cps_eval.rs:1743/1775/1849) を正しくスキップする
必要がある。

---

## 4. 提案する frame model

**追加するデータ型はゼロ**。既存の `prompt_exit: Option<CpsPromptExitFrame>` を
PromptExit marker としてそのまま使う。

意味論を以下のように整理する:

| frame の種類 | 表現 |
| --- | --- |
| ordinary return frame (Perform 後の続き等) | `prompt_exit == None` |
| **PromptExit(P)** (handler scope の exit boundary) | `prompt_exit == Some(P)`、`continuation == value arm` |
| **EscapeTarget(P)** (scope return の jump 先) | 対応する `CpsHandlerFrame.escape` |
| **PromptBoundary(P)** (handler の install 位置) | 「`PromptExit(P)` の return frame の **直後**」と定義 |

つまり PromptBoundary は派生概念。`return_frame_threshold` フィールドは
最終的に削除可能 (= `index_of(prompt_exit == Some(P)) + 1` で計算可能)。

ただし削除は段階的にやる (Phase 2.3)。

---

## 5. 新 routing アルゴリズム

### 5.1 `handle_scope_return` (current activation 内)

```rust
// 旧:
let frame = &active_handlers[index];
let threshold = frame.return_frame_threshold;
active_handlers.truncate(index);
ScopeReturnAction::JumpOrExit { target, value, return_frame_threshold: threshold }

// 新:
let frame = &active_handlers[index];
// PromptExit(P) を rposition で探して、その手前までを残す
let truncate_at = return_frames
    .iter()
    .rposition(|f| {
        f.prompt_exit.as_ref().is_some_and(|exit| exit.prompt == frame.prompt)
    })
    .map(|i| i)  // PromptExit 自身も pop する (handler scope を抜けるから)
    .unwrap_or(0);
active_handlers.truncate(index);
ScopeReturnAction::JumpOrExit { target, value, return_frame_threshold: truncate_at }
```

不変条件下では `truncate_at == frame.return_frame_threshold` のはずなので、
動作は同じ。乖離があった場合に `prompt_exit` 側を信頼する。

### 5.2 `try_route_scope_return_through_return_frames` (caller chain を walk)

各 return frame の `active_handlers snapshot` から prompt 一致を探す部分は同じ。
matched handler の threshold で `rest_frames` を truncate する代わりに、
`rest_frames` 自身を `prompt_exit == Some(P)` の rposition で truncate する:

```rust
// 旧:
let threshold = matched_handler.return_frame_threshold;
if rest_frames.len() > threshold { rest_frames.truncate(threshold); }

// 新:
let truncate_at = rest_frames
    .iter()
    .rposition(|f| {
        f.prompt_exit.as_ref().is_some_and(|exit| exit.prompt == matched_handler.prompt)
    })
    .unwrap_or(0);
rest_frames.truncate(truncate_at);
```

### 5.3 native JIT (`yulang_cps_route_scope_return_i64`)

cps_repr_cranelift.rs:9281-9430 を同じ方針で書き換える。
NATIVE_CPS_I64_RETURN_FRAMES の各エントリは `prompt_exit: Option<NativeCpsI64PromptExitFrame>`
(cps_repr_cranelift.rs:5941) を持っているので、同じ rposition lookup ができる。

---

## 6. 3 層別変更点

### 6.1 cps_eval.rs (interpreter)

- `handle_scope_return` (L352): 5.1 のとおり書き換え.
- `try_route_scope_return_through_return_frames` (L2476-2480): 5.2 のとおり書き換え.
- 他の routing point: なし (上記 2 つに集約されている).
- `rebase_captured_handler_frame` (L2119) の `return_frame_threshold` 計算: 当面残す
  (compat). Phase 2.3 で削除候補.

### 6.2 cps_repr.rs (repr-layer evaluator)

cps_eval と同じ shape の routing 関数が並んでいるはず. grep で位置確認:

```
prompt_exit:  L2131 (InstallHandler 内 push), L3056 (capture 側 lookup), L3746 (field 定義)
```

InstallHandler / capture 側は cps_eval と同じ実装になっている (Layer 2 として
mirror). routing 側 (`handle_scope_return` 相当 / `try_route_*` 相当) を同じ方針で
書き換える. 関数名は要確認.

### 6.3 native JIT (cps_repr_cranelift.rs)

- `yulang_cps_route_scope_return_i64` (L9281): 5.3 のとおり書き換え.
- `consume_native_i64_abort` (L9901): `return_frame_threshold` を使っている可能性、確認.
- `restore_native_i64_return_frame_prefix` (L10052): 同上.

---

## 7. 段階的実装計画

各 phase で `cargo test -q -p yulang-native` および
`solved/` snippets の VM/native 一致を確認する。

### Phase 2.1: cps_eval routing を切り替え

- `handle_scope_return` / `try_route_scope_return_through_return_frames` を `prompt_exit` ベースに変更
- 旧 threshold 計算結果と比較する `debug_assert_eq!` を一時的に追加し、乖離検出
- `cargo test -q -p yulang-runtime` で interpreter のレグレッションがないか確認

### Phase 2.2: cps_repr routing を切り替え

- cps_repr.rs の同 shape 関数を同方針で書き換え
- `cargo test -q -p yulang-native` (cps_repr 経由のテスト) で確認

### Phase 2.3: native JIT routing を切り替え

- cps_repr_cranelift.rs の `yulang_cps_route_scope_return_i64` を変更
- bug repro `for+say+tail` ケースで `(5, "0\n")` が返るか確認
- yulang-native 192 tests + solved/ snippets で regression なきか確認

### Phase 2.4 (任意): threshold field を削除

- 確認: Phase 2.1〜2.3 で `return_frame_threshold` 参照が全部消えていたら field を削除
- 残ってる参照を 1 つずつ marker ベースに移植

---

## 8. 既存テストとの互換性

### 影響を受けると思われる test

- `runs_var_update_in_for_loop_through_cps_repr`: md round-6 で「prompt_exit を入れる WIP では `["0"]` で落ちた」と書かれている。今回は marker を追加するのではなく **既にある marker を routing 側でも使う** だけなので、不変条件が成立する限りは旧 threshold と一致するはず。
- `runs_junction_method_undet_once_through_cps_repr`: 同上、別途確認。
- `runs_undet_once_open_range_guard_through_cps_repr`: 同上。

### 不変条件破れの検出戦略

Phase 2.1 で `debug_assert_eq!` を入れて、旧 threshold と新 marker-rposition が
食い違ったケースを **テスト失敗として表面化** させる。
乖離が出るテストがあれば、それは「shallow handler の境界がそもそもズレている」
ケースであり、本バグと同じ root cause なので、修正対象として正しい。

### 退避戦略

各 phase の前で git commit. Phase 2.X の test が落ちたら、その phase だけ revert
できるようにする。

---

## 9. 残された懸念 / 未決

- `merge_extras_into_frames` 周りで、resume-site の extra frame に `prompt_exit` が
  set されないケースがあるか. set されない場合、capture 境界がブレないか.
- shallow handler の `k v` で resume された continuation の中で再度 handler が
  install される時、新しい prompt がぶつからないか (fresh_prompt なのでぶつからないはず、
  ただし trace で確認したい).
- threshold を削除した時、`owner_initial_frame_count` 等の他のフィールドが
  threshold ベースで計算されていないか.

---

## 10. 次の確認待ち

このドキュメントに対する方向性確認。OK なら Phase 2.1 (cps_eval routing 切替) から
着手する。
