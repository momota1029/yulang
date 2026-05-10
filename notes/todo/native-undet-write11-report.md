# native-undet-write11 実装レポート

## 実装したこと（write11.md 指示ベース）

### 1. Prompt-aware ScopeReturn（旧 Aborted の置き換え）

`CpsRuntimeValue::Aborted` を廃止し、`ScopeReturn { prompt, target, value }` に移行。

```rust
ScopeReturn {
    prompt: CpsPromptId,        // どの InstallHandler インスタンスか
    target: CpsContinuationId,  // ジャンプ先（EXIT_RWH_TARGET = usize::MAX は RWH 専用）
    value: Box<CpsRuntimeValue>,
}
```

`CpsPromptId` は `InstallHandler` 実行ごとに `fresh_prompt()` で払い出す動的 ID。
再帰的なハンドラインストール（once の中で once を呼ぶ等）を正しく区別できる。

---

### 2. escape フィールドの IR 追加

`CpsStmt::InstallHandler` に `escape: CpsContinuationId` を追加。
ハンドラスコープの腕ボディが non-local return するとき、`escape` が指す継続にジャンプする。

**重要**: `escape = merge_cont`（value_cont ではない）。
value_cont を指すと、腕ボディのリターンが value arm を再適用してしまう。

---

### 3. `inherited` フラグと `into_inherited()`

```rust
struct CpsHandlerFrame {
    // ...
    inherited: bool,  // true = resumption/呼び出し元から引き継いだフレーム
}
```

`eval_continuations` の先頭で `active_handlers = into_inherited(active_handlers)` を呼ぶ。
引き継いだフレームは `ScopeReturn` を解決しない（= Perform のキャッチはしても、ScopeReturn の着地点にはならない）。

これにより「内側の eval フレームが外側の once の ScopeReturn を横取りする」バグを防ぐ。

---

### 4. handle_scope_return / dispatch_scope_return! マクロ

`handle_scope_return` が ScopeReturn の届き先を判定し、`ScopeReturnAction` を返す。

```rust
enum ScopeReturnAction {
    Value(CpsRuntimeValue),
    JumpOrExit { target: CpsContinuationId, value: CpsRuntimeValue },
    Propagate(CpsRuntimeValue),
}
```

dispatch マクロにループラベルを渡す形式（`dispatch_scope_return!('cont, result, dest)`）で、
`continue 'cont` を正しくループラベルに向ける。

---

### 5. ForceThunk の再帰ループ

once の branch 腕が `Thunk` を返すケースがあるため、ForceThunk を再帰的に剥がすループを追加。
`ScopeReturn` が来たらループを抜けて dispatch。

---

### 6. Phase F.5 step 5（return サイトでの force 挿入）

`lower_root`, `lower_lambda`, `lower_recursive_lambda` の return 直前に
`force_if_non_thunk_demand` を挿入。これで thunk ラップされた値が最終値として漏れ出るのを防ぐ。
3 つのユニットテストのゴールデンを更新済み。

---

## テスト状況

- **170 テスト PASS**（write11 実装後）
- `compares_std_undet_once_scalar_unwrapped` → PASS
- `debugs_std_undet_once_skip_eval_layers` → **FAIL（vm:2, cps:0）**
- Cranelift 系の once テスト群 → 全 `#[ignore]`（未着手）

---

## 残存バグの根本原因

### 症状

`work()` 内でガード（reject path）を持つ `once` が、CPS では 0（nil）を返す。
インタープリタ（VM）は 2 を返すため、意味論的に間違っている。

### 何が起きているか

```
outer_once (H1, queue=[])
  └─ inner_once (H2, queue=[])
       └─ work() — n を perform_undet, ガード判定
            ├─ n=1 → guard fail → reject
            └─ n=2 → guard pass → return 2
```

1. `each` の CPS グラフ内で sub::return が発火 → ScopeReturn(H_sub) が上向きに伝播
2. `each` の eval フレームで H_sub を非 inherited フレームとして検出 → escape(merge_cont) にジャンプ
3. `each` が 1 を返して `work` に戻る
4. `work` が n=1 → guard fail → **reject を perform**
5. この時点で **inner_once の H2 eval フレームは既に終了**（sub::return で短絡したため）
6. 残っている active_handlers は outer_once の H1 のみ（queue=[]）
7. H1 の reject ハンドラ → queue 空 → nil を返す

### 本質的な問題

`Resume(k_true_thunk, true)` の eval フレームは sub::return 発火後に exit する。
その時点で inner_once の H2 フレームも消える。
`work` のリジェクトは「H2 が生きている内側の once のコンテキスト」で起きるべきだが、
そのコンテキスト自体が消えている。

`extra` ハンドラ（Resume 時に outer から継承）を試みたが、
Resume eval が exit した後の work の perform には届かない。

---

## 未解決の設計問題

**Q: k_true_thunk を Resume するとき、work の継続（reject 以降も含む）を
inner_once の catch 境界まで含めてキャプチャするにはどうすればいいか？**

候補 A: `once` の branch 腕で plain `Resume(k, true)` ではなく
`ResumeWithHandler(k, true, H2)` を生成する lowering に変更する。
これで H2 が k の resume スコープにインストールされ、reject が H2 を見つけられる。

候補 B: `Resume` の eval フレームが終了する前に work の残り継続をキャプチャ
（= "delimited continuation" を明示的に reify）し、inner_once のスコープで実行し直す。
実装コストが高い。

**→ 候補 A が最も現実的。lowering 側で `ResumeWithHandler` を使うか、
once の CPS 生成を「k を resume するとき、現在のハンドラ H2 を引き継ぐ形」に変える。**

ChatGPT Pro（りな）への確認事項:
1. `once` の branch 腕内で `k` を resume するときに H2 を明示的に渡す lowering は正しい方向か？
2. それとも eval レイヤーの「捕捉範囲」を広げる別の方法が適切か？
3. `ResumeWithHandler` を lowering から直接生成する場合、ハンドラ ID はどう渡すか？（静的に既知？動的に lookup？）

---

## コミット予定

- write11 実装の全変更（ScopeReturn, inherited, escape, Phase F.5 step 5）
- 上記のバグは未修正だが、170 テスト PASS の状態でコミット
- Cranelift フェーズは次セッション以降
