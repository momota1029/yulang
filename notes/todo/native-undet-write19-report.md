---
title: native-undet-write19 実装レポート
date: 2026-05-11
---

# native-undet-write19 実装レポート

## 結論
- 既存 167 テスト PASS（regression なし）
- `debugs_std_undet_once_skip_eval_layers` は **依然として cps:0**（vm:2 にはまだ届かない）
- write19 §step 1〜5 の trace 強化を実施し、root cause を **multi-shot resumption の ScopeReturn 伝播が intermediate handler eval を破壊している** ことに絞り込んだ。case A/B/C のどれでもなく、**case D (intermediate handler destruction)** が正しい分類。

---

## 実装したこと（trace 強化のみ。意味論変更なし）

`crates/yulang-native/src/cps_eval.rs`:

### 1. `summarize_cps_value(value)` helper を追加
`CpsRuntimeValue` をコンパクトに表示する整形ヘルパ。
- `Plain` → `Plain(VmValue)`
- `Thunk` → `Thunk(owner=..., entry=...)`
- `Closure` → `Closure(owner=..., entry=..., recursive_self=...)`
- `Resumption` → `Resumption(owner=..., target=..., frames=N, handlers=M, guards=K)`
- `List` → 先頭 3 件 preview
- `Tuple` → 全件 preview
- `Variant` → tag + nested summarize
- `ScopeReturn` → `ScopeReturn(prompt, target, value)`

### 2. `EffectfulApply` trace を強化
callable / arg / return_frames.len / initial_frame_count を全部 dump。
arg は `summarize_cps_value` で構造を見せる。

### 3. `CpsStmt::ApplyClosure` trace を追加
callable / arg / return_frames.len / initial_frame_count を表示。
（sync apply 経路の挙動を把握するため）

### 4. `PrimitiveList` trace を追加
ListEmpty / ListSingleton / ListMerge / ListLen / ListIndex / ListIndexRangeRaw を、
opcode + 引数長 + 結果サマリで表示。

### 5. `InstallHandler` trace を追加
handler / prompt / escape_owner_function / threshold / handlers.now を出力。
（handler frame の活動状態を frame chain と同時に追える）

すべて `YULANG_CPS_TRACE_FRAMES=1` 環境変数 guard。

---

## trace 分析（決定的な観測）

`YULANG_CPS_TRACE_FRAMES=1 cargo test -p yulang-native debugs_std_undet_once_skip_eval_layers -- --ignored --nocapture` を実行。

イベント順:

1. **第1 iteration: branch arm 発火**
   - `Perform branch` (each cont 5)、`active_handlers=[(0,T,1), (1,T,0)]`
     - 0 = outer once (threshold 1)
     - 1 = H_sub (threshold 0)
   - outer once の branch arm が選ばれ、k1 を queue へ
   - `ListSingleton + ListMerge` で queue=[k1] 構築
   - `EffectfulApply once cont 9` で recursive loop を起動
     - callable=Closure(loop)
     - arg=List(len=1, [Resumption])

2. **recursive once eval 起動**
   - `InstallHandler once cont 3 prompt=2 threshold=1`
     - これは内側 once のハンドラ。**prompt=2 で別 eval として live**

3. **callback 内で sub::return 発火**
   - `Perform sub::return` (callback の post-branch)

4. **ScopeReturn(prompt=1) が伝播**
   - 5 つの eval frame を貫通: each → once(prompt=2) → outer once → each → fold_impl
   - 各 eval が ScopeReturnDispatch で `Propagate` を返し eval が終了する
   - **問題はここ**: prompt=2 の recursive once eval が ScopeReturn 通過で「終了扱い」になり、queue=[k1] を保ったまま消える

5. **6 段目で matched=yes**
   - `fn=each owner_match=yes threshold=1 JumpOrExit`
   - each は `Plain(Int("1"))` を返す

6. **work が gt(1,1)=false を計算**
   - `Perform reject` (guard cont 4)

7. **reject 時の active_handlers**
   - `active_handlers=[(0,T,1)]` — outer once しか残っていない
   - **prompt=2 の recursive once は消滅済み**

8. **outer once の reject arm 発火**
   - 環境内の queue は **初期空** (= `[]`)
   - 期待された queue=[k1] は recursive eval と一緒に消えた
   - `uncons([])` → `Variant(nil)`
   - once は nil を返す → root は `Int("0")` → cps:0

---

## case 分類（write19 §guidance より）

- **case A (recursive loop が呼ばれていない)** ❌
  - trace で `EffectfulApply once cont 9 callable=Closure(loop) arg=List(len=1)` 確認
- **case B (recursive loop は呼ばれるが queue が空)** ❌
  - recursive loop は queue=[k1] を持って起動している
- **case C (reject の Perform 位置が想定と違う)** ❌
  - reject は work の guard で正しく発火している
- **case D (intermediate handler eval が ScopeReturn 伝播で消える)** ✓ ← 新規分類
  - work が sub::return を返す前段の ScopeReturn(prompt=1) で、
    prompt=2 の recursive once eval frame が終了する
  - その後 work が reject を出しても prompt=2 はもう存在しない
  - 結果 reject は outer once（queue=[] のまま）に拾われる

---

## なぜそうなるか（意味論レベル）

algebraic effect の正しい semantics では:
- `sub::return n` は **H_sub のスコープから抜ける**
- H_sub は each の内側に張られている → each の中で完結
- recursive once（prompt=2）は H_sub の **外側** に張られている →
  **本来 ScopeReturn(prompt=1, H_sub) 通過で死ぬべきではない**

現在の CPS eval は ScopeReturn を見つけた frame を一律に終了させているため、
prompt=2 eval が「途中で巻き込まれて」しまう。

multi-shot resumption の場合、resumption を applied したときに張られた
**外側のハンドラ scope は、resumption 内部からの ScopeReturn では破壊されない**
ことが期待される。これは delimited continuation の prompt 境界に当たる。

---

## write20 で取るべき方針（仮）

A. **ScopeReturn propagation の境界条件を見直す**
   - prompt と eval frame の対応を厳密化
   - 「自分の prompt にマッチしないが、自分の上に積まれた別 prompt の handler を持つ」
     eval frame は ScopeReturn 通過で終了せず、再開を待つ

B. **handler scope を resumption replay 時に再構築**
   - resumption invoke 時、当該 resumption が capture した「上の」ハンドラ群を
     一時的に push し直す
   - 既存の `adjusted_frames` 経路を拡張

C. **prompt ベースの delimited continuation を厳密化**
   - 各 eval が「自分の prompt が含まれるか」だけで Propagate / Terminate を判定
   - 現在の `inherited` フラグだけでは足りていない

write19 では実装変更を入れず、write20 でりなと方向性を相談したい。

---

## 触ったファイル

- `crates/yulang-native/src/cps_eval.rs`:
  - `summarize_cps_value` helper 追加
  - `Return` trace を値表示込みに（write18 から継続強化）
  - `EffectfulApply` trace を callable/arg/frames で強化
  - `CpsStmt::ApplyClosure` trace 追加
  - `PrimitiveList` trace 追加
  - `InstallHandler` trace 追加

---

## りなに渡す質問

1. **multi-shot resumption の ScopeReturn 境界**:
   現在 ScopeReturn(prompt=p) は途中の eval を全部一律に終了させている。
   本来 prompt 境界以外の eval は live のまま残るべきで、resumption replay 時に
   再開できる必要がある。これは:
   - delimited continuation の prompt-based scoping を厳密化する方向
   - resumption invoke 時に「上の」ハンドラ scope を再 install する方向
   どちらが yulang の意味論と整合するか？

2. **CpsReturnFrame の owner_function / prompt 連携**:
   現在の `escape_owner_function` は ScopeReturn 通過判定に使っているが、
   prompt id との二重管理になっている。prompt 単独で判定できるよう整理しても
   問題ない？

3. **trace で次に確認すべき点**:
   - prompt=2 の recursive once eval が「ScopeReturnDispatch で Propagate を
     返した瞬間」のスナップショット（queue / handlers / frames）が欲しい
   - そこから write20 の修正ポイントが具体化できそう

---

## コミット予定

write19 完了。
- trace 強化（summarize_cps_value + ApplyClosure/PrimitiveList/InstallHandler）
- root cause 分類: case D (intermediate handler destruction)
- 意味論修正は write20 へ
