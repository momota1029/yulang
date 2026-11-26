この周に閉じた C の行: C21（順序付き `ref _ 'a` の限定範囲、`RefPositions441.dictionary_sound_R21`・`check`・`check_sound`）

# cycle 441 — ref の本来の row/value 位置

実開始 2026-11-26T12:30:54.707Z。通常の 50 分ゲート以降に報告を確定。実経過と exclusive worker release は同じ commit の canonical heartbeat。使用量の枠は不明。

## 依頼・完了した範囲

I‑74 の C21 一行のみ、I‑78 / I‑79。元の C423 の定義、正本 spec §6.2 L57 の `impl Add (ref _ int)` の `_` は独立の binder、§4.6 L221–235 の順序は row `'e`・value `'a`。開始時正本 `integration/m1-final@2e47eb95797eda5d68d1b62ac1664fe07cb1d2c5` に C440 exact 採用済み（Lean `5d57993d91ace99c523aaca4b6d8804d4b1498aa`）。手元 work の古い spec が正本と一致するという主張はしていない。正本 spec を読み、spec を更新していない。

限定した実入口は **where / 固定出力なし、可視候補一つ、元の point origin から読む `ref _ 'a`**。row と value の binder は別々、元の引数は `[inr row,inl value]`。row covariant と value invariant を宣言された projected run body から導出し、既存 table の順序と一致させる。実 run の field-local `'f` を公開型引数に足していない (`B3` の rank-2 下げは別)。

1. 実候補テープの元の ordinal と `DeepRead` から、同じ state/request の `actual_ref_selected_trace441` を構築。実 row scope と value の捕捉を同じモデルの別の型付き channel で保つ。独立 local rule と `ref_only_dictionary_sound441` は既存 `I72.DictionaryEvidence.node` を使用。`dictionary_sound_R21` は任意の元 state/request/dictionary、任意のその適合モデルで同じ固定 evidence を返す。
2. `.reference` witness は origin index と有限 raw escape データのみ。mode/答え/捕捉を信頼して受け取らない。全過去 witness の Bool は定義的に同じ。未フィルタの元 raw root K2 は旧拒否として優先し、深部の variable binder の中身を調べているとはしない。
3. 任意の Problem/Result/Witness が true なら元の state での分類と、その全適合モデルで同じ報告・元の `WindowMeaning`・実 row/value capture の意味を返す固定外形 `check_sound`。native source syntax に対して、生の ordinary root 値が mixed nominal 全体と同値だと推定しない。

[実入口と scope](../design/dots-cycle-441-c21-verified-entry.md)。実 signed effect `(56,[1,-2])` が row channel、Int が value channel の具体的適合モデルを構成。public checker true、Mode の両 formal が projected run の同じ owner root を持つ入力も true。endpoint/mode/author の取り違え・同一 binder 再使用・rival・違う report では scoped check false。元の root raw K2 は prior true/new false。見ない regular value leaf の cycle、同じ数値名が row/value の別々の channel を持つ正例、C440 の実 prior witness も個別検証。各同一 State の適合モデルでは、二つの accepted wire が捕捉した row/value の**各元の名前**が一致する ([fidelity](../design/dots-cycle-441-c21-source-fidelity.md))。

## literal の境界と比較で得たもの

- [mixed comparator](../design/dots-cycle-441-c21-literal-boundary.md) は既存 compiler そのもので、通常は順方向の row 1 atom に value invariant 4 交差を順に足す。反転した位置は admit しない。inherited invariant では 4 row + 4 value を順に保持。型 Int が同じでも実 signed row の forward と backward を同じモデルで識別。
- 文字どおりの **`ref _ int` は未実装**。元の scope が実 singleton literal の Problem、その exact `[row,type]` metadata と適合モデルを用意し、既存の typed comparison が成立しても、fixed named `SourceHead` では選択の証拠を作れないことを検証。旧 centered path は混合 arity kind を受けず、既存 `DeepRead` に ordinary scalar を rigid nullary `.app int []` と読む節がない。literal 区間の比較可能性は matcher の代用にならない。任意の既存 named `SourcePrimitives` の local rule を差しても同じ literal の `Event.head` にはならない。この証拠形式の境界を、言語の拒否／false な推論結果とは言っていない。独立対照の本物のゼロ引数 nominal `Token` なら、元の named `SourceHead` が構成できる。scalar に対応する別の typed leaf evidence の表現と正式な採用が残る。
- field-local `'f` の rank-2 source lowering・任意 where/output・一般完全性、停止性、証人生成／Rust は今回の範囲外。旧既存の意味論はそのまま。質問ノートなし。C22 未着手。

## 検証・公開

- 科学 pin `658106bae52323f830bec55a8ee3349b2815774e`（Lean `f9471c73c28ed615317a4de8ff847af8b093e97d`）。6 production と 7 standalone Audit、全部で 13 immutable Git blobs を再取得し、独立検証で official Lean 4.35.0 `--trust=0 -DwarningAsError=true` 個別 exit 0。47 standalone audit 宣言は標準公理のみ。4,083 / 4,083 focused old dependency source provenance が正本と一致。全体 `lake build` / `tools/verify-lean.sh` / Rust は走らせていない。
- Audit の import: `Yulang.*` 以外 0 件。[完全な axioms 出力、Git blob と再現](../design/dots-cycle-441-c21-verification.md)（blob `ca2a535fda61549d5a5eb54199379f6feb066508`）。凍結 `Audit.lean` / `README.md` は metadata IDs のみ確認。既存 Lean/notes/spec の削除・置換なし。元の barrel の 375,968 bytes を保持し 6 import append。
- 差分 **22 paths**（6 production、7 Audit、barrel、6 今周 design notes、canonical handoff と heartbeat）。期待した先頭に対する nonforce で `work/dots-main` にのみ公開。exact canonical report / coverage / HB と Lean tree を再取得照合し writer release。

最終照合時の正本 `integration/m1-final@2e47eb95797eda5d68d1b62ac1664fe07cb1d2c5`（Lean `5d57993d91ace99c523aaca4b6d8804d4b1498aa`）に C441 の exact 13 blobs はまだ揃っていない。C21 の scoped 完了は `work/dots-main` 上。正式取込・監督役の全体検証は別。

**C の残り: scoped 一覧の 1 行（C22）。** [coverage 一覧](../design/dots-cycle-441-c-coverage.md)
