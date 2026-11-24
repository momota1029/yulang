# Yulang dots cycle 380 — I-66: I-65 step 1 の証明骨組み

## 結果

I-66 に従い、開始心拍の後の最初の成果として [証明骨組み](../design/dots-cycle-380-i65-step1-skeleton.md) を公開した。初版は `0d181f649f20cc8f171a68ded16d61e91cf3303e`。同じ一つのノートを監査し、最終 blob `b3ef15182f1271c1bb452564cd24f764576b3356` を確認した。固定した `dictionary_sound` は逐語一致。骨組みは、独立な分類から選択を含む実 source trace、局所の順序付き receipt、有限の辞書木、同じモデルでの意味、固定結論の順につなぐ。元の定理はまだ証明していない。

- 最上段から不足している `Classifies` と `DictionaryEvidence` の接続も S01/S13 に数えた。C357 の限定定理の `SourceChecked`、`Coverage`、`Declared` を固定定理の新しい仮定にはしない。同じ key の別イベントを混同しないよう、実出現を明示の添字で運ぶ。
- root K2 と、支持のある lower が開く候補検査を分けた。片付いていない出力を展開の支持にせずとも、等式は K2 グラフに残る。C379 の真の unary dispatch と C368 の実普通位置を再利用するが、任意の候補・位置の全順序を実証したわけではない。
- C365 の `Current/Fits` から C360 の現在の write 盤面と独立 grant への接続は自明でない。同じ状態の実作者・版・source/output ordinal・固定 target を保つ S07 と、同じモデルで解釈する S09 を区別して数えた。出力の同値や grant の後付けで埋めない。既存の typed receipt には unary 値の範囲制限がある。

## 残り（I-66 の行 ID）

- S01 未証明 — `classifies_unpacks_actual_source`
- S02 一部 — `selected_source_inversion`
- S03 一部 — `selected_mixed_k2_priority`
- S04 一部 — `elected_occurrence_has_general_head`
- S05 一部 — `selected_actual_ordered_capture`
- S06 一部 — `selected_ordinary_literal_receipt`
- S07 一部 — `selected_typed_actual_owner_and_retention`
- S08 一部 — `ordinary_or_typed_node_assembly`
- S09 一部 — `general_local_meaning`
- S10 未証明 — `selected_frontier_to_general_node`
- S11 一部 — `lower_selected_general`（tree/forest を返す一補題）
- S12 一部 — `general_tree_sound`
- S13 未証明 — `general_meaning_to_dictionary`

**未解決 13 件 = 未証明 3 件（S01・S10・S13） + 一部 10 件（S02–S09・S11–S12）。証明済み再利用 P01–P04 は別。** 次は S01 の独立 source/診断 API から一件ずつ進める。I-65 step 1 は未完、step 2/3 は未着手。S1/S2 は閉じていない。C は後回し。停止性・旧 `Local`・旧 C334 接続・fixture 拡大は対象外。

## 検証と公開

- 正本 `integration/m1-final` pinned `a4bfae3c7ea3baf8212ead8c79db84408fcf5ec6`。inbox `b99fbb19f8c0c8c05abcd09f4cf3f44cfd4de26e`（I-66）、roles `2732b1d76476e382489803943a9f44fa18aef544`、inference `60008e0edd66649f48d9ab387d7892b6037138d0`。I-65 関連 46 モジュールは C379 work とこの integration の blob ID が全一致し、取得した全文から Git blob ID を独立再計算して照合した。
- 固定文を逐語照合。S13 に必要な S01–S13 の依存は循環なし。62 件の再利用先と 4 件の証明済み補題を、integration の不変ファイル/宣言の行に照合した。P01–P04 は署名も原文と照合した。これは設計と出典の監査であり、未証明の文の Lean 検査ではない。
- `work/dots-main` の設計、公式心拍、handoff の 3 パスのみ。全変更は expected-head の non-force 公開。Lean tree `fe6b1df127b876ff889f0d46788c089e04df9feb` は C379 と同一。凍結2パスは metadata だけ照合し、中身は読んでいない。新規 Lean、focused Lean/Audit、全体 Lake、Rust の実行なし。質問ノートなし。使用量の枠は不明。
- 開始 `2026-11-23T23:30:43.451Z`。最終照合開始 `2026-11-24T00:20:56.437Z`、約50分。範囲外の次作業へは移っていない。
