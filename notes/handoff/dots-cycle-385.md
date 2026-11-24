# Yulang cycle 385

閉じた補題なし・分けた補題: S13 → S13a, S13b

I-68 に従い、今回は S13 だけを分けた。[更新した一覧](../design/dots-cycle-380-i65-step1-skeleton.md)には、どの補題が構造の証明で必要か、どの補題が組立時に前提を供給するかを区別した作業順を載せた。S12 は各 node の意味に S09 を実際に使う。一方 S13 は同一モデルの意味を引数で受けるので、S12 の定理を証明本体で使わない。S13 で未定義の一般 carrier を既存の限定版とみなして閉じたことにはしなかった。

- **S13a `general_literal_replay_alignment`（未証明）:** 同じ元 replay から出現を落とさず canonical tree に対応づけ、元の where 子順・各固定出力の literal ordinal/target・全 receipt の正確な列を取り出す。モデルや一般意味は使わない。先頭の作業はこの一件。
- **S13b `aligned_general_meaning_to_dictionary`（未証明）:** その出現に対応づけた全ての型・行の意味を同じモデルの `DictionaryEvidence` として返す。表示添字 `(s,m,q,d,written)` が一致するだけで、独立に与えられた source event を同一とはみなさない。出力がない節点では空の書込み列も事象を同定しない。一般 carrier の導入／反転で接続を示す義務を残した。新しい `Fits` や同一性の仮定は元 S13 には足さない。
- 両子を使う元 S13 の合成を一覧に明記。S13 の原文、固定 `dictionary_sound`・`check_sound` と最上段の証明骨格、S01–S12 の文および状態はそのまま。今回 Lean ファイルは増やしていない。

**未解決 14 件 = 未証明 4 件（S01、S10、S13a、S13b）＋ 一部 10 件（S02–S09、S11、S12）。** 親 S13 と証明済み再利用 P01〜P04 を重ねて数えない。I-65 Step 1 は未完、Step 2・3 は未着手。S1/S2 未完、C は後回し。停止性・旧 `Local`・旧 C334・fixture・言語の受理範囲・K2 優先・release 権限の層は変えていない。選択結果が実行順に依存する承認済み例には当たっておらず、意味問い合わせは起票していない。

## 確認

- 前周 `244e6ad3c2032e45e0faea7827f1af5b41028212` の完了心拍・報告、`integration/m1-final` `ac5ad01366d274d521c54a75d372d6d0cc1831aa` の常設指示、役割／推論仕様と I-68 inbox blob `8fcff32329234b9cc304a919051d1c30e03542aa` を読み直した。開始 2026-11-24T04:30:43.534Z UTC（入口で記録）。
- immutable integration の `lean/Yulang/GeneralDeclarativeI65*.lean` 78 ファイルを Git blob と照合し、一覧の一般名 `GeneralTree`、`GeneralTreeMeaning`、`LiteralTreeFrom`、`SourceTreeTrace`、`DictionaryEvidence` はその範囲で見つからなかった。C365 `SourceTree` は ordinary、C368 `ReceiptTree` は既存の ordinary/unary 型付き範囲、C384 `ExactWhereLowering` は C365 への条件付き lowering。C381 `root_event_no_diagnostic_recovery381` は異なる二 event が独立に許される場合の非復元であり、実言語に曖昧例があるという主張ではない。C368 の `every_written_receipt_in_one_model` は membership 投影で、木の同一性を返さない。
- 一覧の元の最上段・S01–S12・S13 の原 Lean 文が exact bytes で不変と突合。公開は `work/dots-main` のみ expected-head / non-force、累積 3 paths（一覧・心拍・報告）。Lean tree は C384 と同一で、凍結2ファイルは blob ID のみ確認。新しい Lean 定理はなく、全体ビルド・CI・Rust は未実行。次の S13a に向けて、上の既存四つの anchor の閉包 3,902 source blobs を正本と比較し、既存 3,881 artifact の source 依存が一致する範囲を再利用、残り 21 本の既存 Lean を 4.35.0 / `--trust=0 -DwarningAsError=true` で別出力先に再構築した（exit 0）。既存 anchor の `#check` と `#print axioms` も exit 0、標準 `propext`, `Classical.choice`, `Quot.sound` の範囲（C381 非復元は公理なし）。これは既存 dependency 検証で、S13a/S13b の型検査・証明ではない。使用量の枠は不明。
- 最終照合開始 `2026-11-24T05:20:47.561Z`（50 分経過）。
