# Handler の相関付き観測・分岐保存

Date: 2026-10-24
Sprint-ID: CORRELATED-HANDLER-20261024/r1
Baseline: `d52c2c48e0e876be4e3e6588e2b1b3b4b27933ea`
Contract SHA-256: `f2debbf830e4b4726af992ec6d1817090fbbd8d493c9f15c76b43c4699ae306e`
Outcome: CANDIDATE_CO3_OBS_ACCEPTED; whole-language parent OPEN

## 実際に狭くなった前提

直前の join 定理は観測言語ごとの要約を特徴付けたが、handler の否定を含む query と分岐への適用は残していた。[新しい証明](../../../notes/theory/2026-10-24-correlated-handler-observation.md)は、修正候補機械の joint cell を使い、この consumer 部分を構成した。

- H1–H2: 同じ witness と現 world に基づく P/PF/grant の query exactness、および Eligible の四場合への整理。
- 真偽の両 filter と action relation の和集合・合成法則。必要な cell quotient の判定条件。
- H3: query が偽なので候補を飛ばす場合と、実行した arm が No を返す場合を分離。後者の pending request と現在 world を Rejoin し、次候補の owner/path/grant を再観測する。
- H4–H5: 指定された有限 table 自身の全有限経路の像との一致、および具体候補実行の branch/successor を含む片方向 simulation。

保護の代替を一つの bit にまとめる lost-branch 例、No 前に L が変化する例を保存した。いずれも candidate-state discriminator であり、actual source に到達例を構成したとは主張しない。追加で提案した二候補・極値 summary の例は凍結前に導出・記載を完了しなかったため、本成果や査読対象へ数えない。

## 独立査読

Producer は `/root/astra_scoped_join`。停止・書込み終了・子なし receipt を受領して r1 を凍結後、非共著者 `/root/astra_semantics_review` が査読した。primary と dispatcher は課題の方向付けに参加しており、独立査読者ではない。

対象 SHA-256: `b1b94aa7712ef0a5be043070b042c830dfde9c16ca7874f7046a0827405eadc4`。

判定は **ACCEPTED for the specified revised finite candidate graph; no BLOCKING/MAJOR findings**。within-witness と grant 内部の相関、PF⇒P、filter の商条件、candidate 変更時の F/GC/GW、No 後の現在 L、TABLE の exactness と concrete inclusion の区別を確認した。primary はこの範囲で受理した。査読後の proof 変更は、結果への一行の receipt のみ。

失敗やその他の終端遷移を含む全 continuation semantics は、H5 の action-coverage 前提を満たす必要がある。表示した handler path 表だけで全 source coverage を証明したとは扱わない。

## 残る義務

候補の CO3-OBS はこの範囲で解消した。残るのは、全 source の graph 生成がこれら両 branch、action、現在世界の Rejoin/Prep、失敗・終端辺を含むこと、実 weight/native 表示との対応、各 pending/capture/resume owner の対応、独立した foreign continuation 契約である。全 surface、値型、元の Simple-sub A/B・主型性・停止性も未完。

統合稿 §5–7 と索引へ証明を適用した。旧 certificate が新しい table を満たすこと、全 table path が concrete trace になること、任意の A_all の採用は主張しない。次は source 導出から必須 edge を生成する構成と coverage を証明する。追加のユーザー仕様選択は求めない。

## 資源と保存

新しい予約は dispatcher30 + producer190 + reviewer80 =300 秒。以前の1500 を保持し累積1800 秒、未観測分を返却しない。要求 Astra/medium、観測モデル・effort・実稼働時間 UNKNOWN。同時 child 最大一人、全 child は最終 receipt で停止・書込み終了・子なしを確認した。background execution はない。

固定 hash、関連 manuscript、ローカル link、whitespace と file inventory を静的に確認。tests/build/compiler 実行・実装変更はなし。旧証明、質問ディレクトリ、元作業場所の未知 writer を変更しない。この記録を含む commit が統合 locator となり、専用 branch の明示した path と全送信範囲を primary が点検して non-force push する。
