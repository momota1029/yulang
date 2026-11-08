# spec追記案（監査cycle 1）

確定した追記案はまだない。spec/ は変更していない。

- F1は既にspec05 §5.5cにある。欠落していると主張する対象はspecの文言ではなく、Common矢印比較との接続位置である。質問ノートを分離した。
- private helperのcopy、pipe引数位置、pattern OR/as/注釈/refutable binding、else無しifは旧文書との違いだが、新specの明示変更をY2復元で上書きしない。
- cast曖昧性は旧文書と旧実機自体が食い違う。実機の先頭採用を規則に昇格しない。
- error record payloadは旧文書が古く、今回のY2 constructor実行は新specと一致した。
- role residualのvariance反転・共起簡約は旧文書と既存unitの一致を確認したが、新spec/Leanの全接続の不存在は確定していない。次回に範囲を絞って確認する。

- narrower errorの直接wrapは実機でunhandled、明示up→wrapは成功した。新specの意味核を書き換える理由にはせず、source生成と実行の境界差として継続監査する。

## Cycle 2（2026-11-08）

X1–X25 oracleと追加境界を照合した。確実な新規の仕様欠落として追記すべき条文は、このサイクルでは確定していない。X2/宣言where、未知receiver二roleの曖昧、宣言variance、optional field、field-local forallは新specに明示された選択で、旧実機との差を復元要求にしない。F1のcarrier接続は既存質問へ追記した。effectful defaultのsource境界は回帰候補として保存したが、既に許可された効果を旧実装の失敗に合わせて禁止する提案はしない。

## Cycle 3: F1配置の決定と、新規の受理境界（2026-11-08）

- 最新§5.5cはF1を独立cast判断と確定した。過去の「Common arrowへ入れるか」の問いは解決済み。標準arrowの局所iffはこれと整合し、今後も維持する。旧pure-argument subtype分岐を新仕様へそのまま移す提案はしない。
- ordinary unused argumentの高階適用でpingが起動しない対照を `y2-claims-f1-cycle-3.md` に追加した。新specは起動時放出を既に明記しているので追記すべき意味規則の欠落ではなく、旧実機/source接続の相違として保持する。
- whole-record restの返値を名前付き境界越しに射影する例は、直接lambdaの成功と対照になる。新しい型推論で「通るべき」source回帰例の候補であり、一般化schemeの完全性の証明ではない。
- §3c.5の導入文には旧 `'label next` の説明が残る一方、同節の確定箇条書きは `.again` を指定する。監査は後者を採用済みの決定として読む。意味を再決定する質問ではなく、将来の文書整合の候補。spec自体は編集しない。
