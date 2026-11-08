# spec追記案（監査cycle 1）

確定した追記案はまだない。spec/ は変更していない。

- F1は既にspec05 §5.5cにある。欠落していると主張する対象はspecの文言ではなく、Common矢印比較との接続位置である。質問ノートを分離した。
- private helperのcopy、pipe引数位置、pattern OR/as/注釈/refutable binding、else無しifは旧文書との違いだが、新specの明示変更をY2復元で上書きしない。
- cast曖昧性は旧文書と旧実機自体が食い違う。実機の先頭採用を規則に昇格しない。
- error record payloadは旧文書が古く、今回のY2 constructor実行は新specと一致した。
- role residualのvariance反転・共起簡約は旧文書と既存unitの一致を確認したが、新spec/Leanの全接続の不存在は確定していない。次回に範囲を絞って確認する。

- narrower errorの直接wrapは実機でunhandled、明示up→wrapは成功した。新specの意味核を書き換える理由にはせず、source生成と実行の境界差として継続監査する。
