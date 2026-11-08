# Cycle 11: 実producerのcapture位置

状態: 既存の単引数・unary構造断片の補助証明。言語意味論の追加なし。

## 目的と停止条件

cycle10で表へ入力していたsource IDと実producerを繋ぐ最初の橋として、実際に検査したheadからcaptureの深さを計算する。型値の等しさではなく、親endpointの構造位置を証拠にする。literal headのunknown sentinelはsource captureとみなさない。25分以内、focused buildと公開まで。

独立な判断は既存の `Inspect`。`captureDepth` は構文だけから計算し、`Inspect ... (.hit payload)` と深さの存在を前提として、その深さの元のendpointがpayloadであることを証明する。実productionに持ち上げ、where template中の変数の深さから実childに残るcapture位置を追跡する。

## B4への接続と限界

分類: soundness補助。独立判断に基づくproducer provenanceであり、全B4 exactness/completeness/principalityではない。親のlower/upperは別々の位置を持つ。synthetic wrapperをsource nodeと誤認しない。parserからのsource ID、複数引数・record DAG・更新後graphのidentityとgrowStateへの統合はなお未達。構造位置の追跡に言語設計判断は不要。
