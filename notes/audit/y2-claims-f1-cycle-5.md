# F1 audit cycle 5: finite effect-count matrix

旧Y2 `d4c8bc8fc`、新spec `integration/m1-final@9b619434c`。rawソース/コマンド/出力は runtime-cycle-5-effect-count.md、controls.md、continuation-wrap.md。ordinary actualは `x:int`。handlerはpingを7で再開し、再設置したhandlerの結果へ100を加える。意味論を決めず観測だけを記録する。

|ID|出典|規則・例|実機の結果|新spec|Lean|分類|備考|
|---|---|---|---|---|---|---|---|
|F1-C5-01|effects.md Handler、新spec5.5c|unused ordinary `actual(x:int)=42` へ直接ping計算を渡す|check/mono0、VM/interpreter142|起動時放出|既存strictAppが対応する抽象規則、実source接続未確認|一致|この例では引数効果1回。raw effect-countの42-direct|
|F1-C5-02|同上|同actualをeta wrapper経由で高階へ渡す|check/mono0、VM/interpreter142|起動時放出|同上|一致|wrapperの一般的必要性は主張しない|
|F1-C5-03|同上|ordinary identityをdirect/higher/etaで呼ぶ|全経路check/mono0、VM/interpreter107|起動時放出|同上|一致|この有限3経路のみ|
|F1-C5-04|同上|ordinary `actual(x:int)=x+x` をdirect/etaで呼ぶ|check/mono0、VM/interpreter114|起動時放出|同上|一致|算術operatorは自己完結定義。1引数評価を確認|
|F1-C5-05|同上|unused ordinaryをhigherへ直接渡す|check/mono0、VM/interpreter42|起動時にpingを放出する規則と異なる|独立cast/strictAppとのsource接続は今回未検証|違う|既存cycle3の非再開handler対照を、再開して回数を数える対照で補強|
|F1-C5-06|同上|ordinary `x+x` をhigherへ直接渡す|check0、mono/run1 `[ping] vs []`|普通の関数を高階の効果付き引数へ使えるという5.5cと差|同上|違う|実行前失敗。効果2回発火とは言えない|
|F1-C5-07|effects.md Handler、新spec5.2/5.3|継続結果 `add 100 (k 7)` と `add 100 (handle(k 7))`|前者check/mono0だが両runtimeでthunk/int error、後者107|shallow continuationは行が残り、再設置は明示する|未確認|未確認|旧runtime boundary差は確定。一般的な残余行の意味や根本原因は未確定|

4一致、2違う、1未確認。新specのcastを矢印subtypeへ混ぜる変更は提案しない。既存確定の独立cast方針を維持する。分類は旧Y2実装に対するもので、新Leanの健全性を反証したとはしていない。
