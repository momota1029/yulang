# Cycle254: 個別入力readbackから出力深さへ
開始2026-11-18T10:35:05Z。最新integration155c7aa0c、I50継続。
前回253全公開treeと手元bytes一致、前回completed、実行中writerなし。

## 先に閉じる主張
実Frame、Holds model、ground Inputs labelsがある任意のplanについて、
全inputNamesの各nameに、model(binder name)と同値な閉じた正規Patternが存在し、
そのencode sizeとconstructor depthをsource labelsのmassで抑える。
253のcoveredHeadやwhere非空は要求しない。代わりに実完了inspectionから
Complete query、正規化済みtemplateからcanonical shapeを導く。

証明経路:
1. finiteな親Patternの実observational projectionは、親以下のsizeの
   finiteな子Patternを持つ（既存inversion/project_valueを用いる）。
2. query.variablesの複数nameは各々同じprojectionを参照する。
   名前ごとのboundを証明する。複数nameのsizeを足したjoint boundとはしない。
3. Complete translationで各head input nameが失われない既存定理を使い、
   実head schemaとsource labelへ接続する。
4. produced child outputとassociated RHSへの接続は、この定理の後に進める。

## 停止性との境界
これは各modelのreadback存在であって、全model共通の実行producerではない。
全source Step Acc、source pool閉包、private非流出、strict progressは残る。
狭いnamed-output poolの閉包は253で診断済みなので再実装しない。
規則の変更も意味論の選択もしない。I49のsource反例停止条件に該当する
新しい反例が出た場合は、該当依存を止めて分析を記録する。
