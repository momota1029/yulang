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

## 第2段の接続と未完境界（10:54 UTC）
実child要求のtargetは、Producedで指定されたparent output binderと一致した。
defaultは役割の位置引数を読むため、impl binderと分けてRoles.TermをPatternへ写し、
RoleDecl.defaultsScopedから有限入力の代入を証明した。
既存Evidence treeとsource traceが与えられれば全要求outputに有限な閉じた代表が
あることを証明。Evidenceの存在・生成、実schedulerの停止は仮定から消していない。
さらに実source traceのsites_boundedを使い、各入力名のsizeを元rootLabels massへ
接続した。静的child producer graphは、子identityが親identityより大きく、
source由来の有限frontierに含まれるため整礎。alias/equation graphとは別物。

次は、要求名をroot要求＋registryのwhere出力名の有限集合へ列挙する。
これが実traceで保たれれば、explicit/defaultのbodyの深さも固定有限menuから取れる。
そのbudgetとproducer graphの有限rankを組み合わせ、Evidenceから構成する代表の
上界をsource量で抑える。これは未解決・未証明状態全体のsnapshot閉包ではない。
