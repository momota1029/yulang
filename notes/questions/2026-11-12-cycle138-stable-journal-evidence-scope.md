# I-23 の安定状態限定でも残る raw journal の反例

## 第一案: 判断を保留し、現 target / Astra の定義を変更しない

今回 `GeneralDictionaryRefreshGap.no_evidenceNode` が、変更されていない
`B4SkeletonV4.EvidenceNode (GeneralDictionaryFeedbackEvidence.boundary roles)`
の否定を証明した。I-23 により Stable を追加しても、任意 raw state を量化する
現在の型では証明不能である。既存の13フィールドのうちこの具体的な1義務を
未解決ではなく「反証済み」として区別し、監督役の判断を待つ。

## 最小の状況

意味的には list 引数に対する terminal 辞書の選択で、関連出力には int が必要。
source0/list と source1/要素の両方について int モデルと string モデルが残る。
可視の宣言キー40を選択する一方、同じ需要identityの古い不可視キー41がjournalにある。
古いpacketは関連出力を要求していないため、stringモデルを排除しない。
しかしキー衝突で40のinstallationを止める。exact refreshは両モデルを保存するので
source1を単一の既知headへ変えられず、enqueue/merge/equateも新たに行えない。
実際の Stable と selected40[] が成立するが、stringモデルで親Evidenceは偽。

これはYulangプログラムからこのjournalが得られるという主張ではない。
`not_sourceFormed` は既存SourceFormedではこの状態を作れないことも証明している。
従って言語意味論・到達可能入力の不整合は示していない。source syntaxを捏造した
実行例ではなく、現在のLean proof-interfaceが要求するraw stateの反例である。

## 監督役に必要な判断

この橋の対象を既存 `SourceFormed` または実際の初期化から到達可能な状態に
限定する構成を、どの層で行うべきか。例えば状態型に形成証拠を保持する境界か、
骨格側で初期状態/到達性を運ぶ形か。単に追加の健全性仮定としてEvidence/Jointを
置く修復は選ばない。今回、いずれの変更も行っていない。

独立作業は継続した: 空journalからの実際のordinary/固定view-refresh traceに沿う
全記録の現在Instance不変量、記録網羅性+Accによる有限辞書構成、SourceFormedの
モデル不要な可視性、およびsingleton registryの実selectedキー整合性。
これらは境界の修復を勝手に承認したものではなく、未証明の一般義務を隠さない。

## 監督役の判断（2026-11-12）: 骨格と target に「初期状態」と「到達可能性」を入れる（I-25）

承認済み草稿の「任意の状態 Σ」は、通常の制約と共有グラフ（区間を含む）であり、solver の内部の journal（packet・site・alias）を含まない。具体的な境界の `State` は journal を含むので、「任意の raw journal」を量化するのは草稿の量化子より強い。したがって、草稿の Σ を「journal が空の初期状態」（具体的には `InitialSource`）として埋め込み、橋の義務は**その初期状態から実際の Step で到達できる状態**だけを量化するのが忠実な翻訳であり、言語の意味は変えない。詳細は inbox I-25。
