# Cycle149 module guide: provenance, materialization and mixed dictionaries

一般 V5 は 6/14 供給済・8/14 未解決のまま。以下は既存定義上の補助定理と、
EvidenceNode / GeneratedChildren の構造条件つき断片である。条件つき断片を
任意の reachable stable source の完成と取り違えない。

## 1. 実際の履歴から得られるもの

`GeneralDictionaryInstallationOrigin` は任意 SourceFormed 状態の任意の記録 packet
について、空 journal の InitialSource からの実 prefix、generated focus での実
Installable・novelty・PacketGuard つき install、その後の実 suffix を回収する。
過去の local selected は回収するが、それを現在の選択だとは仮定しない。
`GeneralDictionaryEdgeOrigin` は任意の実 edge の生成 packet を逆向きに回収する。

`GeneralDictionarySupportOrdinaryExecution` の enqueue/equate/install/merge は元の
全前提を持つ実更新だけである。各 edge に Extension を仮定せず、更新の形から
導出し、空 journal からの任意有限 trace の全 packet に拡張する。refresh と
reobserve はこの ordinary-only subclass には含めない。

`GeneralDictionarySupportSourceInvariants` は別に、refresh/reobserve を含む
すべての実 support trace について seed 保存と ordinary atom 包含を示す。
任意 SourceFormed journal packet の seed 一致、および任意有限 RecordedPath の
構文的保存は実更新から従う。

## 2. 同じモデルでの選択の回収

`GeneralDictionarySameContextSelection` / `GeneralDictionaryOrdinarySelectedReplay`
は任意 SourceFormed 状態、同じ occurrence の記録 packet、同一 context または
ordinary Extension、現在の selected と任意の現在 Models assignment を対象にする。
旧 packet の Instance をその同じ assignment のまま現在へ移し、現在 Unique から
key と子リストの一致を導く。key 一致、Joint、BranchModels は追加前提ではない。
意味的 node Evidence だけでなく、記録された実 edge による Generated children
も導く。key 一意性の一般補題自体は既存で、今回の差分は実 support 履歴との接続。

## 3. 有限 shared nominal materialization

`GeneralNominalSharedJournalPaths` / `GeneralNominalFiniteHistoricalBranch` は
任意有限 arity n、任意の名前写像 Fin n → Nat（重複可）、任意幅の端点を対象にする。
ordinary に実在する双方向 equation の有限対称推移 path から、head/端点の同値を
同じ caller model で導く。point 条件・端点 ID 一致は不要となる。

`GeneralNominalFiniteAssociatedFacts` / `GeneralNominalAssociatedSourceTransport`
は任意有限の demanded output と associated list の実 find? を扱う。無関係な
associated equation まで共通 RHS を要求しない。現在の source model、同名 binder
coherence、allocation merges、各実 output target と head の同値性から、generated
materialization を導く。未定義名が通るとは言わず、nominal 翻訳条件の下で
RequestReady iff RootDefined を分離する。

`GeneralNominalWhereAssociatedFacts` は terminal を外す。任意有限の where 節について
入力 normalize が bare variable、outputNames=[]、root と子出力の RHS が同じ nominal
binder query、実 allocated target が head と同値という条件で、実 canonicalEmit
から materialization を導く。子辞書 Evidence は別であり、where が証明済みとは
言わない。`GeneralNominalWhereRequestMembership` が元の各 clause output を実
canonical request へ順方向に戻す。

## 4. 記録済 materialization から output 制約を導く

`GeneralNominalMaterializedHeadRecovery` は nominal test と全 argument observations、
実 cross-capture equality から output 全体と inspected head の同値を導く。
`packet_request_equivalent` は任意現在 Models に含まれる実 packet.Holds を読む。
別の存在モデルや、新しい semantic equality 仮定に取り替えない。

`GeneralNominalHistoricalOutputRecovery` は全 root/where request を回収する。
outputNames=[] のとき子 target は seed と識別子から決まる実 allocation ID なので、
seed 保存と組み合わせ、現在の root/子 output equality-path 前提を削除できる。

`GeneralNominalHistoricalSelectedEvidence` / `GeneralNominalHistoricalNodeEvidence`
から `GeneralNominalRecoveredNodeEvidence` へ進むにつれて、terminal、明示 output path、
明示 seed といった条件を除いた。現在 selected の共通 Metadata/Fresh/Linked を使い、
歴史から再構築した現在 Instance と Unique を比較する。現在 key を仮定せず導出し、
現在の子 Evidence から同じ model/context の node Evidence を導く。
この経路は新しい historical edge を作らず、一般 GeneratedChildren を証明しない。

## 5. 記録がない leaf と有限辞書全体

`GeneralDictionaryLinearLeaf` / `GeneralDictionaryScalarLeaf` の shape は純構造条件。
terminal・出力要求なし・実 slot/head/query/argument lookup を持ち、nominal 版は
任意有限の injective binder map と inputNames 一致を要求する。任意の現在 source
model で BranchModels を導き、現在の選択との一意性から key と children=[] を得る。
packet、Instance、Evidence、Joint を shape に隠していない。

`GeneralDictionaryCoveredEvidence` は記録のみの条件つき有限辞書帰納。
`GeneralDictionaryRecordedCoverageLimit` はその条件が強すぎる具体例を証明する。
既存の実 reachable・modeled・stable な recursive success でも、selected scalar leaf
には同じ occurrence の記録 packet がない。これは V5 の反例ではない。

`GeneralDictionaryMixedCoverage` は、generated selected focus ごとに
記録 packet + ordinary Extension、または構造的 nominal/scalar leaf のどちらかを
要求する。任意有限の Classify selected dictionary に対して、その同じ現在モデルの
全 dictionary Evidence を相互帰納で構築する。`GeneralDictionaryMixedCoverageExample`
は記録親 + 未記録 Int leaf の実成功例にこの一般条件つき定理を適用する。
coverage 自体、一般 executor、全プログラムの停止性は証明していない。

`GeneralNominalNestedLinearFacts` / `GeneralDictionaryNestedLeaf` は別に、深さ2の
Outer(Inner(v0,...,vn))、中間 point、任意有限 linear binder と最内側任意 interval の
実 inspection/projection/private Models と未記録 leaf Evidence を導く。深さ2の結果を
任意深さの完成と読まない。

## 読み方と残差

同じ片側モデルを維持することと、存在モデルを一つ発見することは異なる。
今回の branch/evidence 輸送は前者。意味的 Instance/Evidence と、過去に実際に生成
された graph edge も異なる。実履歴から edge を回収した場合だけ Generated と言う。
主要な未解決は、任意 reachable stable selected focus の構造 coverage、一般進行と
停止、where accessibility、canonical order である。一般 V5 の8残件は減らしていない。

## 最終統合での追加と正確な範囲

- `GeneralNominalQueryRecoveredNodeEvidence` は旧query・旧RHS翻訳・旧/現head名一致・seed・root/child出力パスを前提にせず、実packet materializationと全support-stepのmetadata保存から回復する。残るのは同occurrenceの実記録packet、headと各lower/upperのRecordedPath、現在のnominal query/RHS、descriptor/parameter形、outputNames=[]、bare-variable where入力、実argument lookup、current selected、およびcurrent子Evidence。
- `GeneralNominalSpineFacts` / `GeneralDictionarySpineLeaf` は任意有限長のunary point-wrapper列と最内層の有限個injective binderを構造帰納で扱う。深さ2だけに制限されない。一方、任意分岐nested tree、繰返しbinder、nonpoint wrapper、row parameters、nonterminal未記録nodeは未対応。
- `GeneralDictionarySpineCoverage` は記録済ordinary-replay可能packet、上記spine terminal leaf、scalar terminal leafの三つを構造coverageとして、任意有限Classify辞書の同一current modelにおけるEvidenceを帰納で導く。実recursive fixtureの記録済parentと未記録scalar leafにも適用した。Classifyの有限証拠を仮定する定理であり、executor停止や一般coverage自体の証明ではない。
- `GeneralNominalStructuralSelectedGraph` のsingleton条件はregistryではなくjournal。子Evidenceを仮定せずInstanceを構築し、Related sitesの同occurrence条件からJoint、actual StableからGeneratedChildrenを導く。
- `GeneralDictionaryFiniteJournalJoint` は任意finite ordinary InitialSource実履歴で、同focusの実packet、current selected/current model、Related sitesの同occurrence条件からJointを導く。singleton journal・key一致・Instance・BranchModelsの仮定は不要で、無関係なpacketは許す。このordinary履歴からGeneratedChildrenを導くこと自体は既存定理がより弱い前提で提供しており、新規の一般化とは数えない。全support-stepでpacket.siteの現在sitesへの実membershipを保持する補題も追加した。

### 既存コメントへの補足
`GeneralNominalSharedJournalPaths.path_sound_after_steps` のコメントはrebuild後のパス残存を保証しない旨を述べるが、後続の`GeneralDictionarySupportSourceInvariants`では現実の全support-step relationについてordinary atom包含とRecordedPath保持を証明した。したがって当該コメントの弱い説明を最終結果の制約として読まない。公開済Leanを変更せず、この補足で明確化する。

一般V5は6/14供給・8/14未解決のまま。今回の構造的部分クラスや具体例を一般定理完成と数えない。
