# cycle259: 実観測からの部分rebase提案

I51/I52継続。cycle258のfinite Fact/remaining Stateを使い、固定表observerと
実I45 packetとの間を埋める。旧Step・旧Lean・specは変更しない。

## データと実行
- 実packetのReportを既存 `ReportProjection257.transport n` で初期5slotへ写す。
- decoderはcaptured name0とsource basisの端点2/4を読む。lower/upper atomの
  添字は2→0、4→1。unsupported endpoint、blocked/conflict/arity、空captureは
  提案なし。複数captureの同一factは重複除去し、固定owner0とbinder0/1を使う。
- 全Reportに対する言語的健全性を先取りしない。今回の宣言的対応対象は実I45
  familyのpacketに限る。このfamilyでReportから提案が計算されることを証明。
- `observeAt n` と新finite writeを接続し、全nで旧固定表observerと同じである
  こと、初回一歩・全後続noopを証明する。nはobserverの入力indexで、新状態に
  保存する履歴ではない。全一般sourceでnを消去したcompilerは未完とする。

## 外側の定理（狙い）
任意nと任意公開境界aについて初期raw Models aなら、初期0〜4と全rowを固定する
complete aが当該実plan nの全Holdsを満たす。同じdecoder proposalで新stateへ
writeすると、old completed stageと新stateの存在公開モデルが同値になる。
Modelの構成を仮定ではなく258の明示completeから得る。

## 次の239断片
既存238の型Equivalent congruenceを再利用する。ただし固定modelのrowEmptyと
任意公開rowの差を隠さず、row-parametricモデルまたはconsumerごとのrow不依存
を先に証明する。239回帰と一般source observerが未完なら未完と書く。

停止測度はremaining.length。decoderの有限Fact参照で新名前の再予約をしない。
ただしこの測度が言語に忠実だという一般主張にはobserver健全性・完全性が必要。

## 239 rowモデルの具体構成（15:36 UTC）
`withRows rows name = (Source237.model name の型, rows name)` と置く。
既存固定modelと型成分は同じ、rowは任意関数。Origin.Observesは型成分しか読まない
ので一般の型成分一致によるiffを証明する。239 raw snapshotはtype parameterのみ、
ordinaryはvar/union/interの型atom、head schemaはnominal source観測でchild/output空。
その各consumerをwithRowsに移し、実book atomsと全plan Holdsを帰納的に構成する。
さらに初期0〜3を境界assignmentへ戻すcompleteを考える。source初期モデルから
その4型はS/F/PとEquivalentであり、全rowはwithRowsと同じなので既存238のSame
による全journal移送が使える。row不依存を仮定にせず、具体consumerで埋める。

## 239への新Step接続
任意row・初期公開境界のcompletionをLeanで構成できた。次に4slotへの投影で
実239 reportのlower/upper captureがどちらも初期slot2へ写ることを示す。
一般のstate/slot-to-atom関数で同じdecoder操作を定義し、239ではbasis[var2]、
固定owner0、lower0/upper0、固定binderの2factとする。固定5factのremaining状態を
再利用するが、239用のfactsは240と別で、勝手に両fixtureのslot集合を同一視しない。
new Modelsは初期raw sourceに、install済みならactual binder≃slot2を加える。
全rowsを保つcompletionでこれを満たすことと旧completed stage公開射影とのiffを
証明し、実report由来observer/runで一度install後にnoopとなる回帰を作る。

239 new Modelsは二状態のif分岐でなく、present factsごとの解釈にする。
lower0/upper0はsource slot2と内部actual binderとの双方向subtype、binder0/1も
その固定二条件、installed0はowner marker。全状態のpresentは固定factsの部分列。
初期は空、finalは全5factなのでraw source∧binder Equivalentになる。
明示completeが全5factを満たすなら任意中間subsetも満たす。これにより任意有限
stateの公開射影iff初期sourceを示せるが、239という固定terminal sourceの結果。

## 一般finite-writeの意味保存則
239のpresent-fact意味付けを任意basis、任意baseモデル述語、任意fact解釈へ分離する。
固定FactのBoolean等号の正しさを証明した上で、write後presentへの所属は
「元presentに所属、またはbasisとproposalの双方に所属」と同値になる。
従ってwrite後Models iff 旧Models ∧ proposal中のbasis内fact全成立。
これは一般observerの健全性を仮定に隠す定理ではなく、実装したfilter writeの
正確な意味。言語sourceからbase/fact/observerを導く義務は引き続き別に残る。

## proposal閉包を実行時にも分離する
一般writeはbasis外factを無視するので、言語compilerを接続する前にchecked commitを
追加する。proposal中のbasis外factをリストで返し、存在すれば状態を書かない。
これは内部表現の未支持を報告する結果であり、source programの意味的拒否ではない。
全factがbasis内なら既存tryWriteを使い、none（既処理）とsome（新install）を分ける。
I45/239の実decoder proposalは既にfactsとの等号があるので検査を通る。
この入口上でwrite後Models iff旧Models∧全proposal成立を証明する。

## 複数proposalのdriver
単一proposalがnoopでも、別のproposalに新情報があるかもしれない。一般observerの
有限proposal列を左から走査し、noopを飛ばして最初のinstallを返す。unsupportedは
内部エラーとして停止し、source拒否とはしない。全列noopのときだけquiescent。
走査がsome stateを返せば元のStepの一歩でremaining長が減ることを証明し、
この減少でwell-foundedな反復関数を定義する。これも有限basis/observerを受け取る
実行器であり、一般sourceから正しいobserverを作る仕事を済ませたとは呼ばない。

## 固定proposal集合の順序について
任意state、proposal p/qのwriteはfilterなので可換・冪等である。ただしobserverが
stateによって別proposalを出す場合の合流性はこれだけでは言えない。
固定した有限proposal列に限り、全writeの結果とchecked schedulerの終端を対応
させる。noopを先頭に入れても次の新factを見落とさない。observer一般の順序独立、
全言語主型性へ拡大しない。

## 最終実行probeと失敗意味の境界

`notes/verification/cycle259/DriverProbe.lean` はI45/239のsettleがremaining=0を返すことをLean評価で確認し、別の手作り内部observerについて初回書込みが成功した後にunsupported999を返すことを3本のkernel検証補題と評価で確認した。これはsourceから到達する言語反例ではない。各commitの部分書込み禁止は、複数回commitを内部で実行するsettle全体のrollbackを意味しない。pure関数settleはerrorのみを返し、中間Stateを返さない。#evalは証明oracleではなく、Yulang2実装を実行したものでもない。

全28 moduleは独立読取レビュー済み。独立再ビルドではなく、この作業者によるfresh dependency buildを別に記録する。固定batchのliteral終点一意性は、一般sourceのprincipal typingや任意動的observerの合流性ではない。

## 次のsource接続で最初に解く義務（16:12 UTCの再点検）

今回の有限driverをさらに抽象化するより、terminalでない実sourceの同じ観測・据え付けへ接続することを次の優先にする。具体的には252のassociated outputを持つsourceが小さな次の対象になる。258のslot3だけを補完する実packet Holds/Evidenceを再利用し、出力を読まない239/I45だけで一般compilerが完成したと言わない。

1. **factの意味表**: 現Factはlower/upper/binder/installedだけで、出力・child・head presenceの一般的な意味表をsourceから作っていない。選択肢は新しい有限fact型を作るか、binder indexをsource由来の有限obligation表の添字として使うか。後者なら既存generic driverは再利用できるが、表の各entryと実packetの全fieldとの対応を明示する必要がある。名前0・binder0/1に固定した現在のdecoderを一般化済みと扱わない。
2. **失敗の分類**: 現compileのnoneはunsupported/blocked/conflict/arity/空captureを区別しない。両実fixtureではnoneにならないと証明したが、一般sourceではnone→noopだけでは検査漏れになる。言語拒否・まだ準備できない観測・未対応内部表現を区別する入口を先に設計する。新しい拒否規則を勝手に追加しない。
3. **owner別の置換と単調性**: finite remainingの減少は既存Stepに対して確実だが、sourceで端点が変化したときに既存factsを保持できることを一般には示していない。固定ownerの新しい集約が旧公開制約を失わず、かつ同一意味の見直しならnoopとなる対応が必要。有限basisだけを仮定してこの義務を済ませない。
4. **output pool閉包と深さ**: I50のsource名＋owner output参照というpoolを使用し、ground readback深さは依存鎖の加算、保存構文深さとは分ける。今回の239/I45はoutput空なので、循環outputの拒否・K2との接続は進んでいない。新Stepの残数上界はこの未解決義務を代替しない。
5. **EvidenceNodeまで**: finite表のdecoder健全性/完全性 → 実packetの全Holdsと同じinstall → sourceからのClosed/公開射影 → 一般PermittedとEvidenceNodeへ進む。199/202/204/206/218/230の回帰、一般12性質、resolve_exact、principal typingはこのサイクルでは移植・再検証していない。全source Accを宣言するには同じ入口がすべてを表せることが必要。

現時点では言語の意味を選び直す必要は確認しておらず、今回の内部unsupported probeをYulangプログラムの拒否例として質問しない。上記の未完は一般sourceへの射程の限界で、検証済みの部分Stepや239/240回帰を無効にするものではない。

### 実252 sourceで確認した具体的な未接続箇所

`OutputCoverageProbe.lean` は上記の「出力対応が必要」を具体的に検証した。252の実packet reportを、slot2をatom0へ写す現在の一般構文decoderに渡すと5factsを返し、同basisのchecked commitも成功する。一方、既存の `replace bottom` はこの実sourceの初期journal Modelsとprepared Frameを満たすが、packet Holds（出力方程式）を満たさない。3本の補題を `--trust=0 -DwarningAsError=true` で検証した。

これは239/I45のcertificateの反例ではない。252用の有限fact意味表や公開モデル対応をまだ定義していないところに、既存の構文受理だけを当てはめても出力証明書にならない、という厳密な範囲確認である。checked writeが成功することは内部basis閉包の証拠であって、source Modelsを真に拡張することの証拠ではない。言語の拒否・新Stepの非停止・I50上界違反は示しておらず、明示的な全体STOP条件の新たな成立とは扱わない。
