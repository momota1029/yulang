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
