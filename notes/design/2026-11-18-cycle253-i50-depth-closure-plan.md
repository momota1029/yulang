# Cycle253: I50 加算深さと公開参照poolの設計

開始09:28:30UTC、integration42e33c1a9。前回のmax上界は再使用しない。
以下を別々の主張として扱う。新source反例が閉じれば実装を止める。

## A. template代入の加算（最初のLean対象）

任意の実Pattern/Expr template tと代入σについて、tの各変数の置換項の深さがB以下
なら `depth(t[σ]) ≤ depth(t)+B`。listの最大深さも相互再帰で証明する。
これはground readback用のsyntax補題で、raw compilerのvar参照を代入したことには
しない。252の実例では2+2=4となり、誤ったmaxを正しく修復する。

ただし「ownerの入力の深さ最大」だけでBを供給できるかは別問題。
associated RHSはwhereの出力専用変数も読める（spec6.3）。その場合Bには他owner
の出力readbackも含める必要がある。I50の依存鎖上の加算はこれを意図すると
考えられるが、own inputだけの不等式を無条件に証明済みとしない。

## B. finite acyclic dependency graph

owner候補の有限性は252のactual source theoremを使えるが、同じownerが出す
複数出力やtemplateの参照変数をどのnodeに結ぶかを明示する。source名をleaf、
各出力名をnodeとし、ground readbackの各substitution dependencyが先行nodeを
参照する場合、深さ≤source bound+path上template depthの和を帰納で示す。
cycleはalias-only（型構築子の増加0）とproper-constructor cycleを区別する。
有限node数だけでacyclicを仮定したり、alias cycleをK2拒否と同一視しない。
実source Stepがこのorderまたは既存拒否分類を供給することは別途必要。

## C. raw構文とpool閉包

生のtemplateは有限で、σがvarへのrenameならconstructor深さを増やさない。
source名＋有限owner出力名を参照する有限pool上で、raw RHSは有限templateと有限
renameの組合せとして列挙できる。これはground展開の項集合とは別。

252のSnapshotNormalは任意atomの代入結果がpool内にあることを条件にした。
private aggregate参照だけをold normalized RHSへ置換し、public output参照は
展開せず残す、という表現が必要。任意のsource名のground展開を行えば252反例が
再発する。現source bindingsのendpointが常にこのpublic参照集合かを調べる。
空下界bottom/空上界top、union内のinterなど、単なるvar poolでは表現できない
項も明示的に扱う。pool外を黙って削ることで閉包を偽装しない。

## D. gates

raw参照式の有限性とground depth上界のどちらも、依存graph/source名の保存へ
結ぶまでAccではない。private escapeと新factの厳密増加は引き続き未完了。
言語意味は変えず、I50の具体的な上界解釈がsource例で破れれば、閉じた診断を
公開して監督役へ返す。packet/Permitted部品は増やさない。

## 09:48 checkpoint: 狭いpoolの診断と修正候補

`GeneralDictionaryCompoundPool253.source_reachable_pool_gap` は既存238の実sourceを
I45のinstall一歩へ埋め込み、実到達childの入力端点が元source名とnamed-output
binder名のpoolから外れることを閉じる。registryのoutputNamesは空であり、owner
候補をどれだけ増やしても埋まらない。private slotだけを置換し、そのpublic
端点を保存するmappingについては、同端点のvar atomは依然pool外となる。

**範囲**: これは到達public端点の列挙漏れと条件付き置換閉包の診断であり、
新rebase境界の実SnapshotNormal処理に到達して失敗するtraceではない。
非停止反例でもなく、I50の「ownerの出力」をすべてのemitted portと読む場合
まで否定しない。named binder限定の閉包証明だけを保留し、独立の研究は続ける。

候補修正は `GeneralNominalPublicPorts253.ports`。purpose2のnamed出力に加え、
whereのcompound入力用3/4とclause出力用5を列挙する。sourceから有限ownerを
取ることにより、全将来installの該当public portは一つの有限listに入る。
0/1のversioned private aggregateはどのbinding履歴についてもこのlist外。
`GeneralDictionaryCompoundPoolRepair253` で今回の欠落だけは修復を検証した。
これは候補basisの定義であり、実compiler/journalの表現変更を行っていない。
actual center7/8/9の扱い、構造項を原子にすべき場合、bottom/top、中間の異なる
演算をどう閉包するか、source trace全体でのprivate escapeはまだ別の義務。

加算上界は `Build` でtopological readback順序が供給される場合に証明する。
各nodeがsourceまたは前node出力を代入するなら、深さはsource最大深さと全node
のtemplate深さの和以下。これをowner数だけに置き換えてはいけない。owner内
複数出力やoutput-only binderの依存も数える。正の深さ増分を持つcycleは矛盾、
aliasだけの0増分cycleはこの議論では拒否できない。実sourceが順序または適切な
拒否分類を供給する定理はまだない。

## 09:51 新しい整理: producer呼出しと制約graphを分離する

`Declaration.OutputOnly` は output-only変数をheadとwhere入力から除外し、
`Declaration.Scoped` はwhere入力をhead入力名だけに制限している。
`Produced` は各output binderに具体的なwhere出力のproducerを指定する。
従って、入力captureを固定した**宣言のproducer呼出し**はoutput binderの値を
変えても同じchild入力を持ち、各child入力の正規化質量はPatersonで真に小さい。
このsyntax呼出し関係そのもののAccはsource規則から示せる。これを次に検証する。

ただしこれはoperational StepのAccではない。異なる候補、履歴のsnapshot、
制約の等式alias、output制約の整合性確認までこの順序で実行されるというproducer
実装が必要である。実journalのすべての依存辺を宣言call辺と同一視しない。
I50の依存graphを設計するときは、(i) 値を計算するproducer call graph と
(ii) 値の整合性を検査する等式graph を分けると、0増分alias cycleを誤ってK2と
報告しなくて済む。言語規則の追加ではなく、現行Produced/OutputOnly/Scopedの利用。

## 09:58 私的slotとの分離

拡張候補basisはsource名＋purpose2〜5のpublic port名のvar。
source形成のbelow_seedとoriginのpurpose区別から、purpose0/1の全private名は
position0（固定rebase）でも正のposition（versioned）でもbasisに現れない。
このbasis上のunion/intersection正規形は全typeSources（row含む）でprivate-free。
ただしnormalizeは非対応atomを削るので、意味保存はSupported前提を付けた別定理に
まとめた。private-freeだけをsource閉包の証明とはしない。

`associated_from_children` は実checked宣言のscopeとProducedを使い、入力bound Iと
子associated値bound CからRHS深さ≤template深さ＋max(I,C)を得る。子のboundを
無条件にIへ落とさない。`calls_wellFounded` は宣言的呼出しのみなので、source
compilerがこの呼出し順と整合することが次の主要なproducer義務である。

## 10:00 normalized producer順序の接続

rawにcaptureしてから正規化する形と、normalizeArgsを先にcaptureする形は一般に
同一視できない（既存HiddenJoinの注意）。今回のAssociatedは後者を読む。
既存 `GeneralPatternConservativeSubstitution.checked_normalized_descent` は
CountsCoveredとConservativeSmallerから後者そのものの厳密減少を証明している。
これを使い `NormalizedChild` とそのAcc、およびactual Associated引数への
`normalized_binder_producer` を追加した。normalize/substの無条件交換は使わない。
残るのはこの宣言的計算順序と現在のsource journal・選択候補・readbackの接続。

## 10:03 associated入力readbackの不足を分解

既存 `VersionedHeadReadback237.readback` はwhere入力でNeededな変数だけの有限
readbackを返し、whereが非空という前提もある。associated RHSだけが読むhead入力
まで得られたとは言えない。まず非空where宣言について、同じhead_weight議論を
inputNamesの全名へ広げる。新たな有限性前提は置かず、Frame/Holds/ground Inputsと
非空whereから、全head入力のPart・各labelサイズ上界・head質量上界を作る。
whereのないleafには適用しない。その一般化は別義務として残す。

## 10:06 leafの範囲を少し拡張する

head_weight237が非空whereを要求する用途は、checked.countsCoveredから正規化headの
coveredArgs=trueを取り出す箇所だけだった。そこでこの構文検査結果を直接入力する
head_weight_covered / readback_covered を同じsource意味論から導出する。
finite性や深さ上界そのものは仮定しない。非空whereは従来のcheckedからこの条件を
供給し、leafでもcoveredHeadが計算で通るもの（252の単変数headなど）に適用できる。
variant payload内のplainNames joinなど、Complete queryでもcoveredHeadが偽になりうる
headは未対応なので、全leafを覆ったとは報告しない。

## 10:13 次のproducer義務を具体化

追加のstrict使用例で、head=`variant 0 (var 0 | var 1)`、whereなし、associated=var0
の宣言が実DeclarationCheckedを満たし、inspection queryはCompleteだが
coveredArgs(normalizeArgs head)=falseとなることを確認した。
これは言語の反例やsource非停止ではなく、readback_coveredの適用範囲が全checked
leafでないことを示す宣言レベルの検査例（Cycle253Usage.joinedLeaf）。

次は二つの契約を分ける:
1. **各入力名の個別Part・size/depth bound**: Complete queryの各variable使用を
   source labelの構造projectionへ戻す。plainNamesが同じoriginを複数名に共有する
   場合は各名を個別に読む。translated_namesで全inputNamesを覆う。
2. **head全体の質量和bound**: Paterson/where descent用のcovered headでのみ使用。
   上のquery名ごとの情報から、重複した使用をそのまま足してよいと仮定しない。

これにchild出力のreadbackをNormalizedChild順で結ぶproducerを作る。ただし
selected candidateとalias/historyの対応は別証明。strict新fact進捗はまだ供給しない。

raw有限性についても、有限templateの列挙はまだ任意refreshのdescriptor/label
vocabularyがsource由来であることを示さない。public portsの集合が有限なだけで
任意のobserved構造やcompound endpoint式の集合まで有限と数えない。
深さ補題は明記した構文と代表に対するもの。後段normalizeの深さや同値な任意の
冗長表現の深さへ無条件に読み替えない。

10:12にintegration155c7aa0cを確認。252成果とI50の統合で、指示の変更なし。
merge時のbarrel/heartbeat競合は、integration barrelが253 barrelの完全なprefixで
あることをbyte確認して既存＋253追記を保持し、心拍は稼働中253を保持して解決。
merge前後の全treeのbytesに差分はない。
