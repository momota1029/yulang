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
