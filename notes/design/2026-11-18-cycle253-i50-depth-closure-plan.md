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
