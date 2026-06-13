# method選択について
`x.meth`があったとき、それらはすぐには解決されない。`x`の型`'a`の下界が1つでもあってその型に`.meth`というメソッドがあったとき、初めて名前が解決される。

methodが解決されるまでそのSCCは「method依存である」として解かれることがない。

# impl候補の有効範囲
`impl`は、その`impl`を含むファイルが読み込まれたときにだけ候補として効く。未読込ファイルに書かれた`impl`は、method選択やrole解決のcandidate tableに入らない。

したがって、method選択とrole解決は、現在のfile SCCから到達して読み込まれたファイル集合を候補集合の境界として扱う。これにより、別file SCCの解析では、そのSCCが読み込んだ`impl`だけを見て解決できる。

`impl`が読み込まれた後の可視性は、通常のmodule visibility / realm visibilityに従う。

# 可変参照のmethod選択について
- `x.meth`で`x`が`ref<'e,'a>`であった場合、`'a`に対して同様に下界を調べてmethodを探す。

# 解決しなかったmethodを含むSCCについて
これらは`role`の関連型によって解決する可能性があるため、以下のループを行う
1. 全てのSCCで関連型を含むrole(生)をcompact型として展開する
2. 解けるroleを全て解く
3. 解けたものがあれば1に戻る
4. SCCに変化がなければmethodを全てroleかrecord fieldとして解釈し、ループを抜ける

これを行うことでmethodは最終的に全て解決される。

最後にmethodをrole methodとして解釈した場合でも、selection解決そのものはreceiver専用のrole demandを作らない。
method自身のschemeをinstantiateすれば全引数のdemandが既に生まれ、receiverはその第1引数へ下界として流れ込む。
例えば`role Ord 'a: our x.le: 'a -> bool`に対して`x.le y`を`Ord.le`として解決したなら、
`Ord.le`のscheme instantiationから作られる`Ord α` demandに、selection subjectである`x`の値型が流れ込む。

receiverの値型をsubjectにしたdemandを別に作ると、method instantiation由来のdemandとcoalesceされたときに
receiver側のpayload変数が不変区間の中心(=実引数)を乗っ取り、supertypeで解決できるinstanceを失う。
通常引数が複数のroleでは、残りの引数位置を本物のdemandと共有できず、mergeもimpl候補との照合もできない
述語が永久に残る。したがってreceiver demandのfabricateは行わない。
