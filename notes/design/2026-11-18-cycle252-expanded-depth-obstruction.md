# Cycle252: I49のmax深さ上界に対する実source診断

状態: 実checked sourceから1回のinstallationまでLeanで閉じた例を取得。
これを受けて新実装を停止し、監査・保全・報告だけを行う。
言語が非停止する反例ではなく、提案された表現上の深さ上界への反例である。

## 具体例

単項のnominal constructor Fとground Intを使用する。宣言は入力headが型変数a、
whereなし、associated outputは F(F(a))。初期の入力はF(Int)、出力slot3は未拘束。
実compilerのbinderは入力slot2を読み、生成output式はslot3 = F(F(var0))となる。
入力を展開した式はF(F(F(Int)))で、install後の全モデルがこのoutputと同値になる。

Leanのdepthはvarを0、constructor applicationを1+子の最大depthとする。
inputのdepth=2、associated templateのdepth=2、展開後のdepth=4。
したがって `depth(expanded) ≤ max(depth(input),depth(template))` は偽。
Intを0と数える通常のconstructor-only conventionでも1/2→3で同じ不等式が破れる。

この例にunion重複・隠れたfield・where再帰・循環したinputはない。output-only
変数をwhere入力へ戻す違反もなく、既知一点inputを付け替えてもいない。
深いoutputを一つのモデルで勝手に選んだだけではなく、output_forcedが実install後
の全Modelsに対して主張する。初期小モデルではoutput=Intが許されるため、novelも
実証している。全install guardを満たすStepとReachableを明示した。

## 何を反駁し、何を反駁しないか

- I49でprivate名を解いたpublic展開形まで `D=max(source, declarations)` に入れる
  という上界は、この実際のreadbackに適用できない。
- 生のjournalはvar参照を残せるので、保存template自身の深さは2。この証明を
  「保存したraw項が無限に成長する」と読み替えてはいけない。
- 一回で止まるwhereなしの例であり、source Accの否定でも言語意味の矛盾でもない。
- 別の原子として全体を包んだりDを加算型へ修正する方法まで反駁しない。ただし
  その有限basis/上界は別途構成・保存を証明する必要がある。
- 現mixed/point source境界の診断であり、未完成rebase後継Stepの実行と偽らない。

## 監督役へ返す判断

言語の意味を変更する必要は、この例からは生じない。表現の上界を修正する問題。
少なくともtemplate代入の加算増分を数えなければならない。再帰的なoutput依存に
沿った増加を抑えるには、有限owner生成pathとoutput依存/共有の不変条件が要る。
既存SettledGrowth/SourceFactorizationの増大型budgetは参考になるが、actual
producerがまだ構成されていないため、そのまま完成証明として転用しない。

今回の正常化は有限pool内のunion/intersectionだけに意味保存・冪等性・列挙・
private-read非流出を証明した。pool外ならchecked prepare=None。sourceが固定pool
に閉じるというI49の残義務を、これら局所定理の前提へ隠して完成扱いしない。
新しい上界・basisの扱いは監督役の判断を待ち、勝手に置換した仕様で先へ進まない。
