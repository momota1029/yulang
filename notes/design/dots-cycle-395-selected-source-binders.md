# Cycle 395: selected-source kinded bindings before output evaluation

正本 f89c2bf4a2098f8664473cebc4a42666b130e735、I-69 inbox 5e202637769e290325b60e4425812e784428f3d7。C394 の型付き compound evaluator は既成の RHS を要求しないが、実 capture の型種をもつ SourceBindingReads394 が必要。**S13bbba (a)**: 選択した出現から、同じ元位置の実 capture を型種付きで得て、同じ元 RHS を書く規則が不足。選択を出力から逆算せず、候補の actual C367 tape とその source head の C366 DeepRead を使う。C386 が Pattern を保持することと、任意の複合 native の typed vector を旧規則で作れることは別。

## 実装する局所切断

- source head の順付き DeepHead を元候補に固定。引数インデックス、その引数で生成された ordinal、Binding の元 name、kind、両端を各 proof と結ぶ。deep_reads_retain_all_sources の位置付き版から C394 の typed read を作る。proof source は actual finite read; no model/solver and no use of unused arguments.
- source frame の実 head capture input を C393 where placement と合成。明示 body の head binder が checked OutputOnly で元 head に出現した場合は、source names/lookup から exact same Capture が出ることを証明。行と値を数値だけで同一視せず、その head visit の original kind を C394 input に運ぶ。
- actual typed head ticket を取得できないことは language rejection でない。出力専用の where binder と role default は head binder ではない。既存 where ordinal の結果と有限 selected producer の出力をつなげる場合だけ、独立 read を足す。S13bbbb retention は触らない。

最上段の文・独立な選択/保留規則・literal carrier・checklist を変更せず、S13 を分割しない。

## 最初の実証

C367 の選択済み tape の実 Stored 位置から、順序を保った visible filter を反転して **同じ元 registry ordinal** を復元する。宣言が単に Registry に含まれるという根拠で元位置を選ばない。C366 の DeepRead で実際に生じた native head leaf を、元の head 引数 ordinal とその leaf ordinal で辿る。任意深さ・引数列に対し、実 leaf 名が元の正規化 head の lexical name であり、同じ capture の value/row であることを証明した。unused は source leaf を生まない。recognized leaf の present 判定はこの実 read の存在と同値。

選択済み tape と checked registry から、任意の元 output ordinal の evaluation を C394 に接続した。scope が揃う分岐では parent output の証拠や型付き vector を入力にせず、実 selected binder と元 Supplies から元 RHS を得る。その射影が既存の native wire に載る場合に限って receipt を出し、選択された registry ordinal、request occurrence、関連型 output ordinal、同じ authored Body と元 fixed target を証明した。selected rule 自体を変更しない。C367 はこの独立局所 read の実入力であり、旧 solver authority を I-67 の Classifies に移していない。全選択の completeness、joined/default/where-only、任意 compound の旧 wire は別で、未対応に意味上の拒否を与えない。
