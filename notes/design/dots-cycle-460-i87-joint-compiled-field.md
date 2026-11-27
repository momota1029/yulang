# I-87 / C460: 同じ選択位置の構文読取と実 raw 追跡

## 構文と provenance

`WrittenPattern460.Term/Args` は現在の解決済み `Pattern` の全てと相互に可逆。元 declaration の head と where は同じ文法に入り、where の番号・元 ID を取り違えると読めない。正規化は `normalize` を別段で輸送するだけで、元 declaration を書き換えない。裸の名前番号を primitive に固定しない。`queryKeys` は現 catalogue と元 Use・mode table から empty/pair/単項 covariant の**演算子**を読む。実 endpoint が point かどうかは従来の実 opener が別に確かめる。

## 単一の経路

`Step` は一つの選択住所だけを読む。閉 record の tail spine は閉性・最初の同名 field を確かめる。兄弟の payload、pair の別成分は展開しない。variant は元タグ、pair は元 ordinal、nominal は実単項の位置のみ。variable・join 自体には降下なし。既存正規化で消えた同一 tag の join と、解消しない `Expr.join` とを区別する。後者は現在の `Inspects` にも降下規則にもないが、言語の拒否を意味しない。

`JointTrail` は既存 raw `AtStep`、同じ logical coordinate での構文 Step、既存 prefix escape を一つの再帰で揃える。raw row・owner / Alias・issuer と実 child を読み、辺は追加しない。`ExactFieldPath` は末尾が実 field で、同じ raw snapshot で terminal の K2 を要求する。root K2 はこの field 証跡ではない。

具体化 `CompiledTrail` は既存 `AuthoredQuery` の証明を起点に、選択子の query を元コンパイラの導出から下へ輸送する。アドレスの名前一致を型一致の代用にしない。最初の compile は既存手順。訪問のために、その後の各段でもう一度 subtree を compile したり兄弟を raw で検査したりしない。独立 `CompiledField` と exact な有限データの iff、同じ state の全 FitsFull、旧 raw trail と同一住所の構文 path に分解する iff を検査した。

## まだ示していないこと

この結果は path **検証**であって、訪問開始を許す一般の G04 head / where 導出や、候補の選定、solver による path の生成ではない。既存の実 C458/C459 ヘッダを使った同じ report の回帰は、この設計の一つの検査でしかない。上流で元 inline 座標と本物の raw operand を一致させる一般保証、現在の正規形に残る join／一般の bound pattern とどう対応するか、全ての G04 コンテキストを既存の累積入口で受けることは未証明。開いた tail は G06/G07、一般 mode・kind・arity・非 point は G20/G21 であり範囲を変更しない。
